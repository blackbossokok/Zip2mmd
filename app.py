"""
Zip2mmd v1.0
- 左侧目录分组（可增删监控目录，可对真实文件操作）
- 右侧固定 3D 视口，内嵌渲染模型（PMX/PMD/GLB/GLTF/FBX/OBJ）
- 不解压：内容按需从压缩包读取，临时文件只落在本工具 _cache
"""

import os
import io
import re
import json
import sys
import time
import hashlib
import struct
import shlex
import shutil
import zipfile
import tempfile
import subprocess
import threading
from flask import Flask, send_file, jsonify, request, abort, Response

app = Flask(__name__)

# ==================== 配置 ====================
def _reg_path(subkey, value="Path"):
    """从注册表读安装目录（7-Zip / WinRAR 都会写）"""
    try:
        import winreg
        for root in (winreg.HKEY_LOCAL_MACHINE, winreg.HKEY_CURRENT_USER):
            for view in (0, getattr(winreg, "KEY_WOW64_32KEY", 0)):
                try:
                    with winreg.OpenKey(root, subkey, 0, winreg.KEY_READ | view) as k:
                        p, _ = winreg.QueryValueEx(k, value)
                        if p:
                            return p
                except OSError:
                    continue
    except Exception:
        pass
    return ""


def _find_tool(env_key, candidates):
    """外部工具路径：优先环境变量，其次常见安装位置。
    发布给别人时不该把作者机器的路径写死——找不到就把对应功能设为不可用。"""
    v = os.environ.get(env_key)
    if v and os.path.isfile(v):
        return v
    for c in candidates:
        if c and os.path.isfile(c):
            return c
    return ""


_7Z_REG = _reg_path(r"SOFTWARE\7-Zip")
_RAR_REG = _reg_path(r"SOFTWARE\WinRAR")

SEVEN_ZIP = _find_tool("ZIPTOOL_7Z", [
    os.path.join(_7Z_REG, "7z.exe") if _7Z_REG else "",
    shutil.which("7z") or "", shutil.which("7za") or "",
    r"C:\Program Files\7-Zip\7z.exe",
    r"C:\Program Files (x86)\7-Zip\7z.exe",
])
UNRAR = _find_tool("ZIPTOOL_UNRAR", [
    os.path.join(_RAR_REG, "UnRAR.exe") if _RAR_REG else "",
    shutil.which("unrar") or "",
    r"C:\Program Files\WinRAR\UnRAR.exe",
    r"C:\Program Files (x86)\WinRAR\UnRAR.exe",
])
PMX_EDITOR = _find_tool("ZIPTOOL_PMXEDITOR", [
    r"C:\Program Files\PmxEditor\PmxEditor.exe",
])

# 打包成 exe 后：数据（_cache / config.json）放在 exe 旁边，静态资源在 PyInstaller 的解包目录
FROZEN = bool(getattr(sys, "frozen", False))
BASE_DIR = os.path.dirname(sys.executable) if FROZEN else os.path.dirname(os.path.abspath(__file__))
RES_DIR = getattr(sys, "_MEIPASS", BASE_DIR)
CACHE_DIR = os.path.join(BASE_DIR, "_cache")
try:                                   # exe 放在 Program Files 之类只读目录时，缓存落到用户目录
    os.makedirs(CACHE_DIR, exist_ok=True)
except Exception:
    CACHE_DIR = os.path.join(os.environ.get("LOCALAPPDATA") or tempfile.gettempdir(),
                             "ZipPreviewTool", "cache")
    os.makedirs(CACHE_DIR, exist_ok=True)
THUMB_DIR = os.path.join(CACHE_DIR, "thumbs")
PMX_DIR = os.path.join(CACHE_DIR, "pmx")
TMP_DIR = os.path.join(CACHE_DIR, "tmp")
TRASH_DIR = os.path.join(CACHE_DIR, "trash")
EXTRACT_DIR = os.path.join(CACHE_DIR, "x")
COVER_DIR = os.path.join(CACHE_DIR, "covers")
ENC_CACHE_FILE = os.path.join(CACHE_DIR, "encryption.json")
VENDOR_DIR = os.path.join(RES_DIR, "vendor")
CONFIG_FILE = os.path.join(BASE_DIR, "config.json")

# 默认值必须是中性的：发布出去时不能带上作者的目录和密码
DEFAULT_WATCH_DIRS = []
DEFAULT_PASSWORD = ""
# 封面截图：默认命名 + 包内专用目录（避免和模型源文件混在一起）
DEFAULT_COVER_NAMES = ["ZipPreview.png"]
COVER_FOLDER = "ZipPreview"

ARCHIVE_EXTS = {".zip", ".7z", ".rar", ".rar4", ".rar5", ".001"}
SFX_EXTS = {".exe", ".sfx"}
IMAGE_EXTS = {".png", ".jpg", ".jpeg", ".webp", ".bmp", ".gif", ".tga", ".dds"}
# 贴图类扩展（PMX 的球面贴图 / 卡通贴图，内容是 BMP/PNG 但后缀不同）
TEX_EXTRA = {".spa", ".sph", ".toon"}
PMX_EXTS = {".pmx", ".pmd"}
GLTF_EXTS = {".glb", ".gltf"}
MODEL3D_EXTS = {".pmx", ".pmd", ".glb", ".gltf", ".fbx", ".obj"}

FILE_ICONS = {}  # 界面改用纯文字扩展名标签，不再用图标

# 1x1 透明 PNG（贴图缺失时兜底，避免模型整体加载失败）
BLANK_PNG = bytes.fromhex(
    "89504e470d0a1a0a0000000d4948445200000001000000010806000000"
    "1f15c4890000000d49444154789c63000100000500010d0a2db4000000"
    "0049454e44ae426082"
)

# 1x1 不透明白色 PNG（球面/卡通贴图缺失时兜底，乘算后不影响原色）
WHITE_PNG = bytes.fromhex(
    "89504e470d0a1a0a0000000d4948445200000001000000010802000000"
    "907753de0000000c49444154789c63f8ffff3f0005fe02fea735d05e00"
    "00000049454e44ae426082"
)

_sfx_cache = {}
_sfx_lock = threading.Lock()
_thumb_lock = threading.Lock()
_cfg_lock = threading.Lock()
_list_cache = {}
_list_lock = threading.Lock()
_enc_cache = {}
_enc_lock = threading.Lock()
_prewarming = False


# ==================== 加密探测 ====================

def load_enc_cache():
    global _enc_cache
    if os.path.isfile(ENC_CACHE_FILE):
        try:
            with open(ENC_CACHE_FILE, "r", encoding="utf-8") as f:
                _enc_cache = json.load(f)
        except Exception:
            _enc_cache = {}


def save_enc_cache():
    try:
        with _enc_lock:
            snapshot = dict(_enc_cache)
        with open(ENC_CACHE_FILE, "w", encoding="utf-8") as f:
            json.dump(snapshot, f, ensure_ascii=False)
    except Exception:
        pass


def _enc_key(path):
    try:
        st = os.stat(path)
        return hashlib.md5(f"{path}|{st.st_mtime}|{st.st_size}".encode("utf-8", "replace")).hexdigest()
    except OSError:
        return hashlib.md5(path.encode("utf-8", "replace")).hexdigest()


def _zip_encrypted(path):
    """标准 ZIP：看目录项 flag 位 / 精确解析 AES extra field(0x9901)，毫秒级。
    注意：不能用 b"\\x01\\x99" 子串匹配——NTFS 时间戳(0xa)/Unicode 路径(0x7075)
    等扩展字段的数据里也可能出现这两个字节，会把普通包误判成加密。"""
    try:
        with zipfile.ZipFile(path) as z:
            for i in z.infolist():
                if i.flag_bits & 0x1:
                    return True
                extra = i.extra or b""
                pos = 0
                while pos + 4 <= len(extra):
                    hid, sz = struct.unpack("<HH", extra[pos:pos + 4])
                    if hid == 0x9901:   # WinZip AES
                        return True
                    pos += 4 + sz
        return False
    except Exception:
        return None


def probe_encrypted(path, ext):
    key = _enc_key(path)
    with _enc_lock:
        if key in _enc_cache:
            return _enc_cache[key]

    if ext == ".zip":
        val = _zip_encrypted(path)
    else:
        val = None

    if val is None:
        try:
            r = _run([SEVEN_ZIP, "l", "-slt", "-ba", "-p-", path], timeout=90)
            out = r.stdout.decode("utf-8", "replace")
            err = r.stderr.decode("utf-8", "replace")
            low = err.lower()
            if "Encrypted = +" in out:
                val = True
            elif r.returncode != 0 and ("password" in low or "encrypted" in low or "cannot open" in low):
                val = True
            elif r.returncode == 0:
                val = False
            else:
                val = None  # 判定不了，留空下次再试
        except Exception:
            val = None

    if val is not None:
        with _enc_lock:
            _enc_cache[key] = val
    return val


def prewarm_encryption(watch_dirs):
    """后台把加密状态算好写缓存，前端轮询拿结果，首屏不阻塞"""
    global _prewarming
    if _prewarming:
        return
    _prewarming = True
    try:
        changed = False
        for a in scan_archives(watch_dirs):
            key = _enc_key(a["path"])
            with _enc_lock:
                if key in _enc_cache:
                    continue
            if probe_encrypted(a["path"], a["ext"]) is not None:
                changed = True
        if changed:
            save_enc_cache()
    finally:
        _prewarming = False


# ==================== 基础工具 ====================

def ensure_dirs():
    for d in (CACHE_DIR, THUMB_DIR, PMX_DIR, TMP_DIR, TRASH_DIR, EXTRACT_DIR, COVER_DIR):
        os.makedirs(d, exist_ok=True)
    tempfile.tempdir = TMP_DIR


def load_config():
    if os.path.isfile(CONFIG_FILE):
        try:
            with open(CONFIG_FILE, "r", encoding="utf-8") as f:
                cfg = json.load(f)
            if isinstance(cfg.get("watch_dirs"), list) and cfg["watch_dirs"]:
                cfg.setdefault("clear_cache_on_exit", True)
                return cfg
        except Exception:
            pass
    base = {"watch_dirs": list(DEFAULT_WATCH_DIRS), "password": DEFAULT_PASSWORD,
            "cover_names": list(DEFAULT_COVER_NAMES), "clear_cache_on_exit": True,
            "openers": {}}
    if PMX_EDITOR:                      # 本机装了 PMXEditor 才给默认入口
        base["openers"][".pmx"] = PMX_EDITOR
        base["openers"][".pmd"] = PMX_EDITOR
    return base


def cover_names():
    """用户配置的封面命名（忽略大小写比较，保留原始书写）"""
    cfg = load_config()
    raw = cfg.get("cover_names", DEFAULT_COVER_NAMES)
    if isinstance(raw, str):
        raw = [raw]
    out = []
    for n in raw or []:
        n = str(n).strip().replace("\\", "/").lstrip("/")
        if n and n not in out:
            out.append(n)
    return out or list(DEFAULT_COVER_NAMES)


def normalize_cover_names(raw):
    if isinstance(raw, str):
        raw = re.split(r"[,;\n\r]+", raw)
    out = []
    for n in raw or []:
        n = str(n).strip().replace("\\", "/").lstrip("/")
        # 只取文件名，不允许路径穿越；允许子目录写法但去掉 .. 
        parts = [x for x in n.split("/") if x and x not in (".", "..")]
        n = "/".join(parts)
        if n and n not in out:
            out.append(n)
    return out or list(DEFAULT_COVER_NAMES)


def save_config(cfg):
    try:
        with _cfg_lock:
            with open(CONFIG_FILE, "w", encoding="utf-8") as f:
                json.dump(cfg, f, ensure_ascii=False, indent=2)
    except Exception:
        # exe 放在只读目录时写不了配置，不影响本次运行
        pass


def cleanup_cache(days=7):
    """清理过期缓存。每次最多删 40 项，避免触发批量删除保护"""
    cutoff = time.time() - days * 86400
    removed = 0
    for root_dir in (THUMB_DIR, PMX_DIR, TMP_DIR):
        if not os.path.isdir(root_dir) or removed >= 40:
            continue
        for name in os.listdir(root_dir):
            if removed >= 40:
                break
            p = os.path.join(root_dir, name)
            try:
                if os.path.getmtime(p) < cutoff:
                    if os.path.isdir(p):
                        shutil.rmtree(p, ignore_errors=True)
                    else:
                        os.remove(p)
                    removed += 1
            except Exception:
                pass


def cache_size(path):
    total = 0
    for root, _dirs, files in os.walk(path):
        for f in files:
            try:
                total += os.path.getsize(os.path.join(root, f))
            except OSError:
                pass
    return total


def prune_extract_cache(limit_bytes=2 * 1024 ** 3, max_remove=40):
    """解压缓存超限时按最旧优先清理"""
    if not os.path.isdir(EXTRACT_DIR):
        return
    if cache_size(EXTRACT_DIR) <= limit_bytes:
        return
    items = []
    for sub in os.listdir(EXTRACT_DIR):
        p = os.path.join(EXTRACT_DIR, sub)
        try:
            items.append((os.path.getmtime(p), p))
        except OSError:
            pass
    items.sort()
    for _mt, p in items[:max_remove]:
        shutil.rmtree(p, ignore_errors=True)


def wipe_runtime_cache(include_thumbs=False):
    """退出时清空运行时缓存，返回释放的字节数。
    解压缓存(_cache/x) 和 PMX 导出(_cache/pmx) 是体积大头，删掉下次浏览会按需重建；
    缩略图默认保留（几十 MB，删了列表要重新生成，划不来）。"""
    freed = 0
    # 注意：不带 TRASH_DIR —— 那是工具内删除文件的回收站，用户可能还要还原
    targets = [EXTRACT_DIR, PMX_DIR, TMP_DIR]
    if include_thumbs:
        targets.append(THUMB_DIR)
    for d in targets:
        if not os.path.isdir(d):
            continue
        for name in os.listdir(d):
            p = os.path.join(d, name)
            try:
                if os.path.isdir(p):
                    freed += cache_size(p)
                    shutil.rmtree(p, ignore_errors=True)
                else:
                    freed += os.path.getsize(p)
                    os.remove(p)
            except Exception:
                pass
    return freed


def _should_wipe(cfg=None):
    if "--keep-cache" in sys.argv:
        return False
    cfg = cfg or load_config()
    return bool(cfg.get("clear_cache_on_exit", True))


def _wipe_now():
    try:
        cfg = load_config()
        if not _should_wipe(cfg):
            return
        freed = wipe_runtime_cache(include_thumbs=bool(cfg.get("clear_thumbs_too", False)))
        print(f"  已清空缓存，释放 {format_size(freed)}")
    except Exception:
        pass


def install_console_cleanup():
    """点黑框的 X 时（CTRL_CLOSE_EVENT）也把缓存清掉。
    atexit 在控制台关闭时不会执行，只能用 SetConsoleCtrlHandler。"""
    try:
        import ctypes
        from ctypes import wintypes
        Handler = ctypes.WINFUNCTYPE(wintypes.BOOL, wintypes.DWORD)

        def _h(evt):
            if evt in (2, 5, 6):      # CLOSE / LOGOFF / SHUTDOWN
                _wipe_now()
                return True
            return False

        ref = Handler(_h)
        ctypes.windll.kernel32.SetConsoleCtrlHandler(ref, True)
        globals()["_console_handler_ref"] = ref   # 保持引用，别被 GC
    except Exception:
        pass


def get_file_icon(name):
    return ""


def format_size(size):
    if size < 1024:
        return f"{size} B"
    if size < 1024 * 1024:
        return f"{size / 1024:.1f} KB"
    if size < 1024 * 1024 * 1024:
        return f"{size / (1024 * 1024):.1f} MB"
    return f"{size / (1024 * 1024 * 1024):.2f} GB"


def _run(cmd, timeout=180, cwd=None):
    return subprocess.run(cmd, capture_output=True, timeout=timeout, cwd=cwd,
                          creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))


def is_under_roots(path):
    """路径是否位于某个监控目录内（文件操作安全边界）"""
    real = os.path.abspath(path)
    for root in load_config()["watch_dirs"]:
        try:
            if os.path.commonpath([os.path.abspath(root), real]) == os.path.abspath(root):
                return True
        except ValueError:
            continue
    return False


# ==================== 压缩包扫描 ====================

def is_sfx_archive(path):
    try:
        st = os.stat(path)
    except OSError:
        return False
    key = (path, st.st_mtime, st.st_size)
    with _sfx_lock:
        if key in _sfx_cache:
            return _sfx_cache[key]
    ok = False
    try:
        r = _run([SEVEN_ZIP, "l", "-slt", "-ba", "-p-", path], timeout=30)
        out = r.stdout.decode("utf-8", "replace")
        ok = (r.returncode == 0) and ("Path = " in out) and ("Type = PE" not in out)
    except Exception:
        ok = False
    with _sfx_lock:
        _sfx_cache[key] = ok
    return ok


def scan_archives(watch_dirs):
    out = []
    for root in watch_dirs:
        if not os.path.isdir(root):
            continue
        for cur, dirs, files in os.walk(root):
            dirs[:] = [d for d in dirs if not d.startswith("_cache")]
            for f in files:
                ext = os.path.splitext(f)[1].lower()
                full = os.path.join(cur, f)
                if ext in ARCHIVE_EXTS:
                    kind = ext
                elif ext in SFX_EXTS:
                    if not is_sfx_archive(full):
                        continue
                    kind = ".sfx"
                else:
                    continue
                try:
                    size = os.path.getsize(full)
                except OSError:
                    size = 0
                rel = os.path.relpath(cur, root)
                rel = "" if rel == "." else rel.replace("\\", "/")
                top = rel.split("/")[0] if rel else ""
                out.append({
                    "name": f,
                    "path": full.replace("\\", "/"),
                    "dir": cur.replace("\\", "/"),
                    "size": format_size(size),
                    "raw_size": size,
                    "ext": kind,
                    "badge": "SFX" if kind == ".sfx" else ext.lstrip(".").upper(),
                    "icon": "",
                    "root": root,
                    "rel": rel,
                    "dir_rel": rel,
                    "group": top,
                })
    out.sort(key=lambda x: (x["root"], x["rel"], x["name"]))
    return out


def tree_list(node, prefix=""):
    """把内部目录树转成前端用的嵌套列表：{name,path,count,children}"""
    out = []
    for name in sorted(node["children"], key=str.lower):
        ch = node["children"][name]
        p = (prefix + "/" + name) if prefix else name
        out.append({"name": name, "path": p, "count": ch["count"],
                    "children": tree_list(ch, p)})
    return out


def build_meta(watch_dirs):
    arch = scan_archives(watch_dirs)
    with _enc_lock:
        enc_snapshot = dict(_enc_cache)
    for a in arch:
        a["encrypted"] = enc_snapshot.get(_enc_key(a["path"]))
    roots = []
    for root in watch_dirs:
        items = [a for a in arch if a["root"] == root]
        # 目录树：按 rel 的每一级建节点，子文件夹才能在左侧逐级展开
        tree = {"children": {}, "count": 0}
        for a in items:
            rel = a.get("rel") or ""
            node = tree
            node["count"] += 1
            for part in [p for p in rel.split("/") if p]:
                node = node["children"].setdefault(part, {"children": {}, "count": 0})
                node["count"] += 1
        roots.append({
            "path": root,
            "exists": os.path.isdir(root),
            "count": len(items),
            "size": format_size(sum(a["raw_size"] for a in items)),
            "groups": tree_list(tree),
        })
    return {
        "roots": roots,
        "total": len(arch),
        "sfx": len([a for a in arch if a["ext"] == ".sfx"]),
        "encTotal": len([a for a in arch if a["encrypted"] is True]),
        "encKnown": len([a for a in arch if a["encrypted"] is not None]),
        "password": load_config().get("password", DEFAULT_PASSWORD),
        "archives": arch,
    }


# ==================== 7z 读取层 ====================

def list_cached(filepath, password=None):
    """带缓存的目录列表（贴图兜底查找时频繁调用）"""
    try:
        st = os.stat(filepath)
        key = (filepath, st.st_mtime, st.st_size, password)
    except OSError:
        key = (filepath, 0, 0, password)
    with _list_lock:
        if key in _list_cache:
            return _list_cache[key]
    files = list_archive(filepath, password)
    with _list_lock:
        if len(_list_cache) > 64:
            _list_cache.clear()
        _list_cache[key] = files
    return files


def list_archive(filepath, password=None):
    attempts = []
    if password:
        attempts.append(f"-p{password}")
    attempts.append("-p-")
    last = ""
    for pw in attempts:
        try:
            r = _run([SEVEN_ZIP, "l", "-slt", "-ba", "-sccUTF-8", pw, filepath], timeout=120)
        except subprocess.TimeoutExpired:
            last = "读取超时"
            continue
        out = r.stdout.decode("utf-8", "replace")
        err = r.stderr.decode("utf-8", "replace")
        if r.returncode != 0 and "Path = " not in out:
            low = err.lower()
            last = "密码错误" if "password" in low else (err.strip()[:200] or f"7z 返回码 {r.returncode}")
            continue
        entries = _parse_slt(out)
        if password is None and any(e["encrypted"] for e in entries):
            last = "需要密码"
            continue
        return _to_files(entries)
    raise Exception(last or "无法读取压缩包")


def _parse_slt(out):
    entries, cur = [], {}
    for line in out.splitlines():
        line = line.rstrip("\r")
        if not line.strip():
            if cur.get("Path"):
                entries.append({
                    "path": cur["Path"],
                    "size": int(cur.get("Size", "0") or 0),
                    "is_dir": ("D" in cur.get("Attributes", "")) or (cur.get("Folder") == "+"),
                    "encrypted": cur.get("Encrypted") == "+",
                })
            cur = {}
            continue
        if " = " in line:
            k, v = line.split(" = ", 1)
            cur[k.strip()] = v.strip()
    if cur.get("Path"):
        entries.append({
            "path": cur["Path"],
            "size": int(cur.get("Size", "0") or 0),
            "is_dir": ("D" in cur.get("Attributes", "")) or (cur.get("Folder") == "+"),
            "encrypted": cur.get("Encrypted") == "+",
        })
    return entries


def _to_files(entries):
    out = []
    for e in entries:
        if e["is_dir"]:
            continue
        p = e["path"].replace("\\", "/")
        ext = os.path.splitext(p)[1].lower()
        out.append({
            "name": p.rsplit("/", 1)[-1],
            "path": p,
            "size": format_size(e["size"]),
            "raw_size": e["size"],
            "ext": ext,
            "icon": get_file_icon(p),
            "is_image": ext in IMAGE_EXTS,
            "is_pmx": ext in PMX_EXTS,
            "is_3d": ext in MODEL3D_EXTS,
            "is_archive": ext in ARCHIVE_EXTS or ext in SFX_EXTS,
            "encrypted": e["encrypted"],
        })
    out.sort(key=lambda x: (x["path"].rsplit("/", 1)[0] if "/" in x["path"] else "", x["name"].lower()))
    return out


def extract_one(filepath, inner_path, password=None, dest_dir=None):
    if dest_dir is None:
        # 兜底：落到解压缓存里，不建一次性临时目录（避免删除被安全策略拦截后堆积）
        dest_dir = os.path.join(EXTRACT_DIR, "_misc", _xkey(filepath, inner_path, password))
        os.makedirs(dest_dir, exist_ok=True)
    attempts = [f"-p{password}"] if password else []
    attempts.append("-p-")
    cands = [inner_path.replace("/", "\\"), inner_path]
    last = ""
    for pw in attempts:
        for cand in cands:
            try:
                r = _run([SEVEN_ZIP, "x", "-y", "-bso0", "-bse0", "-bsp0",
                          "-sccUTF-8", pw, f"-o{dest_dir}", filepath, cand], timeout=300)
            except subprocess.TimeoutExpired:
                last = "解压超时"
                continue
            if r.returncode != 0:
                last = r.stderr.decode("utf-8", "replace").strip()[:200]
                continue
            found = _locate(dest_dir, inner_path)
            if found:
                return found
    raise Exception(last or f"未能提取 {inner_path}")


def _locate(dest_dir, inner_path):
    direct = os.path.join(dest_dir, inner_path.replace("/", os.sep))
    if os.path.isfile(direct):
        return direct
    base = os.path.basename(inner_path)
    for root, _d, files in os.walk(dest_dir):
        if base in files:
            return os.path.join(root, base)
    return None


def _xkey(filepath, inner_path, password):
    try:
        st = os.stat(filepath)
        raw = f"{filepath}|{st.st_mtime}|{st.st_size}|{inner_path}|{password}"
    except OSError:
        raw = f"{filepath}|{inner_path}|{password}"
    return hashlib.md5(raw.encode("utf-8", "replace")).hexdigest()


def read_bytes(filepath, inner_path, password=None):
    """读压缩包内单个文件。
    解压结果按 (包路径+修改时间+包内路径+密码) 哈希持久化到 _cache/x，
    命中缓存就不再调 7z —— 贴图/模型重复读取快很多，也不会产生临时垃圾。"""
    key = _xkey(filepath, inner_path, password)
    base = os.path.join(EXTRACT_DIR, key[:2], key)
    direct = os.path.join(base, inner_path.replace("/", os.sep))

    if os.path.isfile(direct):
        with open(direct, "rb") as f:
            return f.read()

    os.makedirs(base, exist_ok=True)
    p = extract_one(filepath, inner_path, password, dest_dir=base)
    with open(p, "rb") as f:
        return f.read()


def extract_all(filepath, password, dest_dir):
    attempts = [f"-p{password}"] if password else []
    attempts.append("-p-")
    for pw in attempts:
        try:
            r = _run([SEVEN_ZIP, "x", "-y", "-bso0", "-bse0", "-bsp0",
                      "-sccUTF-8", pw, f"-o{dest_dir}", filepath], timeout=1800)
        except subprocess.TimeoutExpired:
            continue
        if r.returncode == 0:
            return True
    return False


# ==================== PMX 解析 ====================

def parse_pmx(data):
    try:
        if len(data) < 16:
            return {"format": "未知", "error": "文件过小"}
        if data[:3] == b"Pmd":
            return {
                "format": "PMD",
                "version": "1.0",
                "model_name_jp": data[3:23].decode("shift_jis", "replace").strip("\x00"),
                "model_name_en": data[23:43].decode("shift_jis", "replace").strip("\x00"),
            }
        if data[:4] != b"PMX ":
            return {"format": "未知", "error": f"不是 PMX (magic {data[:4].hex()})"}

        version = struct.unpack_from("<f", data, 4)[0]
        off = 9
        enc_byte = data[off]; off += 1
        off += 1
        idx = list(data[off:off + 6]); off += 6
        enc = "utf-16-le" if enc_byte == 0 else "utf-8"

        def rd(o):
            n = struct.unpack_from("<i", data, o)[0]
            return data[o + 4:o + 4 + n].decode(enc, "replace"), o + 4 + n

        name_jp, off = rd(off)
        comment_jp, off = rd(off)
        name_en, off = rd(off)
        comment_en, off = rd(off)
        vcount = struct.unpack_from("<i", data, off)[0]
        return {
            "format": "PMX",
            "version": f"{version:.1f}",
            "model_name_jp": name_jp,
            "model_name_en": name_en,
            "comment_jp": (comment_jp or "")[:400],
            "comment_en": (comment_en or "")[:400],
            "vertex_count": vcount,
            "encoding": "UTF-16LE" if enc_byte == 0 else "UTF-8",
            "idx_sizes": idx,
        }
    except Exception as e:
        return {"format": "解析错误", "error": str(e)}


# ==================== 缩略图 ====================

def thumb_path(filepath, inner):
    try:
        st = os.stat(filepath)
        key = f"{filepath}|{st.st_mtime}|{st.st_size}|{inner}"
    except OSError:
        key = f"{filepath}|{inner}"
    return os.path.join(THUMB_DIR, hashlib.md5(key.encode("utf-8", "replace")).hexdigest() + ".png")


def make_thumb(filepath, inner, password=None, size=220):
    ensure_dirs()
    cp = thumb_path(filepath, inner)
    if os.path.isfile(cp):
        return cp
    with _thumb_lock:
        if os.path.isfile(cp):
            return cp
        try:
            raw = read_bytes(filepath, inner, password)
        except Exception:
            return None
        try:
            from PIL import Image
            im = Image.open(io.BytesIO(raw))
            im.load()
            if im.mode not in ("RGB", "RGBA"):
                im = im.convert("RGBA")
            im.thumbnail((size, size), Image.LANCZOS)
            tmp = cp + ".t.png"
            im.save(tmp, "PNG")
            os.replace(tmp, cp)
            return cp
        except Exception:
            return None


# ==================== 压缩包封面 ====================
_cover_lock = threading.Lock()
_cover_index = {}   # (archive path, mtime, size, names-tuple, password) -> inner path or ""


def _cover_key(filepath, password, names):
    try:
        st = os.stat(filepath)
        mt, sz = st.st_mtime, st.st_size
    except OSError:
        mt, sz = 0, 0
    return (filepath, mt, sz, tuple(names), password or "")


def find_cover(filepath, password=None, names=None):
    """在包内找封面图：
       优先级 = 用户配置里的命名顺序；同名时优先 ZipPreview/ 专用目录，其次根目录，最后任意目录。
       返回包内路径，找不到返回空串。"""
    names = names if names is not None else cover_names()
    key = _cover_key(filepath, password, names)
    with _cover_lock:
        if key in _cover_index:
            return _cover_index[key]
    inner = ""
    try:
        entries = list_cached(filepath, password)
    except Exception:
        entries = []
    if entries:
        lows = [n.lower() for n in names]
        best = None
        for f in entries:
            p = f["path"]
            base = p.rsplit("/", 1)[-1]
            bl = base.lower()
            order = next((i for i, n in enumerate(lows) if n == bl or n == p.lower()
                          or p.lower().endswith("/" + n)), None)
            if order is None:
                continue
            folder = p.rsplit("/", 1)[0].lower() if "/" in p else ""
            if folder == COVER_FOLDER.lower():
                tier = 0
            elif folder.endswith("/" + COVER_FOLDER.lower()):
                tier = 1
            elif not folder:
                tier = 2
            else:
                tier = 3
            score = (order, tier, len(p))
            if best is None or score < best[0]:
                best = (score, p)
        if best:
            inner = best[1]
    with _cover_lock:
        if len(_cover_index) > 512:
            _cover_index.clear()
        _cover_index[key] = inner
    return inner


def cover_cache_path(filepath, inner, password, names):
    key = _cover_key(filepath, password, names) + (inner,)
    return os.path.join(COVER_DIR, hashlib.md5(repr(key).encode("utf-8", "replace")).hexdigest() + ".png")


def get_cover_png(filepath, password=None, names=None, size=520):
    """取封面并生成缓存 PNG；无封面返回 None"""
    names = names if names is not None else cover_names()
    inner = find_cover(filepath, password, names)
    if not inner:
        return None
    cp = cover_cache_path(filepath, inner, password, names)
    if os.path.isfile(cp):
        return cp
    try:
        raw = read_bytes(filepath, inner, password)
        if not raw:
            return None
        ext = os.path.splitext(inner)[1].lower()
        data = raw if ext in (".png", ".jpg", ".jpeg", ".webp", ".gif") else to_web_image(raw)
        if not data:
            return None
        from PIL import Image
        im = Image.open(io.BytesIO(data))
        im.load()
        if im.mode not in ("RGB", "RGBA"):
            im = im.convert("RGBA")
        im.thumbnail((size, size), Image.LANCZOS)
        tmp = cp + ".t.png"
        im.save(tmp, "PNG")
        os.replace(tmp, cp)
        return cp
    except Exception:
        return None


def to_web_image(raw):
    """把浏览器不认的贴图（tga/bmp/dds）转成 PNG；失败返回 None"""
    try:
        from PIL import Image
        im = Image.open(io.BytesIO(raw))
        im.load()
        if im.mode not in ("RGB", "RGBA"):
            im = im.convert("RGBA")
        buf = io.BytesIO()
        im.save(buf, "PNG")
        return buf.getvalue()
    except Exception:
        return None


# ==================== 路由：页面与静态 ====================

@app.route("/")
def index():
    resp = Response(PAGE_HTML, mimetype="text/html")
    resp.headers["Cache-Control"] = "no-store, no-cache, must-revalidate, max-age=0"
    resp.headers["Pragma"] = "no-cache"
    return resp


@app.route("/vendor/<path:name>")
def vendor(name):
    p = os.path.join(VENDOR_DIR, name)
    if not os.path.isfile(p):
        abort(404)
    return send_file(p, max_age=86400)


# ==================== 路由：元数据 ====================

@app.route("/api/meta")
def api_meta():
    cfg = load_config()
    return jsonify(build_meta(cfg["watch_dirs"]))


@app.route("/api/encryption")
def api_encryption():
    """后台预热的结果：{path: true/false}，未探测完的不会出现"""
    meta = build_meta(load_config()["watch_dirs"])
    out = {a["path"]: a["encrypted"] for a in meta["archives"] if a["encrypted"] is not None}
    return jsonify({"map": out, "done": meta["encKnown"] >= meta["total"]})


@app.route("/api/settings")
def api_settings_get():
    cfg = load_config()
    return jsonify({"cover_names": cover_names(), "cover_folder": COVER_FOLDER,
                    "default_cover_names": DEFAULT_COVER_NAMES,
                    "openers": cfg.get("openers") or {},
                    "passwords": cfg.get("passwords") or [],
                    "seven_zip": SEVEN_ZIP, "unrar": UNRAR,
                    "text_editor": cfg.get("text_editor") or ""})


def apply_tool_paths(cfg):
    """从配置里刷新外部工具路径（改完设置立即生效，不用重启）"""
    global SEVEN_ZIP, UNRAR, PMX_EDITOR
    for key, var in (("seven_zip", "SEVEN_ZIP"), ("unrar", "UNRAR"), ("pmx_editor", "PMX_EDITOR")):
        v = (cfg.get(key) or "").strip()
        if v and os.path.isfile(v):
            globals()[var] = v


def normalize_passwords(raw):
    """密码库：去重、去空白、保持顺序；也接受换行分隔的字符串"""
    if isinstance(raw, str):
        items = raw.replace("\r", "\n").split("\n")
    elif isinstance(raw, list):
        items = raw
    else:
        items = []
    out = []
    for p in items:
        p = str(p).strip()
        if p and p not in out:
            out.append(p)
    return out


def normalize_openers(raw):
    """.zprj -> D:\\...\\MarvelousDesigner.exe ；也接受 "zprj=路径" 的多行文本"""
    out = {}
    if isinstance(raw, str):
        pairs = [ln.split("=", 1) for ln in raw.splitlines() if "=" in ln]
    elif isinstance(raw, dict):
        pairs = list(raw.items())
    else:
        pairs = []
    for k, v in pairs:
        k = str(k).strip().lower()
        v = str(v).strip().strip('"')
        if not k or not v:
            continue
        if not k.startswith("."):
            k = "." + k
        out[k] = v
    return out


def openers():
    return normalize_openers(load_config().get("openers") or {})


# 文本类：没有单独配置时用记事本打开（也可以给 .txt 配 Notepad++ / VS Code）
TEXT_EXTS = {".txt", ".md", ".json", ".xml", ".ini", ".cfg", ".log", ".csv",
             ".yml", ".yaml", ".py", ".bat", ".ps1", ".html", ".htm", ".srt", ".ass"}
_last_open = {}


def _parse_prog(prog):
    """配置里可以写「程序 + 参数」，例如：
         C:\\...\\Code.exe -r
         C:\\...\\notepad++.exe -multiInst
       返回 (exe, 参数列表)。"""
    s = (prog or "").strip()
    if not s:
        return "", []
    try:
        parts = shlex.split(s, posix=False)
    except Exception:
        parts = [s]
    parts = [p.strip('"') for p in parts if p.strip()]
    if not parts:
        return "", []
    exe = parts[0]
    if not os.path.isfile(exe):
        exe = shutil.which(exe) or ""
    if not exe:
        return "", []
    return exe, parts[1:]


@app.route("/api/settings", methods=["POST"])
def api_settings_save():
    body = request.get_json(silent=True) or {}
    cfg = load_config()
    if "cover_names" in body:
        names = normalize_cover_names(body.get("cover_names"))
        cfg["cover_names"] = names
    if "openers" in body:
        cfg["openers"] = normalize_openers(body.get("openers"))
    if "passwords" in body:
        cfg["passwords"] = normalize_passwords(body.get("passwords"))
    for k in ("seven_zip", "unrar", "text_editor", "pmx_editor"):
        if k in body:
            cfg[k] = str(body.get(k) or "").strip()
    save_config(cfg)
    apply_tool_paths(cfg)
    with _cover_lock:
        _cover_index.clear()
        for f in os.listdir(COVER_DIR):
            if f.endswith(".png"):
                try:
                    os.remove(os.path.join(COVER_DIR, f))
                except OSError:
                    pass
    return jsonify({"ok": True, "cover_names": cover_names(),
                    "openers": cfg.get("openers") or {},
                    "passwords": cfg.get("passwords") or [],
                    "seven_zip": SEVEN_ZIP, "unrar": UNRAR,
                    "text_editor": cfg.get("text_editor") or ""})


@app.route("/api/open_external", methods=["POST"])
def api_open_external():
    """把包内文件解到临时目录，用配置好的外部程序打开（.zprj → Marvelous Designer 等）。
    文本类没单独配置时默认用记事本；同一个文件 1.2 秒内重复点击只启动一次（防双击开两个）。"""
    body = request.get_json(silent=True) or {}
    p = body.get("path") or ""
    inner = body.get("inner") or ""
    ext = (body.get("ext") or os.path.splitext(inner)[1]).lower()
    prog = openers().get(ext)
    if not prog and ext in TEXT_EXTS:
        prog = (load_config().get("text_editor") or "").strip() or "notepad.exe"
    if not prog:
        return jsonify({"error": f"还没有给 {ext} 配置外部程序（设置 → 格式关联）"}), 400
    exe, extra = _parse_prog(prog)
    if not exe:
        return jsonify({"error": "程序不存在（检查 设置 → 格式关联）"}), 400
    if not os.path.isfile(p):
        return jsonify({"error": "压缩包不存在"}), 404
    pw = body.get("password") or load_config().get("password", DEFAULT_PASSWORD)
    try:
        data = read_bytes(p, inner, pw)
    except Exception:
        try:
            data = read_bytes(p, inner, None)
        except Exception as e:
            return jsonify({"error": str(e)}), 500
    ensure_dirs()
    target = os.path.join(TMP_DIR, "%s_%s" % (
        hashlib.md5((p + inner).encode("utf-8", "replace")).hexdigest()[:8],
        os.path.basename(inner) or "file" + ext))
    try:
        with open(target, "wb") as f:
            f.write(data)
        # 同一个文件短时间内重复点（双击）只启动一次
        key = (exe.lower(), target.lower())
        now = time.time()
        if now - _last_open.get(key, 0) < 1.2:
            return jsonify({"ok": True, "file": target, "skipped": True})
        _last_open[key] = now
        subprocess.Popen([exe] + extra + [target], close_fds=True)
    except Exception as e:
        return jsonify({"error": str(e)}), 500
    return jsonify({"ok": True, "file": target})


@app.route("/api/cover")
def api_cover():
    """压缩包封面图；无封面返回 1x1 透明 PNG（前端 img 保持占位）"""
    p = request.args.get("path", "")
    pw = request.args.get("password", "") or load_config().get("password", DEFAULT_PASSWORD)
    if not os.path.isfile(p):
        return Response(BLANK_PNG, mimetype="image/png")
    cp = get_cover_png(p, pw)
    if not cp:
        return Response(BLANK_PNG, mimetype="image/png")
    return send_file(cp, mimetype="image/png", max_age=120)


_cover_flag = {}


@app.route("/api/covers")
def api_covers():
    """批量统计「有没有预览图」，给筛选和批量模式用（按 路径+mtime+size 缓存）"""
    cfg = load_config()
    names = cover_names()
    pw = cfg.get("password", DEFAULT_PASSWORD)
    out = {}
    for a in scan_archives(cfg["watch_dirs"]):
        p = a["path"].replace("/", "\\")
        try:
            st = os.stat(p)
            key = (p, st.st_mtime, st.st_size)
        except OSError:
            out[a["path"]] = False
            continue
        if key not in _cover_flag:
            try:
                _cover_flag[key] = bool(find_cover(p, pw, names))
            except Exception:
                _cover_flag[key] = False
        out[a["path"]] = _cover_flag[key]
    return jsonify({"map": out})


@app.route("/api/cover/delete", methods=["POST"])
def api_cover_delete():
    """删掉包内的预览图（ZipPreview/xxx.png）"""
    body = request.get_json(silent=True) or {}
    p = body.get("path", "")
    pw = body.get("password") or load_config().get("password", DEFAULT_PASSWORD)
    if not os.path.isfile(p) or not is_under_roots(p):
        return jsonify({"error": "压缩包路径无效"}), 400
    ext = os.path.splitext(p)[1].lower()
    if ext not in (".zip", ".7z"):
        return jsonify({"error": "rar / 自解压包不支持修改"}), 400
    inner = ""
    try:
        inner = find_cover(p, pw, cover_names())
    except Exception:
        inner = ""
    if not inner:
        return jsonify({"ok": True, "removed": False})
    base = [SEVEN_ZIP, "d", "-y", "-bso0", "-bse0"]
    r = _run(base + ["-p" + pw, p, inner], timeout=120)
    if r.returncode != 0:
        r = _run(base + [p, inner], timeout=120)
    if r.returncode != 0:
        return jsonify({"error": "删除失败：" + (r.stderr.decode("utf-8", "replace").strip()[:160] or str(r.returncode))}), 500
    with _cover_lock:
        _cover_index.clear()
    with _list_lock:
        _list_cache.clear()
    _cover_flag.clear()
    return jsonify({"ok": True, "removed": True})


@app.route("/api/cover/save", methods=["POST"])
def api_cover_save():
    """把视口截图写入当前压缩包内的 ZipPreview/ 目录（不改动任何源文件）"""
    body = request.get_json(silent=True) or {}
    p = body.get("path", "")
    png = body.get("png", "")           # dataURL
    if not os.path.isfile(p) or not is_under_roots(p):
        return jsonify({"error": "压缩包路径无效"}), 400
    if not png.startswith("data:image/png;base64,"):
        return jsonify({"error": "截图数据无效"}), 400
    try:
        import base64
        raw = base64.b64decode(png.split(",", 1)[1])
    except Exception:
        return jsonify({"error": "截图解码失败"}), 400
    ext = os.path.splitext(p)[1].lower()
    if ext not in (".zip", ".7z"):
        return jsonify({"error": "rar / 自解压包不支持写入封面，请改用 zip 或 7z"}), 400
    names = cover_names()
    name = os.path.basename(names[0]) or "ZipPreview.png"
    pw = body.get("password", "") or load_config().get("password", DEFAULT_PASSWORD)
    try:
        tmpdir = tempfile.mkdtemp(dir=TMP_DIR)
        folder = os.path.join(tmpdir, COVER_FOLDER)
        os.makedirs(folder, exist_ok=True)
        target = os.path.join(folder, name)
        # 名称后缀不是 png 时转换成对应格式
        ne = os.path.splitext(name)[1].lower()
        if ne in (".jpg", ".jpeg", ".webp"):
            from PIL import Image
            im = Image.open(io.BytesIO(raw)).convert("RGB")
            im.save(target, "JPEG" if ne != ".webp" else "WEBP", quality=92)
        else:
            with open(target, "wb") as f:
                f.write(raw)
        # 先不带密码写入：包本来没加密时，封面也不该被加密（否则资源管理器里要密码）。
        # 只有包是加密的（不带密码写不进去）才回退到用同一密码写入。
        base = [SEVEN_ZIP, "a", "-y", "-bso0", "-bse0"]
        rel = os.path.join(COVER_FOLDER, name)
        r = _run(base + [p, rel], timeout=120, cwd=tmpdir)
        if r.returncode != 0 and pw:
            r = _run(base + ["-p" + pw, p, rel], timeout=120, cwd=tmpdir)
        if r.returncode != 0:
            return jsonify({"error": "写入失败：" + (r.stderr.decode("utf-8", "replace").strip()[:160] or str(r.returncode))}), 500
    except Exception as e:
        return jsonify({"error": str(e)}), 500
    finally:
        try:
            shutil.rmtree(tmpdir, ignore_errors=True)
        except Exception:
            pass
    with _cover_lock:
        _cover_index.clear()
        for f in os.listdir(COVER_DIR):
            if f.endswith(".png"):
                try:
                    os.remove(os.path.join(COVER_DIR, f))
                except OSError:
                    pass
    with _list_lock:
        _list_cache.clear()
    return jsonify({"ok": True, "inner": COVER_FOLDER + "/" + name})


@app.route("/api/pick_folder", methods=["POST"])
def api_pick_folder():
    """系统原生「选择文件夹」对话框"""
    ps = (
        "Add-Type -AssemblyName System.Windows.Forms | Out-Null;"
        "$f=New-Object System.Windows.Forms.Form;"
        "$f.TopMost=$true;$f.ShowInTaskbar=$false;$f.WindowState='Minimized';$f.Show();"
        "$d=New-Object System.Windows.Forms.FolderBrowserDialog;"
        "$d.Description='选择文件夹';"
        "if($d.ShowDialog($f) -eq [System.Windows.Forms.DialogResult]::OK){[Console]::Out.Write($d.SelectedPath)};"
        "$f.Close()"
    )
    try:
        r = subprocess.run(
            ["powershell", "-NoProfile", "-STA", "-Command", ps],
            capture_output=True, timeout=300,
            creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
        out = r.stdout.decode("utf-8", "replace").strip()
        return jsonify({"path": out} if out else {"error": "没有选择"})
    except Exception as e:
        return jsonify({"error": str(e)}), 500


@app.route("/api/pick_file", methods=["POST"])
def api_pick_file():
    """弹一个系统原生的选文件对话框（和工具在同一台机器上），返回选中的 exe 路径"""
    ps = (
        "Add-Type -AssemblyName System.Windows.Forms | Out-Null;"
        "$f=New-Object System.Windows.Forms.Form;"
        "$f.TopMost=$true;$f.ShowInTaskbar=$false;$f.WindowState='Minimized';$f.Show();"
        "$d=New-Object System.Windows.Forms.OpenFileDialog;"
        "$d.Filter='程序 (*.exe)|*.exe|所有文件 (*.*)|*.*';"
        "if($d.ShowDialog($f) -eq [System.Windows.Forms.DialogResult]::OK){[Console]::Out.Write($d.FileName)};"
        "$f.Close()"
    )
    try:
        r = subprocess.run(
            ["powershell", "-NoProfile", "-STA", "-Command", ps],
            capture_output=True, timeout=300,
            creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
        out = r.stdout.decode("utf-8", "replace").strip()
        return jsonify({"path": out} if out else {"error": "没有选择文件"})
    except Exception as e:
        return jsonify({"error": str(e)}), 500


@app.route("/api/browser_settings", methods=["POST"])
def api_browser_settings():
    """用本工具的浏览器配置打开 Edge 的外观设置页，用来关掉「鼠标手势」"""
    exe = _find_browser()
    if not exe:
        return jsonify({"error": "没找到 Edge / Chrome"}), 400
    prof = _profile_dir()
    try:
        subprocess.Popen([exe, f"--user-data-dir={prof}", "--no-first-run",
                          "--no-default-browser-check", "edge://settings/appearance"],
                         stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                         stdin=subprocess.DEVNULL)
    except Exception as e:
        return jsonify({"error": str(e)}), 500
    return jsonify({"ok": True})


@app.route("/api/roots", methods=["POST"])
def api_roots():
    body = request.get_json(silent=True) or {}
    roots = body.get("roots")
    if not isinstance(roots, list):
        return jsonify({"error": "参数错误"}), 400
    clean = []
    for r in roots:
        r = (r or "").strip()
        if not r:
            continue
        r = os.path.normpath(r)
        if r not in clean:
            clean.append(r)
    if not clean:
        return jsonify({"error": "至少要保留一个目录"}), 400
    cfg = load_config()
    cfg["watch_dirs"] = clean
    save_config(cfg)
    threading.Thread(target=prewarm_encryption, args=(clean,), daemon=True).start()
    return jsonify({"ok": True, "meta": build_meta(clean)})


# ==================== 路由：压缩包内容 ====================

@app.route("/api/list")
def api_list():
    filepath = request.args.get("path", "")
    password = request.args.get("password", "") or load_config().get("password", DEFAULT_PASSWORD)
    if not os.path.isfile(filepath):
        return jsonify({"error": "文件不存在"}), 404
    try:
        files = list_cached(filepath, password)
        return jsonify({"files": files, "count": len(files)})
    except Exception as e:
        msg = str(e)
        low = msg.lower()
        need_pw = any(k in msg for k in ("密码", "需要密码")) or \
                  any(k in low for k in ("password", "encrypted", "wrong password"))
        try:
            files = list_archive(filepath, None)
            if need_pw or any(f.get("encrypted") for f in files):
                return jsonify({"need_password": True, "error": msg or "需要密码"})
            return jsonify({"files": files, "count": len(files)})
        except Exception:
            if need_pw:
                return jsonify({"need_password": True, "error": msg})
            return jsonify({"error": msg}), 500


@app.route("/api/thumb")
def api_thumb():
    p = request.args.get("path", "")
    inner = request.args.get("inner", "")
    pw = request.args.get("password", "") or load_config().get("password", DEFAULT_PASSWORD)
    if not os.path.isfile(p) or not inner:
        abort(404)
    cp = make_thumb(p, inner, pw)
    if not cp:
        return Response(BLANK_PNG, mimetype="image/png")
    return send_file(cp, mimetype="image/png", max_age=3600)


@app.route("/api/image")
def api_image():
    p = request.args.get("path", "")
    inner = request.args.get("inner", "")
    pw = request.args.get("password", "") or load_config().get("password", DEFAULT_PASSWORD)
    if not os.path.isfile(p):
        abort(404)
    try:
        data = read_bytes(p, inner, pw)
    except Exception:
        try:
            data = read_bytes(p, inner, None)
        except Exception as e:
            return jsonify({"error": str(e)}), 500
    if not data:
        return jsonify({"error": "空文件"}), 500
    ext = os.path.splitext(inner)[1].lower()
    # TGA / BMP / DDS 浏览器不认，服务端转 PNG 再看大图
    if ext in (".tga", ".bmp", ".dds"):
        png = to_web_image(data)
        if png:
            return send_file(io.BytesIO(png), mimetype="image/png")
        return Response(BLANK_PNG, mimetype="image/png")
    mime = {".png": "image/png", ".jpg": "image/jpeg", ".jpeg": "image/jpeg",
            ".webp": "image/webp", ".gif": "image/gif"}.get(ext, "application/octet-stream")
    return send_file(io.BytesIO(data), mimetype=mime)


@app.route("/api/pmx")
def api_pmx():
    p = request.args.get("path", "")
    inner = request.args.get("inner", "")
    pw = request.args.get("password", "") or load_config().get("password", DEFAULT_PASSWORD)
    if not os.path.isfile(p):
        abort(404)
    try:
        data = read_bytes(p, inner, pw)
    except Exception:
        try:
            data = read_bytes(p, inner, None)
        except Exception as e:
            return jsonify({"error": str(e)}), 500
    return jsonify(parse_pmx(data))


@app.route("/api/model")
def api_model():
    """模型原始字节（给 three.js 的 loader 用）"""
    p = request.args.get("path", "")
    inner = request.args.get("inner", "")
    pw = request.args.get("password", "") or load_config().get("password", DEFAULT_PASSWORD)
    if not os.path.isfile(p):
        abort(404)
    try:
        data = read_bytes(p, inner, pw)
    except Exception:
        try:
            data = read_bytes(p, inner, None)
        except Exception as e:
            return jsonify({"error": str(e)}), 500
    return Response(data, mimetype="application/octet-stream")


# ---------- 批量预解压：模型加载时把同目录资源一次性解出来 ----------
_pf_lock = threading.Lock()


def _extract_key(archive):
    """同一个压缩包（路径+修改时间+大小）对应同一个缓存目录"""
    try:
        st = os.stat(archive)
    except OSError:
        return ""
    raw = "%s|%d|%d" % (archive, int(st.st_mtime), st.st_size)
    return hashlib.md5(raw.encode("utf-8", "replace")).hexdigest()[:16]


def _prefetch_lookup(archive, inner):
    """预解压缓存里有没有这个文件；有就直接返回字节"""
    key = _extract_key(archive)
    if not key or not inner:
        return None
    safe = os.path.normpath(inner).replace("\\", "/")
    if safe.startswith("../") or safe.startswith("/"):
        return None
    dst = os.path.join(EXTRACT_DIR, key, safe)
    try:
        if os.path.isfile(dst):
            with open(dst, "rb") as f:
                return f.read()
    except OSError:
        pass
    return None


def _pf_complete(archive):
    """整包是否已经预解压过"""
    key = _extract_key(archive)
    if not key:
        return False
    marker = os.path.join(EXTRACT_DIR, key, ".pf_" + hashlib.md5(b"").hexdigest()[:10])
    return os.path.isfile(marker)


@app.route("/api/prefetch", methods=["POST"])
def api_prefetch():
    """把某个包内目录下的资源一次性解到缓存，之后贴图请求直接读本地文件。
    体积/数量超限就跳过（避免为了一个模型白解几百 MB）。"""
    body = request.get_json(silent=True) or {}
    arc = body.get("path") or ""
    req_dir = (body.get("dir") or "").replace("\\", "/").strip().strip("/")
    if not arc or not os.path.isfile(arc) or not SEVEN_ZIP:
        return jsonify({"ok": False})
    pw = body.get("password") or load_config().get("password", DEFAULT_PASSWORD)
    key = _extract_key(arc)
    if not key:
        return jsonify({"ok": False})
    dest = os.path.join(EXTRACT_DIR, key)

    try:
        entries = list_archive(arc, pw if pw else None)
    except Exception:
        return jsonify({"ok": False})

    # 优先整个包都解出来（PMX 的贴图常在同级目录或 tex 子目录，只解模型目录会漏）；
    # 整个包太大时退化成只解模型所在目录。
    total_all = sum(int(e.get("raw_size") or 0) for e in entries)
    if total_all <= 400 * 1024 * 1024 and len(entries) <= 800:
        inner_dir = ""
    else:
        inner_dir = req_dir
        pre = inner_dir.lower() + "/" if inner_dir else ""
        sub = [e for e in entries if (not pre or e["path"].lower().startswith(pre))]
        total = sum(int(e.get("raw_size") or 0) for e in sub)
        if total > 300 * 1024 * 1024 or len(sub) > 500:
            return jsonify({"ok": True, "skipped": True, "bytes": total, "count": len(sub)})

    marker = os.path.join(dest, ".pf_" + hashlib.md5(inner_dir.encode("utf-8")).hexdigest()[:10])
    if os.path.isfile(marker):
        return jsonify({"ok": True, "cached": True})

    with _pf_lock:
        if os.path.isfile(marker):
            return jsonify({"ok": True, "cached": True})
        ensure_dirs()
        part = dest + ".tmp"
        shutil.rmtree(part, ignore_errors=True)
        os.makedirs(part, exist_ok=True)
        args = [SEVEN_ZIP, "x", arc, "-o" + part, "-y", "-sccUTF-8",
                ("-p" + pw) if pw else "-p-"]
        if inner_dir:
            args.append(inner_dir + "/*")
        try:
            r = _run(args, timeout=180)
            if r.returncode not in (0, 1):
                shutil.rmtree(part, ignore_errors=True)
                return jsonify({"ok": False, "error": "解压失败"})
        except Exception as e:
            shutil.rmtree(part, ignore_errors=True)
            return jsonify({"ok": False, "error": str(e)})

        os.makedirs(dest, exist_ok=True)
        for root, _dirs, files in os.walk(part):
            rel = os.path.relpath(root, part)
            target = dest if rel == "." else os.path.join(dest, rel)
            try:
                os.makedirs(target, exist_ok=True)
            except OSError:
                continue
            for fn in files:
                try:
                    os.replace(os.path.join(root, fn), os.path.join(target, fn))
                except OSError:
                    pass
        shutil.rmtree(part, ignore_errors=True)
        try:
            open(marker, "w").close()
        except OSError:
            pass
    return jsonify({"ok": True, "files": len(entries), "scope": inner_dir or "(整包)"})


@app.route("/api/asset")
def api_asset():
    """模型依赖资源（贴图 / .bin / .mtl），相对模型所在目录解析。
    浏览器不认的格式（tga/bmp/dds）现场转 PNG；贴图缺失返回透明占位。"""
    p = request.args.get("path", "")
    base = request.args.get("base", "")
    rel = request.args.get("rel", "")
    pw = request.args.get("password", "") or load_config().get("password", DEFAULT_PASSWORD)

    rel = rel.replace("\\", "/").strip()
    if rel.startswith("http"):
        rel = rel.split("?")[0].rsplit("/", 1)[-1]
    if rel.startswith("/"):
        rel = rel.lstrip("/")
        if rel.startswith("api/"):
            rel = rel[4:]
    if not rel:
        return Response(BLANK_PNG, mimetype="image/png")

    inner = os.path.normpath(os.path.join(base, rel)).replace("\\", "/")
    if inner.startswith("../") or inner.startswith("/"):
        inner = os.path.basename(rel)

    ext = os.path.splitext(inner)[1].lower()
    data = None
    # 已经整包预解压过：只读本地文件，一次 7z 都不调
    if p and _pf_complete(p):
        data = _prefetch_lookup(p, inner)
        if data is None:
            want = os.path.basename(rel).lower()
            try:
                for f in list_cached(p, pw):
                    if f["name"].lower() == want:
                        data = _prefetch_lookup(p, f["path"])
                        if data is not None:
                            inner = f["path"]
                            ext = os.path.splitext(inner)[1].lower()
                        break
            except Exception:
                pass
        if data is None:
            if ext in IMAGE_EXTS or ext in TEX_EXTRA:
                return Response(WHITE_PNG if ext in TEX_EXTRA else BLANK_PNG, mimetype="image/png")
            abort(404)
    else:
        # 命中批量预解压缓存就直接读文件，省掉一次 7z 调用
        data = _prefetch_lookup(p, inner) if p else None
        for pwd in ([] if data is not None else ([pw] if pw else []) + [None]):
            try:
                data = read_bytes(p, inner, pwd)
                break
            except Exception:
                continue

    # 路径对不上时按文件名兜底（FBX/GLTF 里的贴图路径常与实际目录不一致）
    if data is None:
        want = os.path.basename(rel).lower()
        try:
            for f in list_cached(p, pw):
                if f["name"].lower() == want:
                    data = _prefetch_lookup(p, f["path"])
                    if data is None:
                        data = read_bytes(p, f["path"], pw)
                    inner = f["path"]
                    ext = os.path.splitext(inner)[1].lower()
                    break
        except Exception:
            pass

    if data is None:
        # 贴图类缺失不要 404，否则整个模型可能加载失败
        if ext in IMAGE_EXTS or ext in TEX_EXTRA:
            return Response(WHITE_PNG if ext in TEX_EXTRA else BLANK_PNG, mimetype="image/png")
        abort(404)

    if ext in (".png", ".jpg", ".jpeg", ".webp", ".gif"):
        mime = {".png": "image/png", ".jpg": "image/jpeg", ".jpeg": "image/jpeg",
                ".webp": "image/webp", ".gif": "image/gif"}[ext]
        return Response(data, mimetype=mime)
    if ext in (".tga", ".bmp", ".dds") or ext in TEX_EXTRA:
        # .spa / .sph / .toon 实际常是 BMP/PNG 数据，按内容试着解
        png = to_web_image(data)
        if png:
            return Response(png, mimetype="image/png")
        return Response(WHITE_PNG if ext in TEX_EXTRA else BLANK_PNG, mimetype="image/png")
    return Response(data, mimetype="application/octet-stream")


@app.route("/api/download")
def api_download():
    p = request.args.get("path", "")
    inner = request.args.get("inner", "")
    pw = request.args.get("password", "") or load_config().get("password", DEFAULT_PASSWORD)
    if not os.path.isfile(p):
        abort(404)
    try:
        data = read_bytes(p, inner, pw)
    except Exception:
        try:
            data = read_bytes(p, inner, None)
        except Exception as e:
            return jsonify({"error": str(e)}), 500
    return send_file(io.BytesIO(data), as_attachment=True, download_name=os.path.basename(inner))


# ==================== 路由：PMXEditor ====================

@app.route("/api/open-editor", methods=["POST"])
def api_open_editor():
    body = request.get_json(silent=True) or {}
    p = body.get("path", "")
    inner = body.get("inner", "")
    pw = body.get("password") or load_config().get("password", DEFAULT_PASSWORD)
    if not os.path.isfile(p):
        return jsonify({"error": "文件不存在"}), 404
    if not os.path.isfile(PMX_EDITOR):
        return jsonify({"error": f"未找到 PMXEditor: {PMX_EDITOR}"}), 500

    ensure_dirs()
    key = hashlib.md5(f"{p}|{inner}".encode("utf-8", "replace")).hexdigest()[:16]
    outdir = os.path.join(PMX_DIR, key)
    target = os.path.join(outdir, inner.replace("/", os.sep))

    try:
        if not os.path.isfile(target):
            os.makedirs(outdir, exist_ok=True)
            extract_all(p, pw, outdir)
            if not os.path.isfile(target):
                data = read_bytes(p, inner, pw)
                os.makedirs(os.path.dirname(target), exist_ok=True)
                with open(target, "wb") as f:
                    f.write(data)
        subprocess.Popen([PMX_EDITOR, target], close_fds=True)
        return jsonify({"ok": True, "file": target})
    except Exception as e:
        return jsonify({"error": str(e)}), 500


# ==================== 路由：真实文件操作 ====================

@app.route("/api/fs/reveal", methods=["POST"])
def fs_reveal():
    body = request.get_json(silent=True) or {}
    p = os.path.normpath(body.get("path", ""))
    if os.path.isfile(p):
        subprocess.Popen(["explorer", "/select,", p])
    elif os.path.isdir(p):
        subprocess.Popen(["explorer", p])
    else:
        return jsonify({"error": "路径不存在"}), 404
    return jsonify({"ok": True})


@app.route("/api/fs/open", methods=["POST"])
def fs_open():
    body = request.get_json(silent=True) or {}
    p = os.path.normpath(body.get("path", ""))
    if not os.path.isfile(p):
        return jsonify({"error": "文件不存在"}), 404
    os.startfile(p)
    return jsonify({"ok": True})


@app.route("/api/fs/rename", methods=["POST"])
def fs_rename():
    body = request.get_json(silent=True) or {}
    p = os.path.normpath(body.get("path", ""))
    new_name = (body.get("name") or "").strip()
    if not os.path.isfile(p):
        return jsonify({"error": "文件不存在"}), 404
    if not is_under_roots(p):
        return jsonify({"error": "只允许操作监控目录内的文件"}), 403
    if not new_name or any(c in new_name for c in '\\/:*?"<>|'):
        return jsonify({"error": "文件名不合法"}), 400
    if not os.path.splitext(new_name)[1]:
        new_name += os.path.splitext(p)[1]
    target = os.path.join(os.path.dirname(p), new_name)
    if os.path.exists(target):
        return jsonify({"error": "同名文件已存在"}), 400
    try:
        os.rename(p, target)
        return jsonify({"ok": True, "path": target.replace("\\", "/")})
    except Exception as e:
        return jsonify({"error": str(e)}), 500


@app.route("/api/fs/mkdir", methods=["POST"])
def fs_mkdir():
    body = request.get_json(silent=True) or {}
    parent = os.path.normpath(body.get("parent", ""))
    name = (body.get("name") or "").strip()
    if not os.path.isdir(parent):
        return jsonify({"error": "父目录不存在"}), 404
    if not is_under_roots(parent):
        return jsonify({"error": "只允许在监控目录内新建"}), 403
    if not name or any(c in name for c in '\\/:*?"<>|'):
        return jsonify({"error": "文件夹名不合法"}), 400
    target = os.path.join(parent, name)
    if os.path.exists(target):
        return jsonify({"error": "同名文件夹已存在"}), 400
    try:
        os.makedirs(target)
        return jsonify({"ok": True, "path": target.replace("\\", "/")})
    except Exception as e:
        return jsonify({"error": str(e)}), 500


@app.route("/api/fs/move", methods=["POST"])
def fs_move():
    """把压缩包 / 文件夹移动到另一个目录（拖拽和右键「移动到…」都走这里）。
    目标已有同名项时先返回 conflict，由前端确认后再带 overwrite=true 重试。"""
    body = request.get_json(silent=True) or {}
    src = os.path.normpath(body.get("src", ""))
    dst_dir = os.path.normpath(body.get("dst_dir", ""))
    overwrite = bool(body.get("overwrite"))
    if not (os.path.isfile(src) or os.path.isdir(src)):
        return jsonify({"error": "源不存在"}), 404
    if not os.path.isdir(dst_dir):
        return jsonify({"error": "目标目录不存在"}), 404
    if not is_under_roots(src) or not is_under_roots(dst_dir):
        return jsonify({"error": "只允许在监控目录内移动"}), 403
    if os.path.abspath(src).lower() == os.path.abspath(dst_dir).lower():
        return jsonify({"error": "已经在这个目录里了"}), 400
    if os.path.isdir(src):
        # 不允许把文件夹移进自己的子目录
        s = os.path.abspath(src).lower().rstrip("\\") + "\\"
        if (os.path.abspath(dst_dir).lower() + "\\").startswith(s):
            return jsonify({"error": "不能移动到它自己的子目录"}), 400
    target = os.path.join(dst_dir, os.path.basename(src))
    if os.path.abspath(target).lower() == os.path.abspath(src).lower():
        return jsonify({"error": "已经在这个目录里了"}), 400
    if os.path.exists(target):
        if not overwrite:
            return jsonify({"conflict": True, "name": os.path.basename(src)}), 200
        try:
            if os.path.isdir(target):
                shutil.rmtree(target)
            else:
                os.remove(target)
        except Exception as e:
            return jsonify({"error": "覆盖失败：" + str(e)}), 500
    try:
        shutil.move(src, target)
    except Exception as e:
        return jsonify({"error": "移动失败：" + str(e)}), 500
    with _list_lock:
        _list_cache.clear()
    cfg = load_config()
    return jsonify({"ok": True, "path": target.replace("\\", "/"),
                    "meta": build_meta(cfg["watch_dirs"])})


@app.route("/api/fs/trash", methods=["POST"])
def fs_trash():
    """删除压缩包 → 移到本工具回收站（可手动还原），不进系统回收站"""
    body = request.get_json(silent=True) or {}
    p = os.path.normpath(body.get("path", ""))
    if not os.path.isfile(p):
        return jsonify({"error": "文件不存在"}), 404
    if not is_under_roots(p):
        return jsonify({"error": "只允许操作监控目录内的文件"}), 403
    ensure_dirs()
    stamp = time.strftime("%Y%m%d_%H%M%S")
    dst = os.path.join(TRASH_DIR, f"{stamp}__{os.path.basename(p)}")
    n = 1
    while os.path.exists(dst):
        dst = os.path.join(TRASH_DIR, f"{stamp}_{n}__{os.path.basename(p)}")
        n += 1
    try:
        shutil.move(p, dst)
        return jsonify({"ok": True, "trash": dst.replace("\\", "/")})
    except Exception as e:
        return jsonify({"error": str(e)}), 500


@app.route("/api/fs/extract", methods=["POST"])
def fs_extract():
    """把整个压缩包解到指定目录（真实解压，用户明确要求才做）"""
    body = request.get_json(silent=True) or {}
    p = body.get("path", "")
    pw = body.get("password") or load_config().get("password", DEFAULT_PASSWORD)
    target = body.get("target") or ""
    if not os.path.isfile(p):
        return jsonify({"error": "文件不存在"}), 404
    if not target:
        stem = os.path.splitext(os.path.basename(p))[0]
        target = os.path.join(os.path.dirname(p), stem)
    target = os.path.normpath(target)
    try:
        os.makedirs(target, exist_ok=True)
        if not extract_all(p, pw, target):
            return jsonify({"error": "解压失败（密码错误或文件损坏）"}), 500
        return jsonify({"ok": True, "target": target.replace("\\", "/")})
    except Exception as e:
        return jsonify({"error": str(e)}), 500


@app.route("/api/trash/open", methods=["POST"])
def trash_open():
    ensure_dirs()
    subprocess.Popen(["explorer", TRASH_DIR])
    return jsonify({"ok": True})


@app.route("/api/browse", methods=["POST"])
def api_browse():
    """给「添加目录」用的简易目录浏览"""
    body = request.get_json(silent=True) or {}
    path = body.get("path") or ""
    if not path:
        drives = []
        for letter in "CDEFGH":
            d = f"{letter}:\\"
            if os.path.isdir(d):
                drives.append({"name": d, "path": d})
        return jsonify({"path": "", "dirs": drives, "parent": None})
    path = os.path.normpath(path)
    if not os.path.isdir(path):
        return jsonify({"error": "目录不存在"}), 404
    dirs = []
    exes = []
    try:
        for name in sorted(os.listdir(path), key=str.lower):
            full = os.path.join(path, name)
            if os.path.isdir(full):
                dirs.append({"name": name, "path": full.replace("\\", "/")})
            elif name.lower().endswith((".exe", ".bat", ".cmd")):
                exes.append({"name": name, "path": full.replace("\\", "/")})
    except PermissionError:
        return jsonify({"error": "没有访问权限"}), 403
    parent = os.path.dirname(path)
    return jsonify({"path": path.replace("\\", "/"), "dirs": dirs, "exes": exes,
                    "parent": (parent.replace("\\", "/") if parent != path else None)})


# ==================== 前端页面 ====================

def _ui_asset(name):
    """页面用到的图标：打包后在 _MEIPASS，源码运行时在 app.py 旁边"""
    for d in (RES_DIR, BASE_DIR):
        p = os.path.join(d, name)
        if os.path.isfile(p):
            return p
    return ""


@app.route("/favicon.ico")
def favicon():
    p = _ui_asset("app.ico")
    if not p:
        return Response(status=404)
    return send_file(p, mimetype="image/x-icon", max_age=86400)


@app.route("/icon.png")
def icon_png():
    p = _ui_asset("app_icon.png")
    if not p:
        return Response(status=404)
    return send_file(p, mimetype="image/png", max_age=86400)


PAGE_HTML = r"""<!DOCTYPE html>
<html lang="zh-CN">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Zip2mmd</title>
<link rel="icon" type="image/png" href="/icon.png">
<link rel="shortcut icon" type="image/x-icon" href="/favicon.ico">
<style>
:root{
  --bg:#fafafb; --panel:#fff; --line:#ededf1; --line2:#e2e2e8;
  --text:#17171c; --text2:#65656f; --text3:#9c9ca6;
  --accent:#3b6ef5; --accent-soft:#eef3ff;
  --green:#1f9d63; --red:#dc4c4c; --purple:#7c5cf0;
  --side-w:250px; --view-w:440px;
}
*{box-sizing:border-box;margin:0;padding:0}
html,body{height:100%}
body{font-family:-apple-system,BlinkMacSystemFont,"Segoe UI","PingFang SC","Microsoft YaHei",sans-serif;
  font-size:14px;color:var(--text);background:var(--bg);display:flex;overflow:hidden;-webkit-font-smoothing:antialiased}
::-webkit-scrollbar{width:9px;height:9px}
::-webkit-scrollbar-thumb{background:#d8d8de;border-radius:9px;border:2px solid transparent;background-clip:content-box}
::-webkit-scrollbar-track{background:transparent}
button,input,select{font-family:inherit}

#sidebar{width:var(--side-w);flex:0 0 var(--side-w);height:100vh;overflow-y:auto;overflow-x:hidden;
  background:#fff;border-right:1px solid var(--line);padding:14px 12px 40px}
.brand{display:flex;align-items:center;gap:8px;padding:2px 6px 14px;cursor:default;user-select:none}
.brand .dot{width:22px;height:22px;border-radius:7px;background:linear-gradient(135deg,#3b6ef5,#7c5cf0);flex:none}
.brand .logo{width:24px;height:24px;border-radius:7px;flex:none;display:block}
.brand h1{font-size:14px;font-weight:650;letter-spacing:.2px;white-space:nowrap}
.srow{display:flex;gap:6px;align-items:center;margin-bottom:8px}
.srow .grow{flex:1;min-width:0}
.sinput{width:100%;height:34px;border:1px solid var(--line2);border-radius:8px;padding:0 10px;
  font-size:13px;background:#fff;outline:none;color:var(--text)}
.sinput:focus{border-color:var(--accent);box-shadow:0 0 0 3px rgba(59,110,245,.1)}
.entry{display:flex;align-items:center;gap:8px;padding:8px 10px;border-radius:9px;cursor:pointer;
  font-size:13.5px;color:#2e2e36;user-select:none;white-space:nowrap;overflow:hidden}
.entry:hover{background:#f5f5f8}
.entry.on{background:var(--accent-soft);color:var(--accent);font-weight:600}
.entry .n{margin-left:auto;font-size:11px;color:var(--text3);font-weight:400;flex:none}
.entry.on .n{color:var(--accent)}
.entry .t{overflow:hidden;text-overflow:ellipsis}
.entry .chev{width:12px;flex:none;font-size:9px;color:var(--text3);transition:transform .15s}
.entry.folded .chev{transform:rotate(-90deg)}
.entry.sub{padding-left:26px;font-size:12.8px;color:#4a4a54}
.entry.sub .ico{font-size:12px;opacity:.75}
.divider{height:1px;background:var(--line);margin:10px 4px}
.slabel{font-size:11px;font-weight:600;color:var(--text3);letter-spacing:.5px;padding:0 8px;margin:12px 0 6px}
.sitem{display:flex;align-items:center;gap:8px;padding:9px 10px;border-radius:9px;cursor:pointer;font-size:13.5px;color:#2e2e36}
.sitem:hover{background:#f5f5f8}
.statline{font-size:11px;color:var(--text3);padding:10px 8px 0;line-height:1.8}

#center{flex:1;min-width:0;display:flex;flex-direction:column;height:100vh}
.toolbar{height:52px;flex:none;background:#fff;border-bottom:1px solid var(--line);
  display:flex;align-items:center;gap:8px;padding:0 16px;overflow-x:auto}
.toolbar2{height:42px;gap:6px;background:#fcfcfe}
.toolbar2 .hint{color:var(--text3);font-size:11.5px}
.toolbar .sep{width:1px;height:20px;background:var(--line2);flex:none}
.tinput{height:30px;border:1px solid var(--line2);border-radius:7px;padding:0 9px;font-size:12.5px;width:120px;outline:none}
.tinput:focus{border-color:var(--accent)}
.fbtn{flex:none;font-size:12px;padding:5px 10px;border-radius:7px;border:1px solid var(--line2);
  background:#fff;color:#4a4a54;cursor:pointer;white-space:nowrap}
.fbtn:hover{background:#f5f5f8}
.fbtn.on{background:var(--accent);border-color:var(--accent);color:#fff}
.fbtn.solid{background:var(--accent);border-color:var(--accent);color:#fff}
.fbtn.solid:hover{background:#2f5cd8}
.crumb{display:flex;align-items:center;gap:6px;font-size:12.5px;color:var(--text2);min-width:0}
.crumb b{font-weight:600;color:var(--text);overflow:hidden;text-overflow:ellipsis;white-space:nowrap;max-width:340px}
.crumb .back{cursor:pointer;color:var(--accent);flex:none}
#content{flex:1;overflow-y:auto;padding:16px}

.grid{display:grid;grid-template-columns:repeat(auto-fill,minmax(150px,1fr));gap:12px}
.card{background:#fff;border:1px solid var(--line);border-radius:10px;overflow:hidden;cursor:pointer;transition:.14s;position:relative}
.card:hover{border-color:#c7cdff;box-shadow:0 4px 14px rgba(59,110,245,.12);transform:translateY(-1px)}
.card.dragging{opacity:.4}
.card.sel{outline:2px solid var(--accent);outline-offset:-2px;background:#f3f7ff}
.srow{position:relative}
.fpanel{position:absolute;left:calc(100% + 6px);top:0;width:198px;background:#fff;border:1px solid var(--line);
  border-radius:10px;box-shadow:0 10px 30px rgba(0,0,0,.14);padding:10px;z-index:90;
  display:flex;flex-direction:column;gap:9px}
.fpanel.hide{display:none}
.fpanel .flabel{font-size:11px;color:var(--text3);margin-bottom:4px}
.fpanel .fgroup{display:flex;gap:5px;flex-wrap:wrap}
.batchbar{display:flex;align-items:center;gap:6px;padding:6px 10px;margin:8px 0;
  background:#eef3ff;border:1px solid #d9e2ff;border-radius:9px;min-height:34px;box-sizing:border-box}
.batchbar.hide{display:none}
.batchbar .bcount{font-size:12px;color:var(--accent);font-weight:600;margin-right:4px}
.entry.drop{background:#e8f0ff;box-shadow:inset 0 0 0 2px var(--accent);border-radius:6px}
.card .box{height:104px;background:#f3f4f8;display:flex;align-items:center;justify-content:center;overflow:hidden;position:relative}
.card .box img{width:100%;height:100%;object-fit:cover;display:block}
.card .box .ph{font-size:30px;opacity:.5}
.card .box .ext{font-size:11.5px;letter-spacing:.8px;color:#9aa0b4;font-weight:650}
.card .info{padding:7px 9px}
.card .fn{font-size:11.8px;line-height:1.32;word-break:break-all;display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical;overflow:hidden}
.card .fs{font-size:10.5px;color:var(--text3);margin-top:3px;display:flex;gap:5px;align-items:center;flex-wrap:wrap}
.tag{background:#eef0f6;color:#6b7280;padding:1px 5px;border-radius:4px;font-size:9.5px;font-weight:600}
.tag.sfx{background:#fff1e6;color:#c2410c}
.tag.enc{background:#fff8e6;color:#a16207}
.rows .card{display:flex;align-items:center;border-radius:8px;margin-bottom:5px}
.rows .card .box{width:42px;height:42px;flex:none;border-radius:6px;margin:6px 0 6px 8px}
.rows .card .box .ph{font-size:17px}
.rows .card .info{flex:1;padding:6px 10px;display:flex;align-items:center;gap:10px;min-width:0}
.rows .card .fn{-webkit-line-clamp:1;flex:1}
.rows .card .fs{margin:0;white-space:nowrap;flex:none}
/* ---------- 压缩包封面 ---------- */
.card .box .cover{position:absolute;inset:0;width:100%;height:100%;object-fit:contain;display:block;
  background:#f3f4f8;z-index:1}
.card .box .cover.hide{display:none}
.card .box .ext{z-index:0}
.arcard{background:#fff;border:1px solid var(--line);border-radius:10px;overflow:hidden;cursor:pointer;
  transition:.14s;display:flex;flex-direction:column;position:relative}
.arcard:hover{border-color:#c7cdff;box-shadow:0 4px 14px rgba(59,110,245,.12);transform:translateY(-1px)}
.arcard.on{border-color:var(--accent);box-shadow:0 0 0 2px var(--accent-soft)}
.arcard .abox{height:118px;background:#f3f4f8;position:relative;display:flex;align-items:center;justify-content:center;overflow:hidden}
.arcard .abox img{position:absolute;inset:0;width:100%;height:100%;object-fit:contain;z-index:1;background:#f3f4f8}
.arcard .ainfo{padding:8px 9px;min-height:52px}
.arcard .an2{font-size:11.6px;line-height:1.32;word-break:break-all;display:-webkit-box;
  -webkit-line-clamp:2;-webkit-box-orient:vertical;overflow:hidden;color:#2e2e36}
.arcard.on .an2{color:var(--accent);font-weight:600}
.arcard .am2{font-size:10.3px;color:var(--text3);margin-top:5px;display:flex;gap:5px;align-items:center;flex-wrap:wrap}
.arclist.cards{display:grid;grid-template-columns:repeat(auto-fill,minmax(140px,1fr));gap:10px;
  align-content:start;padding:12px;width:320px;flex:0 0 320px;border-right:1px solid var(--line);
  overflow-y:auto;background:#fafbff}

/* ---------- 左右铺开：两个原视口并排 ---------- */
#content.split{display:flex;gap:0}
.split-pane{flex:1;min-width:0;overflow-y:auto;padding:16px}
#paneLeft{flex:0 0 46%;border-right:0;background:#fafbff}
#paneRight{background:#fff}
.split-pane .card.on{border-color:var(--accent);box-shadow:0 0 0 2px var(--accent-soft)}
.split-drag{width:6px;flex:0 0 6px;cursor:col-resize;background:transparent;position:relative;z-index:5}
.split-drag::after{content:"";position:absolute;top:0;bottom:0;left:2px;width:2px;background:var(--line)}
.split-drag:hover::after{background:var(--accent)}
#paneLeft > .dirbar:first-child{margin-top:0}
#paneRight .panehd{display:flex;align-items:center;gap:8px;font-size:12.5px;font-weight:650;
  color:var(--text2);padding:0 0 10px;margin-bottom:12px;border-bottom:1px solid var(--line);
  position:sticky;top:-16px;background:#fff;z-index:2}

/* ---------- 可拖拽分隔条 ---------- */
.vsplit{width:5px;flex:0 0 5px;cursor:col-resize;background:transparent;position:relative;z-index:70}
.vsplit::after{content:"";position:absolute;top:0;bottom:0;left:2px;width:1px;background:var(--line)}
.vsplit:hover::after,.vsplit.drag::after{background:var(--accent);width:2px;left:1px}
body.side-collapsed .vsplit.side,body.view-collapsed .vsplit.view{display:none}
body.resizing{cursor:col-resize!important;user-select:none}
body.resizing *{cursor:col-resize!important}

/* ---------- 设置 / 密码对话框 ---------- */
.fld{margin-bottom:14px}
.fld label{display:block;font-size:12px;font-weight:600;color:var(--text2);margin-bottom:6px}
.fld textarea,.fld input[type=text],.fld input[type=password]{
  width:100%;border:1px solid var(--line2);border-radius:8px;padding:8px 10px;font-size:12.5px;
  color:var(--text);outline:none;font-family:inherit;resize:vertical}
.fld textarea:focus,.fld input:focus{border-color:var(--accent);box-shadow:0 0 0 3px rgba(59,110,245,.1)}
.pwchips{display:flex;gap:6px;flex-wrap:wrap;margin:2px 0 6px}
.pwchips .fbtn{letter-spacing:1px}
.pwderr{color:var(--red);font-size:12px;margin-top:8px;min-height:16px}
.empty{text-align:center;color:var(--text3);padding:64px 20px;font-size:13.5px;line-height:2}
.spin{width:24px;height:24px;border:3px solid #e6e8ef;border-top-color:var(--accent);border-radius:50%;
  animation:sp .7s linear infinite;margin:0 auto 12px}
@keyframes sp{to{transform:rotate(360deg)}}
.err{background:#fff4f4;border:1px solid #ffd5d5;color:#c62828;padding:10px 13px;border-radius:9px;font-size:12.5px;margin-bottom:12px;word-break:break-all}
.dirbar{font-size:11.5px;color:var(--text3);margin:14px 0 8px;padding-bottom:5px;border-bottom:1px dashed var(--line);word-break:break-all}
.dirbar:first-child{margin-top:0}

/* ---------- 按类型分栏 ---------- */
.sec{margin-bottom:20px}
.sechead{display:flex;align-items:center;gap:8px;padding:8px 10px;margin-bottom:10px;
  background:#fff;border:1px solid var(--line);border-radius:9px;cursor:pointer;user-select:none}
.sechead:hover{border-color:#c7cdff}
.sechead .chev{width:12px;font-size:10px;color:var(--text3);flex:none}
.sechead .sico{font-size:16px;flex:none}
.sechead .sname{font-size:13px;font-weight:650;color:#2e2e36;white-space:nowrap}
.sechead .scount{font-size:11px;color:var(--accent);background:var(--accent-soft);
  padding:1px 7px;border-radius:9px;font-weight:600;flex:none}
.sechead .sline{flex:1;height:1px;background:var(--line)}
.sechead .sonly{font-size:11px;padding:3px 9px;border-radius:6px;border:1px solid var(--line2);
  background:#fff;color:var(--text2);cursor:pointer;white-space:nowrap;flex:none}
.sechead .sonly:hover{border-color:var(--accent);color:var(--accent)}
.sechead .sonly.on{background:var(--accent);border-color:var(--accent);color:#fff}
.secbody.fold{display:none}
.secbody > .empty{padding:26px 20px}
.secbody .dirbar{font-size:11px;margin:10px 0 7px}

/* ---------- 左右铺开：压缩包列表 | 包内内容 ---------- */
#content.split{display:flex;padding:0;overflow:hidden}
.arclist{width:252px;flex:0 0 252px;border-right:1px solid var(--line);overflow-y:auto;padding:10px 8px;background:#fafbff}
.arcrow{padding:9px 10px;border-radius:9px;cursor:pointer;margin-bottom:4px;border:1px solid transparent}
.arcrow:hover{background:#eef1fb}
.arcrow.on{background:var(--accent-soft);border-color:#cfdcff}
.arcrow .an{font-size:12.8px;color:#2e2e36;line-height:1.4;word-break:break-all;
  display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical;overflow:hidden}
.arcrow.on .an{color:var(--accent);font-weight:600}
.arcrow .am{display:flex;align-items:center;gap:6px;margin-top:5px;font-size:10.5px;color:var(--text3);flex-wrap:wrap}
.arcrow .am .tag{font-size:10px;padding:0 5px;border-radius:4px;background:#eef0f6;color:#5a5a64}
.arcrow .am .tag.enc{background:#fdeaea;color:var(--red)}
.arcfiles{flex:1;overflow-y:auto;padding:16px;min-width:0}
.arcfiles .arcsec{margin-bottom:16px}

/* ---------- 两侧可收缩贴边按钮 ---------- */
.edge-tab{position:fixed;top:50%;transform:translateY(-50%);z-index:60;
  width:15px;height:66px;display:flex;align-items:center;justify-content:center;
  background:#fff;border:1px solid var(--line2);cursor:pointer;color:var(--text2);
  font-size:12px;user-select:none;transition:background .15s}
.edge-tab:hover{background:#eef1fb;color:var(--accent)}
#sideTab{left:var(--side-w);border-left:0;border-radius:0 8px 8px 0;box-shadow:2px 0 7px rgba(0,0,0,.05)}
#viewTab{right:var(--view-w);border-right:0;border-radius:8px 0 0 8px;box-shadow:-2px 0 7px rgba(0,0,0,.05)}
body.side-collapsed #sideTab{left:0}
body.view-collapsed #viewTab{right:0}
#sidebar.hide{width:0;flex:0 0 0;padding:0;border:0;overflow:hidden}

#viewer{width:var(--view-w);flex:0 0 var(--view-w);height:100vh;background:#fff;border-left:1px solid var(--line);
  display:flex;flex-direction:column}
#viewer.hide{display:none}
.vhead{height:52px;flex:none;display:flex;align-items:center;gap:8px;padding:0 12px;border-bottom:1px solid var(--line)}
.vhead .vt{font-size:12.5px;font-weight:600;overflow:hidden;text-overflow:ellipsis;white-space:nowrap;flex:1}
.vhead .ic{height:26px;min-width:26px;padding:0 7px;border-radius:7px;border:1px solid var(--line2);background:#fff;
  display:flex;align-items:center;justify-content:center;cursor:pointer;font-size:11px;color:var(--text2);flex:none}
.vhead .ic:hover{background:#f5f5f8}
#canvasWrap{flex:1;position:relative;background:linear-gradient(180deg,#f7f8fc,#eef0f6);overflow:hidden;min-height:200px}
#c3d{display:block;width:100%;height:100%}
.vhint{position:absolute;inset:0;display:flex;flex-direction:column;align-items:center;justify-content:center;
  color:var(--text3);font-size:12.5px;gap:10px;text-align:center;padding:20px;pointer-events:none}
.vhint .big{font-size:38px;opacity:.35}
.vhint.hide{display:none}
.vhint .sub{font-size:11px;line-height:1.8;max-width:260px}
.mtip{position:absolute;right:10px;bottom:10px;background:rgba(255,255,255,.86);border:1px solid var(--line);
  border-radius:7px;padding:4px 9px;font-size:10.5px;color:var(--text2);pointer-events:none;
  box-shadow:0 1px 4px rgba(0,0,0,.04)}
.vbadge{position:absolute;left:10px;top:10px;background:rgba(255,255,255,.92);border:1px solid var(--line);
  border-radius:7px;padding:4px 8px;font-size:10.5px;color:var(--text2);display:none}
.vbadge.show{display:block}
.shotguide{position:absolute;inset:8px;border:2px dashed rgba(59,110,245,.9);border-radius:6px;
  background:rgba(59,110,245,.05);display:flex;align-items:flex-end;justify-content:center;
  padding-bottom:12px;z-index:60;pointer-events:none}
.shotguide.hide{display:none}
.shotbar{pointer-events:auto;display:flex;align-items:center;gap:8px;background:rgba(255,255,255,.96);
  border:1px solid var(--line);border-radius:9px;padding:6px 9px;box-shadow:0 6px 20px rgba(0,0,0,.14)}
.shotbar .shotip{font-size:11.5px;color:var(--text3)}
.vfoot{flex:none;border-top:1px solid var(--line);padding:10px 12px;max-height:38vh;overflow-y:auto}
.vrow{display:flex;gap:6px;flex-wrap:wrap;margin-bottom:8px}
.lightrow{display:flex;align-items:center;gap:8px;margin-bottom:9px;font-size:11.5px;color:var(--text3)}
.lightrow label{width:32px;flex:none}
.lightrow input[type=range]{flex:1;min-width:80px;accent-color:var(--accent);height:4px}
.lightrow select{height:26px;border:1px solid var(--line2);border-radius:6px;padding:0 6px;font-size:11.5px;color:var(--text);background:#fff;outline:none}
.lightrow span{width:38px;text-align:right;flex:none}
.lightrow .chk{display:flex;align-items:center;gap:4px;width:auto;flex:none;cursor:pointer;user-select:none;white-space:nowrap}
.lightrow .chk input{width:13px;height:13px;margin:0;accent-color:var(--accent);cursor:pointer}
.vkv{display:grid;grid-template-columns:70px 1fr;gap:5px 8px;font-size:11.5px}
.vkv .k{color:var(--text3)}
.vkv .v{word-break:break-all;color:#2e2e36}
.vlabel{font-size:11px;color:var(--text3);font-weight:600;margin:10px 0 6px;letter-spacing:.4px}
.tgrid{display:grid;grid-template-columns:repeat(auto-fill,minmax(66px,1fr));gap:6px}
.tgrid .t{border:1px solid var(--line);border-radius:6px;overflow:hidden;cursor:pointer;background:#f7f8fc}
.tgrid .t img{width:100%;height:56px;object-fit:cover;display:block}

.mask{position:fixed;inset:0;background:rgba(12,14,22,.5);display:none;align-items:center;justify-content:center;z-index:200}
.mask.on{display:flex}
.dlg{background:#fff;border-radius:13px;width:min(520px,92vw);max-height:84vh;display:flex;flex-direction:column;overflow:hidden;box-shadow:0 20px 60px rgba(0,0,0,.28)}
.dlg h3{font-size:14.5px;padding:15px 18px;border-bottom:1px solid var(--line);display:flex;align-items:center;gap:8px}
.dlg .body{padding:14px 18px;overflow-y:auto}
.dlg .foot{padding:12px 18px;border-top:1px solid var(--line);display:flex;gap:8px;justify-content:flex-end}
.dlg .body input{width:100%;height:34px;border:1px solid var(--line2);border-radius:8px;padding:0 10px;font-size:13px;outline:none;margin-bottom:10px}
.dlg .body input:focus{border-color:var(--accent)}
.rootrow{display:flex;gap:6px;margin-bottom:7px;align-items:center}
.rootrow input{flex:1;margin:0}
.rootrow select{height:32px;border:1px solid var(--line2);border-radius:7px;padding:0 6px;font-size:12.5px;background:#fff;color:var(--text);outline:none}
.setwrap{display:flex;gap:14px;min-height:300px}
.setnav{width:104px;flex:none;display:flex;flex-direction:column;gap:4px}
.settab{text-align:left;padding:7px 10px;border-radius:7px;border:1px solid transparent;background:none;
  font-size:12.5px;color:var(--text2);cursor:pointer;font-family:inherit}
.settab:hover{background:#f5f5f8}
.settab.on{background:#eef3ff;color:var(--accent);border-color:#d9e2ff;font-weight:600}
.setbody{flex:1;min-width:0}
.setbody label{display:block;font-size:12px;color:var(--text3);margin:0 0 6px}
.setsec.hide{display:none}
.setbody input{width:100%;height:34px;border:1px solid var(--line2);border-radius:8px;
  padding:0 10px;font-size:13px;outline:none;margin-bottom:8px}
/* 行内控件统一高度、基线对齐（input / select / 按钮以前各是 34 / 32 / 26，看着是错位的） */
.setbody .rootrow{align-items:center}
.setbody .rootrow input,
.setbody .rootrow select,
.setbody .rootrow .fbtn{height:32px;box-sizing:border-box;margin:0;line-height:1}
.setbody .rootrow input{flex:1;min-width:0;width:auto;padding:0 9px;font-size:12.5px}
.setbody .rootrow select{padding:0 8px;font-size:12.5px}
.setbody .rootrow .fbtn{display:inline-flex;align-items:center;justify-content:center;padding:0 11px}
.dlist{border:1px solid var(--line);border-radius:8px;max-height:240px;overflow-y:auto;margin-bottom:10px}
.ditem{padding:7px 11px;font-size:12.5px;cursor:pointer;display:flex;gap:7px;align-items:center}
.ditem:hover{background:#f5f5f8}
.ditem.pktree{display:flex;align-items:center;gap:6px;cursor:pointer}
.ditem.pktree .chev{width:12px;flex:none;color:var(--text3);font-size:10px}
.ditem.pktree .pknm{flex:1;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.ditem.pktree .pkct{color:#9c9ca6;font-size:11px;flex:none}
.ditem.pktree.on{background:#eef3ff;color:var(--accent);font-weight:600}
.note{font-size:11.5px;color:var(--text3);line-height:1.8}

.ctx{position:fixed;background:#fff;border:1px solid var(--line2);border-radius:9px;box-shadow:0 8px 28px rgba(0,0,0,.16);
  padding:5px;display:none;z-index:300;min-width:172px}
.ctx.on{display:block}
.ctx .it{padding:7px 10px;font-size:12.5px;border-radius:6px;cursor:pointer;display:flex;gap:8px;align-items:center;white-space:nowrap}
.ctx .it:hover{background:var(--accent-soft);color:var(--accent)}
.ctx .it.danger:hover{background:#ffefef;color:var(--red)}
.ctx .hr{height:1px;background:var(--line);margin:4px 2px}

.lb{position:fixed;inset:0;background:rgba(12,14,22,.92);z-index:400;display:none;align-items:center;justify-content:center;flex-direction:column;gap:10px}
.lb.on{display:flex}
.lb img{max-width:92vw;max-height:84vh;border-radius:6px;object-fit:contain}
.lb .cap{color:#cfd3e0;font-size:12px;max-width:80vw;text-align:center;word-break:break-all}
.lb .x{position:absolute;top:14px;right:20px;color:#fff;font-size:28px;cursor:pointer;opacity:.8}
.lb .nav{position:absolute;top:50%;transform:translateY(-50%);color:#fff;font-size:34px;cursor:pointer;padding:8px 14px;opacity:.5;user-select:none}
.lb .nav:hover{opacity:1}
.lb .prev{left:8px}.lb .next{right:8px}
</style>
</head>
<body>

<aside id="sidebar">
  <div class="brand" id="brandBtn" title="点一下刷新（外部改动了文件夹后用它重新扫描）"><img class="logo" src="/icon.png" alt=""><h1>Zip2mmd</h1></div>
  <div class="srow"><input class="sinput grow" id="q" placeholder="搜索压缩包…" autocomplete="off">
    <button class="fbtn" id="filterBtn" title="筛选">筛选</button></div>
  <div class="fpanel hide" id="filterPanel">
    <div class="fgroup"><div class="flabel">加密</div>
      <button class="fbtn on" data-fenc="all">全部</button>
      <button class="fbtn" data-fenc="enc">已加密</button>
      <button class="fbtn" data-fenc="plain">未加密</button>
    </div>
    <div class="fgroup"><div class="flabel">预览图</div>
      <button class="fbtn on" data-fcov="all">全部</button>
      <button class="fbtn" data-fcov="has">有</button>
      <button class="fbtn" data-fcov="none">无</button>
    </div>
  </div>
  <div id="nav"></div>
  <div class="divider"></div>
  <div class="sitem" id="trashBtn">工具回收站</div>
  <div class="sitem" id="settingsBtn">设置</div>
  <div class="statline" id="statline"></div>
</aside>
<div class="vsplit side" id="splitSide" title="拖动调整左侧栏宽度"></div>
<div class="edge-tab" id="sideTab" title="收起 / 展开左侧栏">‹</div>

<section id="center">
  <div class="toolbar">
    <div class="crumb" id="crumb"></div>
    <span style="flex:1"></span>
    <button class="fbtn" id="foldAll">折叠全部</button>
    <button class="fbtn" id="cmodeBtn" title="切换：堆叠分栏 / 左右铺开">左右铺开</button>
    <button class="fbtn" id="viewBtn">列表</button>
    <button class="fbtn on" id="toggleViewer">视口</button>
  </div>
  <div class="toolbar toolbar2" id="filterBar">
    <span class="hint" style="flex:none">分栏</span>
    <button class="fbtn on" data-filter="all">全部</button>
    <button class="fbtn" data-filter="model">模型</button>
    <button class="fbtn" data-filter="image">图片</button>
    <button class="fbtn" data-filter="texture">贴图</button>
    <button class="fbtn" data-filter="archive">压缩包</button>
    <button class="fbtn" data-filter="motion">动作</button>
    <button class="fbtn" data-filter="doc">文档</button>
    <button class="fbtn" data-filter="other">其他</button>
    <span class="hint" id="secSummary" style="margin-left:4px"></span>
  </div>
  <div class="batchbar hide" id="batchBar">
    <span class="bcount" id="batchCount">已选 0</span>
    <button class="fbtn" data-b="all">全选</button>
    <button class="fbtn" data-b="inv">反选</button>
    <button class="fbtn" data-b="none">清空</button>
    <span style="flex:1"></span>
    <button class="fbtn solid" data-b="move">移动至…</button>
    <button class="fbtn" data-b="cover">生成预览图</button>
    <button class="fbtn" data-b="delcover">删除预览图</button>
    <button class="fbtn" data-b="exit">退出批量</button>
  </div>
  <div id="content"><div class="empty">从左侧选一个分组或压缩包</div></div>
</section>
<div class="vsplit view" id="splitView" title="拖动调整预览栏宽度"></div>

<section id="viewer">
  <div class="vhead">
    <span class="ic" id="vClose" title="收起视口">✕</span>
    <span class="vt" id="vTitle">3D 视口</span>
    <span class="ic" id="vShot" title="截图">截图</span>
  </div>
  <div id="canvasWrap">
    <canvas id="c3d"></canvas>
    <div class="vhint" id="vHint">
      <div class="big">3D</div>
      <div>点一个模型文件即可预览</div>
      <div class="sub">支持 PMX / PMD / GLB / GLTF / FBX / OBJ<br>左键旋转 · 滚轮缩放 · 右键平移</div>
    </div>
    <div class="mtip" id="mouseTip">左键旋转 · 右键平移</div>
    <div class="vbadge" id="vBadge"></div>
    <div class="shotguide hide" id="shotGuide">
      <div class="shotbar">
        <span class="shotip">虚线内就是截图范围</span>
        <button class="fbtn solid" id="shotOk">确认截图</button>
        <button class="fbtn" id="shotNo">取消</button>
      </div>
    </div>
  </div>
  <div class="vfoot" id="vFoot"></div>
</section>
<div class="edge-tab" id="viewTab" title="收起 / 展开预览栏">›</div>

<div class="mask" id="mask"><div class="dlg" id="dlg"></div></div>
<div class="ctx" id="ctx"></div>
<div class="lb" id="lb">
  <span class="x" id="lbX">×</span>
  <span class="nav prev" id="lbPrev">‹</span>
  <img id="lbImg" src="">
  <div class="cap" id="lbCap"></div>
  <span class="nav next" id="lbNext">›</span>
</div>

<script src="/vendor/three.min.js"></script>
<script src="/vendor/OrbitControls.js"></script>
<script src="/vendor/mmd-parser.min.js"></script>
<script src="/vendor/MMDLoader.js"></script>
<script src="/vendor/GLTFLoader.js"></script>
<script src="/vendor/fflate.min.js"></script>
<script src="/vendor/NURBSUtils.js"></script>
<script src="/vendor/NURBSCurve.js"></script>
<script src="/vendor/FBXLoader.js"></script>
<script src="/vendor/OBJLoader.js"></script>
<script src="/vendor/MTLLoader.js"></script>
<script>
/* ===================== 状态 ===================== */
const S = {
  meta:null, archives:[], files:[], cur:null, curName:'',
  filter:'all', viewMode:'grid', sel:null, pwd:'',
  folded:{}, foldSec:{}, lbList:[], lbIdx:0,
  light:1, autoExpo:true, lightColor:'#ffffff', openers:{}, passwords:[], tools:{}, faceTex:'',
  contentMode:'stack', activeCat:'model', mouseMode:'default', rightRotate:false,
  coverNames:['ZipPreview.png'], coverFolder:'ZipPreview', coverVer:0,
  pwTried:false
};
const $ = s => document.querySelector(s);
const $$ = s => [...document.querySelectorAll(s)];
const esc = s => String(s).replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;').replace(/"/g,'&quot;');
const enc = encodeURIComponent;
const coverURL = p => `/api/cover?path=${enc(p)}&password=${enc(S.pwd)}&v=${S.coverVer}`;
const coverBox = p => `<img class="cover" loading="lazy" src="${coverURL(p)}" onerror="this.classList.add('hide')">`;
const IMG = new Set(['.png','.jpg','.jpeg','.webp','.bmp','.gif','.tga','.dds']);
const M3D = new Set(['.pmx','.pmd','.glb','.gltf','.fbx','.obj']);

/* 真正的脚本异常才提示；模型加载失败/空文件走 onErr 和 loadModel 里的专门提示，
   不要都显示成「脚本出错」 */
window.addEventListener('error', ev=>{
  const msg = String(ev.message || (ev.error && ev.error.message) || '');
  if(!msg || /Load failed|Failed to fetch|NetworkError/i.test(msg)) return;
  try{ setHint('脚本出错', msg); }catch(e){}
});

/* ===================== 侧栏 ===================== */
async function loadMeta(){
  const r = await fetch('/api/meta');
  S.meta = await r.json();
  S.archives = S.meta.archives || [];
  // 密码不再常驻工具栏：只在真正需要时弹窗询问
  try{
    const st = await (await fetch('/api/settings')).json();
    S.coverNames = st.cover_names || ['ZipPreview.png'];
    S.coverFolder = st.cover_folder || 'ZipPreview';
    S.openers = st.openers || {};
    S.passwords = st.passwords || [];
    S.tools = {seven_zip: st.seven_zip || '', unrar: st.unrar || '',
               text_editor: st.text_editor || ''};
  }catch(e){}
  try{ S.rightRotate = localStorage.getItem('zipview.rightRotate') === '1'; }catch(e){}
  try{ S.autoExpo = localStorage.getItem('zipview.autoExpo') !== '0'; }catch(e){}
  try{ S.lightColor = localStorage.getItem('zipview.lightColor') || '#ffffff'; }catch(e){}
  renderStat();
  if(S.meta.encKnown < S.meta.total) setTimeout(pollEncryption, 300);
}

/* 加密探测在后台跑，结果陆续补上，不阻塞首屏 */
let _encPoll = 0;
async function pollEncryption(){
  if(_encPoll > 40) return;
  _encPoll++;
  try{
    const d = await (await fetch('/api/encryption')).json();
    let changed = false;
    for(const a of S.archives){
      if(Object.prototype.hasOwnProperty.call(d.map, a.path) && a.encrypted !== d.map[a.path]){
        a.encrypted = d.map[a.path];
        changed = true;
      }
    }
    if(changed){
      S.meta.encTotal = S.archives.filter(x=>x.encrypted===true).length;
      S.meta.encKnown = S.archives.filter(x=>x.encrypted!==null && x.encrypted!==undefined).length;
      renderNav(); renderStat();
      if(!S.cur) renderArchiveList();
    }
    if(!d.done) setTimeout(pollEncryption, 1200);
  }catch(e){ /* 忽略单次失败 */ }
}

function renderStat(){
  const m = S.meta;
  $('#statline').innerHTML =
    `共 <b>${m.total}</b> 个压缩包 · 已加密 <b>${m.encKnown < m.total ? m.encTotal + '+' : m.encTotal}</b><br>` +
    `${m.roots.length} 个监控目录`;
}

function renderNav(){
  const q = $('#q').value.trim().toLowerCase();
  const m = S.meta;
  let h = '';
  h += `<div class="entry ${S.sel && S.sel.type==='all' ? 'on':''}" data-nav="all">
          <span class="t">全部压缩包</span><span class="n">${m.total}</span></div>`;
  h += `<div class="entry ${S.sel && S.sel.type==='enc' ? 'on':''}" data-nav="enc">
          <span class="t">已加密</span><span class="n">${m.encKnown < m.total ? m.encTotal + '…' : m.encTotal}</span></div>`;
  h += `<div class="slabel">目录分组</div>`;

  for(const root of m.roots){
    const rid = 'r:' + root.path;
    const folded = !!S.folded[rid];
    const on = S.sel && S.sel.type==='root' && S.sel.root===root.path;
    h += `<div class="entry ${on?'on':''} ${folded?'folded':''}" data-nav="root" data-root="${esc(root.path)}">
            <span class="chev">▼</span>
            <span class="t" title="${esc(root.path)}">${esc(shortPath(root.path))}</span>
            <span class="n">${root.count}</span></div>`;
    if(!root.exists){
      h += `<div class="entry sub" style="color:#c62828">目录不存在</div>`;
      continue;
    }
    if(folded) continue;
    h += navTree(root.groups || [], root.path, 0, q);
  }
  $('#nav').innerHTML = h;

  $$('#nav [data-nav]').forEach(el=>{
    el.onclick = ev=>{
      const kind = el.dataset.nav;
      if(kind==='root'){
        const rid = 'r:' + el.dataset.root;
        S.folded[rid] = !S.folded[rid];
        renderNav();
        return;
      }
      // 点小三角 = 展开/收起这一级；点名字 = 选中
      if(kind==='group' && ev.target.classList.contains('chev') && ev.target.textContent.trim() && el.dataset.fold){
        S.folded[el.dataset.fold] = !S.folded[el.dataset.fold];
        renderNav();
        return;
      }
      if(kind==='all') S.sel = {type:'all'};
      else if(kind==='enc') S.sel = {type:'enc'};
      else S.sel = {type:'group', root:el.dataset.root, group:el.dataset.group};
      S.cur = null; S.files = [];
      renderNav();
      renderArchiveList();
    };
    if(el.dataset.nav === 'group'){
      el.oncontextmenu = ev=>{ ev.preventDefault(); groupMenu(ev, el.dataset.root, el.dataset.group); };
    }

    const kind = el.dataset.nav;
    if(kind === 'root' || kind === 'group'){
      // 拖到这里 = 移动到该目录
      el.addEventListener('dragover', ev=>{
        if(!S.drag) return;
        ev.preventDefault();
        el.classList.add('drop');
        try{ ev.dataTransfer.dropEffect = 'move'; }catch(e){}
      });
      el.addEventListener('dragleave', ()=>el.classList.remove('drop'));
      el.addEventListener('drop', ev=>{
        ev.preventDefault();
        ev.stopPropagation();
        el.classList.remove('drop');
        if(!S.drag) return;
        const src = S.drag.path;
        S.drag = null;
        const dst = navTargetDir(el);
        if(src && dst) moveTo(src, dst);
      });
      if(kind === 'group'){
        // 文件夹本身也能拖（移动到别的分组）
        el.setAttribute('draggable', 'true');
        el.addEventListener('dragstart', ev=>{
          const dp = navTargetDir(el);
          S.drag = {kind:'dir', path: dp};
          // 必须写一点 dataTransfer 数据，否则 Chrome/Edge 不会真正开始拖拽
          try{ ev.dataTransfer.setData('text/plain', dp); }catch(e){}
          try{ ev.dataTransfer.effectAllowed = 'move'; }catch(e){}
        });
        el.addEventListener('dragend', ()=>{ S.drag = null; });
      }
    }
  });
}

function shortPath(p){
  const parts = p.split(/[\\/]/).filter(Boolean);
  if(parts.length <= 2) return p;
  return '…\\' + parts.slice(-2).join('\\');
}

/* 左侧目录树：逐级渲染，子文件夹缩进显示 */
function navTree(nodes, rootPath, depth, q){
  let h = '';
  for(const g of nodes){
    const key = 'g:' + rootPath + ':' + g.path;
    const folded = !!S.folded[key];
    const gon = S.sel && S.sel.type==='group' && S.sel.root===rootPath && S.sel.group===g.path;
    const kids = g.children || [];
    if(q && !(g.name||'').toLowerCase().includes(q) && !rootPath.toLowerCase().includes(q)
       && !kids.some(c=>(c.name||'').toLowerCase().includes(q))) continue;
    h += `<div class="entry sub ${gon?'on':''}" style="padding-left:${8 + depth*13}px"
            data-nav="group" data-root="${esc(rootPath)}" data-group="${esc(g.path)}"
            data-fold="${esc(key)}">
            <span class="chev">${kids.length ? (folded?'▸':'▾') : ''}</span>
            <span class="t" title="${esc(g.path)}">${esc(g.name)}</span>
            <span class="n">${g.count}</span></div>`;
    if(!folded && kids.length) h += navTree(kids, rootPath, depth+1, q);
  }
  return h;
}

/* 分组的右键菜单：新建子文件夹 / 移动到… */
function groupMenu(ev, rootPath, group){
  const dir = rootPath + '\\' + group.replace(/\//g, '\\');
  showCtx(ev, [
    {icon:'', label:'新建子文件夹…', run:()=>askMkdirSub(dir)},
    {icon:'', label:'移动到…', run:()=>groupMoveTo(dir)},
    '-',
    {icon:'', label:'打开所在文件夹', run:()=>post('/api/fs/reveal',{path:dir})},
  ]);
}

function askMkdirSub(parent){
  dialog(`<h3>新建子文件夹</h3><div class="body">
    <div class="note" style="margin-bottom:8px;word-break:break-all">在 ${esc(parent)} 里</div>
    <input id="ndName" placeholder="文件夹名">
  </div><div class="foot">
    <button class="fbtn" id="ndCancel">取消</button>
    <button class="fbtn solid" id="ndOk">创建</button>
  </div>`, ()=>{
    $('#ndName').focus();
    $('#ndName').onkeydown = e=>{ if(e.key==='Enter') $('#ndOk').click(); };
    $('#ndCancel').onclick = closeDialog;
    $('#ndOk').onclick = async ()=>{
      const name = ($('#ndName').value || '').trim();
      if(!name) return;
      const d = await post('/api/fs/mkdir', {parent, name});
      if(d && d.error) return alert(d.error);
      closeDialog();
      await loadMeta(); renderNav(); renderArchiveList();
      toast('已创建 ' + name);
    };
  });
}

function groupMoveTo(srcDir){
  pickFolder('移动文件夹到…', dst=>{ moveTo(srcDir, dst); }, srcDir);
}

/* ===================== 中间列表 ===================== */
function renderArchiveList(root){
  root = root || $('#content');
  const isMain = root.id === 'content';
  if(isMain && S.contentMode === 'split'){ renderSplit(); return; }
  if(isMain && (!S.meta || !S.meta.roots || !S.meta.roots.length)){
    root.classList.remove('split');
    $('#crumb').innerHTML = '<b>还没添加目录</b>';
    root.innerHTML = '<div class="empty">还没有扫描目录 —— 打开 <b>设置 → 文件目录</b> 添加要扫描的文件夹</div>';
    return;
  }
  const q = $('#q').value.trim().toLowerCase();
  let list = S.archives;
  const sel = S.sel || {type:'all'};
  if(sel.type==='enc') list = list.filter(a=>a.encrypted===true || a.ext==='.sfx');
  else if(sel.type==='group') list = list.filter(a=>a.root===sel.root && ((a.dir_rel||'')===sel.group || (a.dir_rel||'').startsWith(sel.group + '/')));
  else if(sel.type==='root') list = list.filter(a=>a.root===sel.root);
  if(q) list = list.filter(a=>a.name.toLowerCase().includes(q) || a.rel.toLowerCase().includes(q));

  // 筛选面板：加密状态 / 有没有预览图
  if(S.flt){
    if(S.flt.enc === 'enc') list = list.filter(a=>a.encrypted===true || a.ext==='.sfx');
    else if(S.flt.enc === 'plain') list = list.filter(a=>a.encrypted===false);
    if(S.flt.cov !== 'all'){
      if(!S.coverMap){
        loadCovers().then(()=>renderArchiveList(root));
        root.innerHTML = '<div class="empty">正在统计预览图…</div>';
        return;
      }
      list = list.filter(a=> S.flt.cov==='has' ? !!S.coverMap[a.path] : !S.coverMap[a.path]);
    }
  }
  if(S.batch && S.batch.on) S.batch.order = list.map(a=>a.path);

  if(isMain){
    $('#crumb').innerHTML = `<b>${esc(crumbText(sel))}</b>
      <span style="color:var(--text3)">${list.length} 个</span>`;
    $('#secSummary').textContent = '';
    root.classList.remove('split');
  }

  if(!list.length){
    root.innerHTML = '<div class="empty">这个分组下没有压缩包</div>';
    return;
  }

  const groups = {};
  for(const a of list){ (groups[a.dir] = groups[a.dir] || []).push(a); }

  let h = `<div class="${S.viewMode==='rows'?'rows':''}">`;
  for(const dir of Object.keys(groups).sort()){
    h += `<div class="dirbar">${esc(dir)}</div><div class="${S.viewMode==='grid'?'grid':''}">`;
    for(const a of groups[dir]){
      h += `<div class="card ${S.batch&&S.batch.on&&S.batch.sel.has(a.path)?'sel':''}" data-archive="${esc(a.path)}" draggable="true">
        <div class="box"><span class="ext">${a.badge}</span>${coverBox(a.path)}</div>
        <div class="info">
          <div class="fn" title="${esc(a.name)}">${esc(a.name)}</div>
          <div class="fs"><span class="tag ${a.ext==='.sfx'?'sfx':''}">${a.badge}</span>${a.encrypted===true?'<span class="tag enc">加密</span>':''}<span>${a.size}</span></div>
        </div></div>`;
    }
    h += '</div>';
  }
  h += '</div>';
  root.innerHTML = h;

  $$all(root, '[data-archive]').forEach(el=>{
    el.setAttribute('draggable', 'true');
    el.onclick = ev=>{
      if(S.batch && S.batch.on) return batchClick(ev, el.dataset.archive);
      openArchive(el.dataset.archive);
    };
    el.oncontextmenu = ev=>{ ev.preventDefault(); archiveMenu(ev, el.dataset.archive); };
    el.addEventListener('dragstart', ev=>{
      S.drag = {kind:'file', path: el.dataset.archive};
      el.classList.add('dragging');
      try{ ev.dataTransfer.setData('text/plain', el.dataset.archive); }catch(e){}
      try{ ev.dataTransfer.effectAllowed = 'move'; }catch(e){}
    });
    el.addEventListener('dragend', ()=>el.classList.remove('dragging'));
  });
}

/* ---- 拖拽移动（Windows 资源管理器式：剪切到目标目录） ---- */
function navTargetDir(el){
  const root = el.dataset.root || '';
  if(el.dataset.nav === 'root') return root;
  const g = el.dataset.group || '';
  return g ? root + '\\' + g.replace(/\//g, '\\') : root;
}

async function moveTo(src, dstDir){
  // 批量模式下拖其中的一个 = 把选中的全部拖过去
  if(S.batch && S.batch.on && S.batch.sel.has(src) && S.batch.sel.size > 1){
    return doBatchMove([...S.batch.sel], dstDir);
  }
  const d = await post('/api/fs/move', {src, dst_dir: dstDir});
  if(d.error) return toast(d.error);
  if(d.conflict){
    askOverwrite(d.name, yes=>{
      if(!yes) return;
      post('/api/fs/move', {src, dst_dir: dstDir, overwrite: true}).then(r=>{
        if(r.error) toast(r.error); else afterMove(r);
      });
    });
    return;
  }
  afterMove(d);
}

function afterMove(d){
  if(d.meta){ S.meta = d.meta; S.archives = d.meta.archives; }
  if(S.cur && !S.archives.some(a=>a.path === S.cur)){ S.cur = null; S.files = []; }
  S.sel = {type:'all'};
  renderNav(); renderStat(); renderArchiveList();
  toast('已移动');
}

function askOverwrite(name, cb){
  dialog(`<h3>已有同名项</h3>
    <div class="body"><div class="note">目标文件夹里已经有 <b>${esc(name)}</b>，要覆盖吗？</div></div>
    <div class="foot">
      <button class="fbtn" id="owNo">跳过</button>
      <button class="fbtn solid" id="owYes">覆盖</button>
    </div>`, ()=>{
      $('#owYes').onclick = ()=>{ closeDialog(); cb(true); };
      $('#owNo').onclick = ()=>{ closeDialog(); cb(false); };
    });
}
function $$all(root, sel){ return [...root.querySelectorAll(sel)]; }

function crumbText(sel){
  if(sel.type==='enc') return '已加密压缩包';
  if(sel.type==='group') return (sel.group || '(根目录)');
  if(sel.type==='root') return sel.root;
  return '全部压缩包';
}

async function openArchive(path){
  const a = S.archives.find(x=>x.path===path);
  S.cur = path; S.curName = a ? a.name : path.split('/').pop();
  if(S.contentMode === 'split' && $('#paneRight')){
    // 铺开模式：左侧列表保持不动，只在右侧「新窗口」里显示加载态
    $('#paneRight').innerHTML = '<div class="empty"><div class="spin"></div>正在读取压缩包…</div>';
    $$all($('#paneLeft'), '[data-archive]').forEach(el=>
      el.classList.toggle('on', el.dataset.archive === path));
  }else{
    $('#content').innerHTML = '<div class="empty"><div class="spin"></div>正在读取压缩包…</div>';
  }
  try{
    const r = await fetch(`/api/list?path=${enc(path)}&password=${enc(S.pwd)}`);
    const d = await r.json();
    if(d.need_password){ askPassword(path, d.error); return; }
    if(d.error){ $('#content').innerHTML = `<div class="err">${esc(d.error)}</div>`; return; }
    S.files = d.files || [];
    S.pwTried = false;
    // 分栏筛选 / 折叠状态跨压缩包保持，不重置
    syncFilterBtns();
    renderFiles();
  }catch(e){
    $('#content').innerHTML = `<div class="err">${esc(String(e))}</div>`;
  }
}

/* 只有加密包打不开时才问密码；密码会用于后续所有资源请求（模型 / 贴图 / 预览） */
function askPassword(path, err){
  const name = esc(S.curName);
  const saved = (S.passwords || []);
  const chips = saved.length
    ? `<div class="pwchips">${saved.map((p,i)=>
        `<button class="fbtn" data-pw="${i}" title="点一下直接试这个密码">${esc(p)}</button>`
      ).join('')}</div>
      <div class="note" style="margin-top:4px">已保存的密码（设置 → 密码管理 里可以增删）</div>`
    : `<div class="note">还没有保存过密码，可以在「设置 → 密码管理」里添加。</div>`;
  dialog(`<h3>这个压缩包需要密码</h3>
    <div class="body">
      <div class="fld">
        <label>${name}</label>
        <input type="password" id="pwInput" placeholder="输入压缩包密码" autocomplete="off">
      </div>
      ${chips}
      <div class="note">密码会用于读取包内的模型、贴图和预览图；加密包不输入密码无法预览 3D 模型。</div>
      <div class="pwderr" id="pwErr">${err && S.pwTried ? esc(err) : ''}</div>
    </div>
    <div class="foot">
      <button class="fbtn" id="pwCancel">取消</button>
      <button class="fbtn solid" id="pwOk">确定</button>
    </div>`, ()=>{
      const el = $('#pwInput'); el.focus();
      el.onkeydown = ev=>{ if(ev.key==='Enter') $('#pwOk').click(); };
      $$('#dlg [data-pw]').forEach(b=>b.onclick = ()=>{
        el.value = S.passwords[+b.dataset.pw] || '';
        $('#pwOk').click();
      });
    });
  $('#pwCancel').onclick = ()=>{ closeDialog(); backToList(); };
  $('#pwOk').onclick = ()=>{
    const v = $('#pwInput').value;
    if(!v){ $('#pwErr').textContent = '请输入密码'; return; }
    S.pwd = v; S.pwTried = true; S.coverVer++;
    closeDialog();
    openArchive(path);
  };
}

/* ===================== 按类型分栏 ===================== */
const TEXTURE_EXT = new Set(['.dds','.sph','.spa','.toon','.mtl','.tga']);
const MOTION_EXT  = new Set(['.vmd','.vpd','.mp3','.wav','.ogg','.mp4','.mkv','.avi','.flac']);
const DOC_EXT     = new Set(['.txt','.json','.xml','.ini','.md','.cfg','.csv','.log','.py','.bat','.ps1','.html','.htm','.yaml','.yml']);

/* 顺序即显示顺序：模型第一栏、图片第二栏 */
const SECTIONS = [
  {key:'model',   color:'#3b6ef5', name:'3D 模型',       test:f=>f.is_3d},
  {key:'image',   color:'#1f9d63', name:'图片',           test:f=>f.is_image && f.ext!=='.dds'},
  {key:'texture', color:'#d97706', name:'贴图 / 材质',    test:f=>TEXTURE_EXT.has(f.ext)},
  {key:'archive', color:'#7c5cf0', name:'嵌套压缩包',     test:f=>f.is_archive},
  {key:'motion',  color:'#db2777', name:'动作 / 影音',    test:f=>MOTION_EXT.has(f.ext)},
  {key:'doc',     color:'#0d8fd0', name:'文档 / 配置',    test:f=>DOC_EXT.has(f.ext)},
  {key:'other',   color:'#9c9ca6', name:'其他',           test:()=>true},
];

function classify(files){
  const buckets = SECTIONS.map(s=>({key:s.key, color:s.color, name:s.name, items:[]}));
  const map = Object.fromEntries(buckets.map(b=>[b.key,b]));
  const used = new Set();
  for(const s of SECTIONS.slice(0,-1)){
    for(const f of files){
      if(used.has(f.path)) continue;
      if(s.test(f)){ map[s.key].items.push(f); used.add(f.path); }
    }
  }
  map.other.items = files.filter(f=>!used.has(f.path));
  return buckets;
}

/* 渲染一组文件的网格（按目录分组），堆叠/铺开两种模式共用 */
function renderGrid(items){
  const groups = {};
  for(const f of items){
    const dir = f.path.includes('/') ? f.path.slice(0, f.path.lastIndexOf('/')) : '';
    (groups[dir] = groups[dir] || []).push(f);
  }
  const dirs = Object.keys(groups).sort();
  let h = '';
  for(const dir of dirs){
    if(dir && dirs.length > 1) h += `<div class="dirbar">${esc(dir)}</div>`;
    h += `<div class="${S.viewMode==='grid'?'grid':''} ${S.viewMode==='rows'?'rows':''}">`;
    for(const f of groups[dir]) h += fileCard(f);
    h += '</div>';
  }
  return h;
}

function bindFileCards(root){
  root = root || $('#content');
  $$all(root, '[data-file]').forEach(el=>{
    const p = el.dataset.file;
    el.onclick = ()=>onFile(p);
    el.oncontextmenu = ev=>{ ev.preventDefault(); fileMenu(ev, p); };
  });
}

/* 左右铺开：左侧压缩包列表，右侧所选压缩包的包内内容 */
/* 左右铺开 = 两个「原有视口」并排：
   左窗格保持原来的压缩包列表（可继续点选），右窗格相当于点进去后另开的新窗口，
   显示的就是原模式里那份按类型分栏的内容，两边都复用原来的渲染逻辑。 */
function renderSplit(){
  const content = $('#content');
  content.classList.add('split');
  $('#cmodeBtn').classList.add('on');
  $('#cmodeBtn').textContent = '堆叠分栏';

  const sel = S.sel || {type:'all'};
  $('#crumb').innerHTML = `<b>${esc(crumbText(sel))}</b>
    <span style="color:var(--text3)">${S.cur ? '· ' + esc(S.curName) : '左右铺开'}</span>`;

  // 已存在双窗格就只刷新内容，避免每次点击重建 DOM 造成滚动位置丢失
  let L = $('#paneLeft'), R = $('#paneRight');
  if(!L || !R){
    content.innerHTML = `<div class="split-pane" id="paneLeft"></div>
      <div class="split-drag" id="splitDrag" title="拖动调整左右宽度"></div>
      <div class="split-pane" id="paneRight"></div>`;
    L = $('#paneLeft'); R = $('#paneRight');
    bindSplitDrag();
  }

  // 左：原压缩包列表视图（原样，含封面卡片 / 分组 / 网格或列表）
  renderArchiveList(L);
  // 右：原点进压缩包后的内容视图（原样，含类型分栏 / 折叠 / 筛选）
  if(S.cur){
    R.innerHTML = `<div class="panehd"><span style="flex:1;min-width:0;overflow:hidden;
      text-overflow:ellipsis;white-space:nowrap" title="${esc(S.curName)}">${esc(S.curName)}</span>
      <button class="fbtn" id="paneClose">✕ 关闭</button></div><div id="paneBody"></div>`;
    $('#paneClose').onclick = ()=>{ S.cur = null; S.files = []; renderSplit(); };
    renderFiles($('#paneBody'), true);
  } else R.innerHTML = `<div class="empty">从左侧点一个压缩包<br>
    <span style="font-size:12px">这里相当于另开一个窗口显示包内内容</span></div>`;

  // 左侧选中态
  $$all(L, '[data-archive]').forEach(el=>{
    el.classList.toggle('on', el.dataset.archive === S.cur);
  });
}

let _splitDragBound = false;
function bindSplitDrag(){
  if(_splitDragBound) return;
  _splitDragBound = true;
  const bar = $('#splitDrag'), L = $('#paneLeft');
  bar.addEventListener('pointerdown', ev=>{
    ev.preventDefault(); bar.setPointerCapture(ev.pointerId);
    const x0 = ev.clientX, w0 = L.getBoundingClientRect().width;
    const move = e=>{
      const w = Math.max(220, Math.min($('#content').clientWidth - 300, w0 + e.clientX - x0));
      L.style.flex = '0 0 ' + w + 'px';
      try{ localStorage.setItem('zipview.splitw', Math.round(w)); }catch(_){}
      if(typeof resizeGL === 'function') resizeGL();
    };
    const up = ()=>{
      bar.removeEventListener('pointermove', move);
      bar.removeEventListener('pointerup', up);
    };
    bar.addEventListener('pointermove', move);
    bar.addEventListener('pointerup', up);
  });
  try{
    const w = parseInt(localStorage.getItem('zipview.splitw') || '0', 10);
    if(w >= 220) L.style.flex = '0 0 ' + w + 'px';
  }catch(e){}
}

function renderFiles(root, inPane){
  const content = root || $('#content');
  const isMain = !inPane;
  const split = S.contentMode === 'split';
  if(isMain){
    content.classList.toggle('split', split);
    $('#cmodeBtn').classList.toggle('on', split);
    $('#cmodeBtn').textContent = split ? '堆叠分栏' : '左右铺开';
    if(split){ renderSplit(); return; }
  }

  const buckets = classify(S.files);
  const active = buckets.filter(b=>b.items.length > 0);

  if(isMain){
    $('#crumb').innerHTML = `<span class="back" id="crumbBack">← 返回</span>
      <b title="${esc(S.curName)}">${esc(S.curName)}</b>
      <span style="color:var(--text3)">${S.files.length} 个文件 · ${active.length} 栏</span>`;
    $('#crumbBack').onclick = backToList;
    $('#secSummary').textContent = active.map(b=>`${b.name} ${b.items.length}`).join('   ·   ');
  } else {
    content.scrollTop = content.scrollTop || 0;
  }

  // 灯箱始终包含包内全部可预览图片（dds 浏览器不认，排除）
  S.lbList = S.files.filter(f=>f.is_image && f.ext!=='.dds').map(f=>f.path);

  if(!active.length){
    content.innerHTML = '<div class="empty">这个压缩包里没有可显示的文件</div>';
    return;
  }

  // ---- 堆叠：各类别上下排列 ----
  const shown = active.filter(b => S.filter==='all' || S.filter===b.key);
  if(!shown.length){
    content.innerHTML = '<div class="empty">这个类型下没有文件<br><span style="font-size:12px">点上方「全部」看所有栏</span></div>';
    return;
  }

  let h = '';
  for(const b of shown){
    const folded = !!S.foldSec[b.key];
    const onlyOn = S.filter===b.key;
    h += `<div class="sec" data-sec="${b.key}">
      <div class="sechead" data-sechead="${b.key}" style="border-left:3px solid ${b.color}">
        <span class="chev">${folded?'▸':'▾'}</span>
        <span class="sname">${b.name}</span>
        <span class="scount">${b.items.length}</span>
        <span class="sline"></span>
        <button class="sonly ${onlyOn?'on':''}" data-only="${b.key}">${onlyOn?'显示全部':'只看这栏'}</button>
      </div>
      <div class="secbody ${folded?'fold':''}">`;
    if(folded){ h += '</div></div>'; continue; }
    h += renderGrid(b.items);
    h += '</div></div>';
  }
  content.innerHTML = h;
  bindFileCards(content);
  $$all(content, '[data-sechead]').forEach(el=>{
    el.onclick = ()=>{
      const k = el.dataset.sechead;
      S.foldSec[k] = !S.foldSec[k];
      isMain ? renderFiles() : renderSplit();
    };
  });
  $$all(content, '[data-only]').forEach(el=>{
    el.onclick = ev=>{
      ev.stopPropagation();
      const k = el.dataset.only;
      S.filter = (S.filter===k) ? 'all' : k;
      syncFilterBtns();
      isMain ? renderFiles() : renderSplit();
      (isMain ? $('#content') : content).scrollTop = 0;
    };
  });
}

function syncFilterBtns(){
  $$('[data-filter]').forEach(b=>b.classList.toggle('on', b.dataset.filter===S.filter));
}

function fileCard(f){
  const base = `path=${enc(S.cur)}&inner=${enc(f.path)}&password=${enc(S.pwd)}`;
  let box;
  if(f.is_image && f.ext!=='.dds'){
    box = `<div class="box"><img loading="lazy" src="/api/thumb?${base}"
      onerror="this.parentNode.innerHTML='<span class=&quot;ext&quot;>IMG</span>'"></div>`;
  }else{
    const label = (f.ext || '').replace('.','').toUpperCase() || 'FILE';
    box = `<div class="box"><span class="ext">${label}</span></div>`;
  }
  const tags = [];
  if(f.is_3d) tags.push('<span class="tag" style="background:#eef3ff;color:#3b6ef5">3D</span>');
  if(f.encrypted) tags.push('<span class="tag enc">加密</span>');
  const extLabel = (f.ext || '').replace('.','').toUpperCase() || 'FILE';
  return `<div class="card" data-file="${esc(f.path)}">
    ${box}
    <div class="info">
      <div class="fn" title="${esc(f.name)}">${esc(f.name)}</div>
      <div class="fs">${tags.join('')}<span>${f.size}</span></div>
    </div></div>`;
}

function onFile(path){
  const f = S.files.find(x=>x.path===path);
  if(!f) return;
  if(f.is_image && f.ext!=='.dds') return openLb(path);
  if(f.is_3d) return loadModel(path);
  return showNeedApp(f);          // 不能内嵌预览：在右侧预览区给入口，不直接下载
}

/* 不能预览的格式：在预览区显示文件名 + 「用 XXX 打开」入口 */
function showNeedApp(f){
  if(OBJ) clearModel();
  curModelPath = S.cur;
  $('#vTitle').textContent = f.name;
  $('#vBadge').classList.remove('show');
  const op = S.openers && S.openers[f.ext];
  const isText = TEXT_EXT && TEXT_EXT.has(f.ext);
  const nm = op
    ? ((op.split(/[\\/]/).pop() || '外部程序').replace(/\.(exe|bat|cmd)$/i, ''))
    : (isText ? '记事本' : '');
  const kv = `<div class="vkv">
    <div class="k">文件</div><div class="v">${esc(f.name)}</div>
    <div class="k">格式</div><div class="v">${esc(f.ext.replace('.','').toUpperCase())} · ${f.size}</div>
  </div>`;
  if(op || isText){
    setHint(isText && !op ? '文本文件' : '这个格式需要外部程序',
            `${esc(f.ext)} · 用 ${esc(nm)} 打开`);
    $('#vFoot').innerHTML = `<div class="vrow">
      <button class="fbtn solid" id="vOpenExt">用 ${esc(nm)} 打开</button>
      <button class="fbtn" id="vSave">下载</button></div>` + kv;
    $('#vOpenExt').onclick = ()=>openExternal(f);
  }else{
    setHint('这个格式不能内嵌预览', `${esc(f.ext)} · 在 设置 → 格式关联 里给它配一个程序`);
    $('#vFoot').innerHTML = `<div class="vrow"><button class="fbtn" id="vSave">下载</button></div>` + kv;
  }
  const sv = $('#vSave');
  if(sv) sv.onclick = ()=>download(f.path);
}

/* 用设置里配置的外部程序打开（.zprj → Marvelous Designer、文本 → 记事本 等） */
async function openExternal(f){
  const isText = TEXT_EXT && TEXT_EXT.has(f.ext);
  if((!S.openers || !S.openers[f.ext]) && !isText){
    return alert(`还没有给 ${f.ext} 配置外部程序。\n\n设置 → 格式关联，写一行：\n${f.ext}=程序完整路径`);
  }
  const d = await post('/api/open_external',
    {path:S.cur, inner:f.path, ext:f.ext, password:S.pwd});
  if(d && d.error) alert(d.error);
}

function backToList(){
  S.cur = null; S.files = [];
  renderArchiveList();
}

/* ===================== 3D 视口 ===================== */
let R=null, SC=null, CAM=null, CTL=null, OBJ=null, curModelPath='';
let _dirty = true;   // 需要重画一帧

function initGL(){
  if(R) return true;
  const canvas = $('#c3d');
  if(!window.THREE){ setHint('three.js 未加载', '检查 vendor 目录'); return false; }
  R = new THREE.WebGLRenderer({canvas, antialias:true, preserveDrawingBuffer:true});
  R.setPixelRatio(Math.min(devicePixelRatio, 2));
  if('outputEncoding' in R) R.outputEncoding = THREE.sRGBEncoding;
  // PMXEditor 不做电影级色调映射，贴图颜色 1:1 输出；ACES 会把角色压灰、去饱和。
  // 用线性输出 + 曝光控制亮度：曝光按模型贴图平均亮度自动归一化（各来源素材明暗差别很大）
  if('toneMapping' in R){
    R.toneMapping = THREE.LinearToneMapping;
    R.toneMappingExposure = 1.0;
  }

  SC = new THREE.Scene();
  // PMXEditor 同款：纯白背景
  SC.background = new THREE.Color(0xffffff);

  CAM = new THREE.PerspectiveCamera(38, 1, 0.1, 8000);
  CAM.position.set(0, 12, 34);

  CTL = new THREE.OrbitControls(CAM, canvas);
  CTL.enableDamping = true;
  CTL.dampingFactor = 0.08;
  CTL.target.set(0, 10, 0);
  applyMouseMode();

  // 四灯布光：环境 + 主光 + 补光 + 跟随相机的正面光（避免转角度后脸发黑）
  // 半球光的地面色原来是 0xa8adbd（偏蓝的灰），会给暗部刷一层冷灰、看着「掉色」，
  // PMXEditor 的环境色是中性白，这里改成接近中性的浅灰。
  LIGHTS = {
    hemi: new THREE.HemisphereLight(0xffffff, 0xe6e6e6, LIGHT_BASE.hemi),
    key:  new THREE.DirectionalLight(0xffffff, LIGHT_BASE.key),
    fill: new THREE.DirectionalLight(0xffffff, LIGHT_BASE.fill),
    face: new THREE.DirectionalLight(0xffffff, LIGHT_BASE.face),
  };
  LIGHTS.key.position.set(1.1, 1.9, 1.7);
  LIGHTS.fill.position.set(-1.7, 0.9, -1.3);
  SC.add(LIGHTS.hemi, LIGHTS.key, LIGHTS.fill, LIGHTS.face);
  applyLightLevel();

  // 地面网格在 fitCamera 时按模型尺寸生成（见 updateGrid）

  resizeGL();
  new ResizeObserver(resizeGL).observe($('#canvasWrap'));
  // 按需渲染：相机没动、也没改参数时不重画（空闲时 GPU 占用接近 0）
  (function loop(){
    requestAnimationFrame(loop);
    let moved = false;
    if(CTL) moved = !!CTL.update();
    // 正面光永远从相机方向打过来
    if(LIGHTS && CAM) LIGHTS.face.position.copy(CAM.position);
    if(R && SC && CAM && (_dirty || moved)){
      R.render(SC, CAM);
      _dirty = false;
    }
  })();
  return true;
}

/* 需要重画一帧时调用（改光照/换曝光/贴图加载完等） */
function markDirty(){ _dirty = true; }

/* 光照总和必须正好 1.0：这是「贴图 1:1 输出」的前提。
   之前是 1.15，等于整体提亮 15%（sRGB 端点下约 +6%），皮肤就显白、掉饱和。
   配比也调得更「主光为主」：PMXEditor 基本是一盏主光 + 少量环境，
   原来 hemi 0.35 + fill 0.10 + face 0.08 的三路补光把明暗压平了，看起来发雾。
   不要再改这组值；要整体调亮请用界面的「光照」滑块。 */
const LIGHT_BASE = {hemi:0.22, key:0.70, fill:0.04, face:0.04};
let LIGHTS = null;

function applyLightLevel(){
  const v = S.light;
  if(!LIGHTS) return;
  LIGHTS.hemi.intensity = LIGHT_BASE.hemi * v;
  LIGHTS.key.intensity  = LIGHT_BASE.key  * v;
  LIGHTS.fill.intensity = LIGHT_BASE.fill * v;
  LIGHTS.face.intensity = LIGHT_BASE.face * v;
  markDirty();
  // 光照颜色：给所有灯染色，整体偏暖/偏冷（白 = 不染色）
  const c = S.lightColor || '#ffffff';
  if(LIGHTS.key.color && LIGHTS.key.color.set){
    LIGHTS.key.color.set(c);
    LIGHTS.fill.color.set(c);
    LIGHTS.face.color.set(c);
    LIGHTS.hemi.color.set(c);
    LIGHTS.hemi.groundColor.set(c).multiplyScalar(0.9);
  }
}

/* ===== 材质翻译：MMD 语义 → three.js ===== */

/* 只修一处：MMDLoader 把 PMX 的 ambient 写成了「加在末尾的 emissive」
   （有贴图 ×0.2、无贴图 ×1.0）。典型 ambient 0.4~1.0 → emissive 0.08~0.2，
   经 sRGB 输出就是 0.33~0.48 的灰底，整幅画面像蒙了层雾。
   中性色直接清零；彩色的（多半是发光装饰）保留。
   toon ramp 一律不动——PE 对 toonIndex = -1 / 近白 ramp 就是平光，改了反而和 PE 不一致。 */
function normalizeToonMaterial(m){
  if(!m || !m.isMeshToonMaterial) return false;
  if(m.emissiveMap || !m.emissive) return false;
  const e = m.emissive;
  if(!(e.r || e.g || e.b)) return false;
  if(Math.max(e.r, e.g, e.b) - Math.min(e.r, e.g, e.b) >= 0.08) return false;   // 彩色保留
  e.setRGB(0, 0, 0);
  return true;
}
/* 曝光只用来「防止高光被切白」，不再把每个包硬拉到同一个平均亮度。
   LinearToneMapping 没有高光肩部，超过 1/曝光 的像素直接变白；原来按均值归一化，
   暗色衣服多的包（星铁、二重螺旋）会被拉到 1.3~1.45×，脸和亮部整片死白。
   现在看 85 分位（脸这种最亮的材质）：亮包只压不抬，很暗的包才轻微提亮。
   返回 null 表示贴图还没解码完。 */
function autoExposure(obj){
  const lums = [];
  let pending = false;
  obj.traverse(x=>{
    if(!x.isMesh) return;
    (Array.isArray(x.material) ? x.material : [x.material]).forEach(m=>{
      if(m.map && (!m.map.image || !m.map.image.width)) pending = true;  // 还没解码完
      const im = m.map && m.map.image;
      if(!im || !im.width) return;
      const c = document.createElement('canvas');
      c.width = c.height = 24;
      const cx = c.getContext('2d', {willReadFrequently:true});
      try{ cx.drawImage(im, 0, 0, 24, 24); }catch(e){ return; }
      const d = cx.getImageData(0, 0, 24, 24).data;
      let s = 0, n = 0;
      for(let i = 0; i < d.length; i += 4){
        if(d[i+3] < 40) continue;
        s += d[i]*0.299 + d[i+1]*0.587 + d[i+2]*0.114;
        n++;
      }
      if(n) lums.push(s / n / 255);
    });
  });
  if(pending || !lums.length) return null;
  lums.sort((a, b)=>a - b);
  const q = v => lums[Math.min(lums.length-1, Math.max(0, Math.round(v*(lums.length-1))))];
  const p85 = q(0.85);
  // 光照总和是 1.0 时，输出就等于贴图本身（PMXEditor 的 1:1）。
  // 所以这里只在「最亮的那批材质会切白」时往下压一点，绝不往上抬——
  // 往上抬正是之前整体发白、掉饱和的来源。
  const LIGHT_SUM = 1.0;
  const e = (p85 * LIGHT_SUM > 0.95) ? 0.95 / (p85 * LIGHT_SUM) : 1.0;
  return Math.round(Math.min(1.0, Math.max(0.85, e)) * 100) / 100;
}

/* 鼠标操作模式：
   default = 左键旋转 / 滚轮缩放 / 右键平移
   alt     = 右键旋转 / 左键拖动平移 / 滚轮缩放（中键不绑定） */
function applyMouseMode(){
  if(!CTL || !THREE.MOUSE) return;
  const alt = S.mouseMode === 'alt';
  if(alt){
    CTL.mouseButtons = {
      LEFT: THREE.MOUSE.PAN,
      MIDDLE: -1,                      // 中键不绑定
      RIGHT: THREE.MOUSE.ROTATE
    };
  }else{
    CTL.mouseButtons = { LEFT: THREE.MOUSE.ROTATE, MIDDLE: THREE.MOUSE.DOLLY, RIGHT: THREE.MOUSE.PAN };
  }
  const tip = $('#mouseTip');
  if(tip) tip.textContent = alt
    ? '右键旋转 · 左键拖动平移 · 滚轮缩放'
    : '左键旋转 · 滚轮缩放 · 右键平移';
  bindViewerMouseGuards();
}

/* 浏览器在右键拖动结束时会补发 contextmenu / auxclick，OrbitControls 的
   preventDefault 只覆盖 canvas 上的 pointerdown，拖到 canvas 外或被浏览器
   接手后就会中断旋转（表现为"视角直接退出"）。这里在捕获阶段彻底拦掉。 */
let _mouseGuardsBound = false;
function bindViewerMouseGuards(){
  if(_mouseGuardsBound) return;
  const wrap = $('#canvasWrap');
  if(!wrap) return;
  _mouseGuardsBound = true;
  const stop = e=>{ e.preventDefault(); e.stopPropagation(); };
  wrap.addEventListener('contextmenu', stop, true);
  wrap.addEventListener('auxclick', stop, true);
  wrap.addEventListener('dragstart', stop, true);
  wrap.addEventListener('selectstart', stop, true);
  // 指针按下后捕获，保证拖出画布也能继续旋转 / 平移
  const c = $('#c3d');
  c.addEventListener('pointerdown', e=>{
    try{ c.setPointerCapture(e.pointerId); }catch(_){}
  }, true);
  c.addEventListener('pointerup', e=>{
    try{ c.releasePointerCapture(e.pointerId); }catch(_){}
  }, true);
}

function resizeGL(){
  if(!R) return;
  const el = $('#canvasWrap');
  const w = el.clientWidth || 400, h = el.clientHeight || 300;
  R.setSize(w, h, false);
  CAM.aspect = w / Math.max(1, h);
  CAM.updateProjectionMatrix();
  markDirty();
}

function setHint(main, sub){
  const h = $('#vHint');
  if(!main){ h.classList.add('hide'); return; }
  h.classList.remove('hide');
  h.innerHTML = `<div class="big">3D</div><div>${esc(main)}</div>` +
                (sub ? `<div class="sub">${sub}</div>` : '');
}

function clearModel(){
  if(!OBJ) return;
  SC.remove(OBJ);
  const seen = new Set();
  OBJ.traverse(o=>{
    if(o.geometry && o.geometry.dispose){
      o.geometry.dispose();
      if(o.geometry.attributes){
        Object.keys(o.geometry.attributes).forEach(k=>{
          const a = o.geometry.attributes[k];
          if(a && a.dispose) a.dispose();
        });
      }
    }
    if(o.material){
      (Array.isArray(o.material)?o.material:[o.material]).forEach(m=>{
        // 把所有「值是贴图」的槽位都释放（不只是 map）：glb/fbx 还有
        // emissiveMap / normalMap / metalnessMap / roughnessMap / aoMap / alphaMap…
        // 不释放的话，连续打开几十个模型会把显存吃满。
        for(const k in m){
          const v = m[k];
          if(v && v.isTexture && !seen.has(v)){
            seen.add(v);
            try{ v.dispose(); }catch(e){}
          }
        }
        if(m.dispose) m.dispose();
      });
    }
  });
  OBJ = null;
  // 曝光是按模型算的，换模型先归位，避免沿用上一个模型的曝光
  if(R && 'toneMappingExposure' in R) R.toneMappingExposure = 1.0;
}

function assetURL(baseDir, rel){
  return `/api/asset?path=${enc(curModelPath)}&password=${enc(S.pwd)}` +
         `&base=${enc(baseDir)}&rel=${enc(rel)}`;
}

/* MMDLoader 会用 resourcePath + 贴图名 拼路径，这里给它一个可识别的标记 */
const ASSET_TAG = '@asset/';

function makeManager(baseDir){
  const mgr = new THREE.LoadingManager();
  mgr.setURLModifier(url=>{
    if(/^(data:|blob:|https?:)/.test(url)) return url;
    if(url.startsWith('/api/model') || url.startsWith('/api/asset')) return url;
    let rel = url;
    if(rel.startsWith(ASSET_TAG)) rel = rel.slice(ASSET_TAG.length);
    else if(rel.startsWith('/')){ rel = rel.slice(1); if(rel.startsWith('api/')) rel = rel.slice(4); }
    if(!rel) return url;
    return assetURL(baseDir, rel);
  });
  // 贴图统一用 TextureLoader（服务端已转 PNG），避开 TGA/DDS 的格式问题
  mgr.addHandler(/\.(png|jpg|jpeg|bmp|tga|dds|gif|webp)$/i, new THREE.TextureLoader(mgr));
  return mgr;
}

/* 蒙皮模型的几何包围盒是绑定姿态下的，骨骼也可能与网格不同缩放（FBX 常见 100 倍）。
   这里直接对蒙皮后的顶点采样，得到真正渲染出来的范围。 */
function computeBounds(obj){
  obj.updateWorldMatrix(true, true);
  const box = new THREE.Box3();
  const v = new THREE.Vector3();
  let any = false;

  obj.traverse(o=>{
    if(!o.isMesh || !o.geometry) return;
    const pos = o.geometry.attributes && o.geometry.attributes.position;
    if(o.isSkinnedMesh && o.skeleton && o.skeleton.bones.length && pos && o.geometry.attributes.skinIndex){
      const step = Math.max(1, Math.floor(pos.count / 4000));
      for(let i = 0; i < pos.count; i += step){
        v.fromBufferAttribute(pos, i);
        try{ o.boneTransform(i, v); }catch(e){ /* 少数畸形骨骼跳过 */ }
        v.applyMatrix4(o.matrixWorld);
        box.expandByPoint(v);
      }
      any = true;
    }else{
      if(!o.geometry.boundingBox) o.geometry.computeBoundingBox();
      box.union(o.geometry.boundingBox.clone().applyMatrix4(o.matrixWorld));
      any = true;
    }
  });

  if(!any || box.isEmpty()) return new THREE.Box3().setFromObject(obj);
  return box;
}

function fitCamera(obj){
  const box = computeBounds(obj);
  if(box.isEmpty()) return;
  const size = box.getSize(new THREE.Vector3());
  const center = box.getCenter(new THREE.Vector3());
  const maxDim = Math.max(size.x, size.y, size.z) || 1;
  const dist = maxDim / (2 * Math.tan(Math.PI * CAM.fov / 360)) * 1.18;
  CTL.target.copy(center);
  CAM.position.set(center.x, center.y + size.y * 0.04, center.z + dist);
  CAM.near = Math.max(0.001, dist / 2000);
  CAM.far = dist * 200;
  CAM.updateProjectionMatrix();
  CTL.update();
  updateGrid(box, maxDim);
  markDirty();
}

/* 地面：网格 + 红/蓝坐标轴 + 脚下柔和投影，观感对齐 PMXEditor */
let GROUND = null;
function updateGrid(box, maxDim){
  if(GROUND){
    GROUND.traverse(o=>{
      if(o.geometry) o.geometry.dispose();
      if(o.material){ (Array.isArray(o.material)?o.material:[o.material]).forEach(m=>{
        if(m.map) m.map.dispose(); m.dispose(); }); }
    });
    SC.remove(GROUND);
  }
  const span = Math.max(maxDim * 2.4, 0.5);
  const y = box.min.y;
  const cx = (box.min.x + box.max.x) / 2, cz = (box.min.z + box.max.z) / 2;
  const root = new THREE.Group();
  root.userData.isGround = true;

  // PE（PMXEditor）同款网格：白底、黑色细线
  const grid = new THREE.GridHelper(span, 20, 0x000000, 0x555555);
  grid.position.set(cx, y, cz);
  grid.material.transparent = true;
  grid.material.opacity = 0.8;
  grid.material.depthWrite = false;
  root.add(grid);

  // 红色 X 轴 / 蓝色 Z 轴（PMXEditor 的坐标轴配色）
  const mkAxis = (a, b, color)=>{
    const g = new THREE.BufferGeometry().setFromPoints([a, b]);
    return new THREE.Line(g, new THREE.LineBasicMaterial({color, transparent:true, opacity:0.95}));
  };
  const h = span / 2;
  root.add(mkAxis(new THREE.Vector3(cx-h, y+0.003, cz), new THREE.Vector3(cx+h, y+0.003, cz), 0xcc2222));
  root.add(mkAxis(new THREE.Vector3(cx, y+0.003, cz-h), new THREE.Vector3(cx, y+0.003, cz+h), 0x2244cc));

  // 脚下柔和投影：径向渐变贴片，成本远低于实时阴影，且不受材质/骨架影响
  const cv = document.createElement('canvas'); cv.width = cv.height = 128;
  const g2 = cv.getContext('2d');
  const rg = g2.createRadialGradient(64,64,4,64,64,62);
  rg.addColorStop(0,'rgba(40,44,60,0.34)');
  rg.addColorStop(0.55,'rgba(40,44,60,0.14)');
  rg.addColorStop(1,'rgba(40,44,60,0)');
  g2.fillStyle = rg; g2.fillRect(0,0,128,128);
  const tex = new THREE.CanvasTexture(cv);
  const sh = new THREE.Mesh(
    new THREE.PlaneGeometry(maxDim*1.25, maxDim*1.25),
    new THREE.MeshBasicMaterial({map:tex, transparent:true, depthWrite:false, opacity:0.9}));
  sh.rotation.x = -Math.PI/2;
  sh.position.set(cx, y+0.004, cz);
  sh.renderOrder = -1;
  root.add(sh);

  GROUND = root;
  SC.add(root);
}

/* FBX/Blender 导出的模型常常是 Z 轴朝上（躺着的），立起来才好看 */
function standUp(obj){
  const s = computeBounds(obj).getSize(new THREE.Vector3());
  if(s.z > s.y * 1.25 && s.z > s.x * 0.45){
    obj.rotation.x = -Math.PI / 2;
    obj.updateWorldMatrix(true, true);
    const b = computeBounds(obj);
    obj.position.y -= b.min.y;
    obj.updateWorldMatrix(true, true);
    return true;
  }
  return false;
}

let _loadSeq = 0;       // 连点模型时用序号丢弃过期的加载

async function loadModel(path){
  const seq = ++_loadSeq;     // 本次加载的序号，后面任何一步发现变了就放弃
  const f = S.files.find(x=>x.path===path);
  if(!f) return;
  if(f.size === '0 B'){          // 空文件：直接提示，别让它走到加载器报脚本错误
    if(OBJ) clearModel();
    $('#vTitle').textContent = f.name;
    $('#vBadge').classList.remove('show');
    $('#vFoot').innerHTML = '';
    setHint('这个文件是空的', `${esc(f.name)} · 0 字节`);
    return;
  }
  if(!initGL()) return;

  // 先把模型同目录的资源一次性解出来：后面几十张贴图就不用逐个调 7z 了
  try{
    const pdir = path.includes('/') ? path.slice(0, path.lastIndexOf('/')) : '';
    await post('/api/prefetch', {path:S.cur, dir:pdir, password:S.pwd});
  }catch(e){}
  // prefetch 是异步的，等它回来期间用户可能又点了别的模型 —— 那这次就不要了
  if(seq !== _loadSeq) return;

  curModelPath = S.cur;
  const ext = f.ext;
  const dir = path.includes('/') ? path.slice(0, path.lastIndexOf('/')) : '';
  // 末尾带 &n=文件名：MMDLoader 靠 URL 最后一个 . 判断格式，必须让 URL 以 .pmx 结尾
  const modelURL = `/api/model?path=${enc(S.cur)}&inner=${enc(path)}&password=${enc(S.pwd)}&n=${enc(f.name)}`;

  $('#vTitle').textContent = f.name;
  setHint(`正在加载 ${f.name} …`, '');
  $('#vBadge').classList.remove('show');
  clearModel();
  $('#vFoot').innerHTML = '';
  _faceOrig = null;
  _composed = null;
  _modelInner = path;
  S.faceTex = '';
  S.faceMatIdx = null;

  const mgr = makeManager(dir);
  const onErr = err=>{
    if(seq !== _loadSeq) return;
    console.error(err);
    setHint('加载失败', esc(String((err && (err.message || err.type)) || '文件可能损坏')));
  };
  const onLoad = obj=>{
    // 已经换成别的模型了：把这次加载出来的对象丢掉，不要加进场景
    if(seq !== _loadSeq){
      try{
        obj.traverse(o=>{
          if(o.geometry && o.geometry.dispose) o.geometry.dispose();
          if(o.material){
            (Array.isArray(o.material)?o.material:[o.material]).forEach(m=>{
              if(m.dispose) m.dispose();
            });
          }
        });
      }catch(e){}
      return;
    }
    OBJ = obj;
    // 统一材质：颜色贴图按 sRGB 解释（含自发光贴图），纠正导出常见的 metalness=1 发灰，处理 unlit 模型
    let missingTex = 0;
    obj.traverse(o=>{
      if(!o.material) return;
      (Array.isArray(o.material)?o.material:[o.material]).forEach(m=>{
        if(m.map){ m.map.encoding = THREE.sRGBEncoding; m.needsUpdate = true; }
        if(m.emissiveMap){ m.emissiveMap.encoding = THREE.sRGBEncoding; m.needsUpdate = true; }
        if(m.envMap){ m.envMap.encoding = THREE.sRGBEncoding; m.needsUpdate = true; }
        if(!m.map) missingTex++;
        // MMD 的 ambient 被 MMDLoader 写成了 emissive 常量（加在末尾，会把暗部整体抬灰），
        // 由 normalizeToonMaterial 统一按「中性色清零、彩色保留」处理。
        normalizeToonMaterial(m);   // ambient 语义 + 全白 toon ramp
        refineFaceMaterial(m);
        if(m.isMeshStandardMaterial){
          // 很多 GLB 导出把 metalness 设成 1 又没有环境贴图 → 只剩金属反射=黑/灰，压低回漫反射
          if(!m.metalnessMap && (m.metalness === undefined || m.metalness > 0.9)) m.metalness = 0.1;
          if(!m.roughnessMap && m.roughness > 0.98) m.roughness = 0.82;
          // 纯 unlit（黑底 + 只靠自发光贴图显色）的模型：把自发光贴图当颜色贴图，交给光照与色调映射，避免死白
          if(!m.map && m.emissiveMap && m.color && m.color.getHex() === 0x000000){
            m.map = m.emissiveMap;
            m.color.setRGB(1, 1, 1);
            m.emissive.setRGB(0, 0, 0);
            m.emissiveIntensity = 1;
          }
          m.needsUpdate = true;
        }
        if(m.isMeshPhongMaterial && typeof m.shininess === 'number' && m.shininess > 30){
          m.shininess = 30;   // 高光收一点，避免镜面反光过曝
          m.needsUpdate = true;
        }
        if(!m.map) missingTex++;   // 放在贴图提升之后：真没贴图的材质才算缺
      });
    });
    SC.add(obj);
    // 先渲染一帧，让骨骼矩阵 / 蒙皮变换生效，否则取景会按绑定姿态算错
    R.render(SC, CAM);
    obj.updateWorldMatrix(true, true);
    standUp(obj);
    R.render(SC, CAM);
    fitCamera(obj);
    // 异步贴图/骨骼更新后再校正一次
    setTimeout(()=>{ if(OBJ === obj) fitCamera(obj); }, 150);
    setTimeout(()=>{ if(OBJ === obj) fitCamera(obj); }, 700);
    setHint(null);
    let meshes = 0, verts = 0;
    obj.traverse(o=>{
      if(o.isMesh){
        meshes++;
        if(o.geometry && o.geometry.attributes.position) verts += o.geometry.attributes.position.count;
      }
    });
    $('#vBadge').classList.add('show');
    $('#vBadge').textContent = `${meshes} mesh · ${verts.toLocaleString()} 顶点`;

    // 贴图解码是异步的：改色空间、清 ambient 灰底、换 toon ramp 都要等图片解码完才做得准。
    // 仍然不做任何按名字猜贴图、按几何猜材质组的重绑——那会弄坏文件里本来正确的贴图。
    const refine = ()=>{
      if(OBJ !== obj) return;
      const changed = refineAllMaterials(obj);
      // 贴图解码完后按亮度分布校正曝光（只防高光切白，见 autoExposure）
      if(!obj.userData._expoFixed && S.autoExpo){
        const e = autoExposure(obj);
        if(e != null && R){
          R.toneMappingExposure = e;
          obj.userData._expoFixed = true;
          markDirty();
        }
      }
      if(changed && R && SC && CAM){ R.render(SC, CAM); _dirty = false; }
    };
    [120, 500, 1200, 2400, 4000, 7000, 10000].forEach(ms=>setTimeout(refine, ms));
    // 曝光要等贴图全部解码完才算得准，单独多试几次
    let etries = 0;
    const expoLoop = ()=>{
      if(OBJ !== obj || obj.userData._expoFixed || !S.autoExpo) return;
      refine();
      if(++etries < 10) setTimeout(expoLoop, 800);
    };
    setTimeout(expoLoop, 2600);
    renderViewFoot(f, {meshes, verts, missing: missingTex});
  };

  try{
    if(ext==='.pmx' || ext==='.pmd'){
      const loader = new THREE.MMDLoader(mgr);
      loader.resourcePath = ASSET_TAG;
      loader.load(modelURL, onLoad, undefined, onErr);
    }else if(ext==='.glb' || ext==='.gltf'){
      new THREE.GLTFLoader(mgr).load(modelURL, g=>onLoad(g.scene || g.scenes[0]), undefined, onErr);
    }else if(ext==='.fbx'){
      new THREE.FBXLoader(mgr).load(modelURL, onLoad, undefined, onErr);
    }else if(ext==='.obj'){
      const mtlPath = path.replace(/\.obj$/i, '.mtl');
      const hasMtl = S.files.some(x=>x.path.toLowerCase()===mtlPath.toLowerCase());
      const loadObj = mats=>{
        const loader = new THREE.OBJLoader(mgr);
        if(mats) loader.setMaterials(mats);
        loader.load(modelURL, onLoad, undefined, onErr);
      };
      if(hasMtl){
        new THREE.MTLLoader(mgr).load(
          `/api/asset?path=${enc(S.cur)}&password=${enc(S.pwd)}&base=${enc(dir)}&rel=${enc(mtlPath)}`,
          m=>{ m.preload(); loadObj(m); }, undefined, ()=>loadObj(null));
      }else loadObj(null);
    }else{
      // 给出能落地的下一步，而不是只说「不支持」
      const advice = {
        '.blend': 'Blender 工程文件（可能是 zstd 压缩的）· 在 Blender 里导出 glb/fbx 再打包',
        '.zprj': 'Marvelous Designer 工程 · 在 MD 里导出 obj/fbx 再打包',
        '.uemodel': 'UEFORMAT 网格 · 需要专门解析器，或用 Blender 插件转 glb',
        '.dae': 'Collada · 用 Blender 转成 glb 再打包',
        '.stl': '只有三角面、没有材质贴图 · 用 Blender 转 glb 再打包',
      }[ext] || '建议导出成 glb / fbx / pmx 再打包';
      setHint('这个格式暂不支持内嵌预览', `${esc(ext)} · ${esc(advice)}`);
    }
  }catch(e){ onErr(e); }
}

function renderViewFoot(f, stats){
  const sibs = S.files.filter(x=>x.is_image &&
    (x.path.includes('/') ? x.path.slice(0,x.path.lastIndexOf('/')) : '') ===
    (f.path.includes('/') ? f.path.slice(0,f.path.lastIndexOf('/')) : ''));

  // 外部程序入口：和 PMXEditor 同一个位置（第一个按钮）。配置了 .pmx 就用那个程序，
  // 没配则退回内置的 PMXEditor 路径。
  const opPath = (S.openers && S.openers[f.ext]) || '';
  const opName = opPath ? ((opPath.split(/[\\/]/).pop() || '外部程序').replace(/\.(exe|bat|cmd)$/i, '')) : '';
  let extBtn = '';
  if(opPath) extBtn = `<button class="fbtn" id="vOpenExt">用 ${esc(opName)} 打开</button>`;
  else if(f.is_pmx) extBtn = `<button class="fbtn" id="vEdit">PMXEditor</button>`;
  let h = `<div class="vrow">
    ${extBtn}
    <button class="fbtn" id="vReset">重置视角</button>
    <button class="fbtn" id="vSpin">自动旋转</button>
    <button class="fbtn ${S.mouseMode==='alt'?'on':''}" id="vMouse" title="切换鼠标操作：默认=左键旋转/右键平移；右键旋转=右键旋转/左键平移">鼠标:${S.mouseMode==='alt'?'右键旋转':'默认'}</button>
    <button class="fbtn" id="vDiag" title="打印当前模型的材质/光照状态">诊断</button>
    <button class="fbtn" id="vDownload">下载</button>
  </div>
  <div class="lightrow">
    <label>光照</label>
    <input type="range" id="lightSlider" min="0.2" max="2" step="0.05" value="${S.light}">
    <span id="lightVal">${S.light.toFixed(2)}×</span>
    <label class="chk" title="光照颜色：给所有灯上色（整体偏暖/偏冷）">颜色</label>
    <input type="color" id="lightColor" value="${S.lightColor || '#ffffff'}"
           style="width:28px;height:22px;padding:0;border:1px solid var(--line2);border-radius:5px;background:#fff;cursor:pointer">
  </div>`;

  h += `<div class="vkv">
    <div class="k">文件</div><div class="v">${esc(f.name)}</div>
    <div class="k">格式</div><div class="v">${esc(f.ext.replace('.','').toUpperCase())} · ${f.size}</div>
    <div class="k">网格</div><div class="v">${stats.meshes} 个 · ${stats.verts.toLocaleString()} 顶点</div>
    ${stats.missing ? `<div class="k">贴图</div><div class="v" style="color:#c2410c">${stats.missing} 个材质无贴图</div>` : ''}
  </div>`;

  if(sibs.length){
    h += `<div class="vlabel">同目录贴图（${sibs.length}）</div><div class="tgrid">`;
    h += sibs.slice(0,48).map(s=>{
      const b = `path=${enc(S.cur)}&inner=${enc(s.path)}&password=${enc(S.pwd)}`;
      return `<div class="t" data-lb="${esc(s.path)}"><img loading="lazy" src="/api/thumb?${b}"
        onerror="this.style.visibility='hidden'"></div>`;
    }).join('');
    h += `</div>`;
  }
  $('#vFoot').innerHTML = h;

  if($('#vOpenExt')) $('#vOpenExt').onclick = ()=>openExternal(f);
  if(f.is_pmx && $('#vEdit')) $('#vEdit').onclick = ()=>openEditor(f.path);
  $('#vReset').onclick = ()=>{ if(OBJ) fitCamera(OBJ); };
  $('#vSpin').onclick = ev=>{
    CTL.autoRotate = !CTL.autoRotate;
    CTL.autoRotateSpeed = 1.6;
    ev.currentTarget.classList.toggle('on', CTL.autoRotate);
  };
  if($('#vMouse')) $('#vMouse').onclick = ()=>{
    S.mouseMode = S.mouseMode==='alt' ? 'default' : 'alt';
    applyMouseMode();
    $('#vMouse').textContent = '鼠标:' + (S.mouseMode==='alt' ? '右键旋转' : '默认');
    $('#vMouse').classList.toggle('on', S.mouseMode==='alt');
  };
  $('#vDownload').onclick = ()=>download(f.path);
  if($('#vDiag')) $('#vDiag').onclick = ()=>{
    const lines = [];
    let nmat = 0, ntoon = 0, gmOk = 0, gmNo = 0, withMap = 0, withEmis = 0;
    if(OBJ) OBJ.traverse(o=>{
      if(!o.material) return;
      (Array.isArray(o.material)?o.material:[o.material]).forEach(m=>{
        nmat++;
        if(m.map) withMap++;
        if(m.emissive && (m.emissive.r || m.emissive.g || m.emissive.b)) withEmis++;
        if(!m.isMeshToonMaterial) return;
        ntoon++;
        const im = m.gradientMap && m.gradientMap.image;
        if(im && im.width) gmOk++; else gmNo++;
      });
    });
    lines.push('材质 ' + nmat + ' · toon ' + ntoon + ' · 有贴图 ' + withMap + ' · 有 emissive ' + withEmis);
    lines.push('toon 贴图：已解码 ' + gmOk + ' / 未解码 ' + gmNo);
    lines.push('光照 ' + S.light.toFixed(2) + '× ' + (S.lightColor || '#ffffff') +
               ' · 曝光 ' + (R ? R.toneMappingExposure.toFixed(2) : '-'));
    lines.push('物体 ' + (OBJ ? (OBJ.type + ' 子节点 ' + OBJ.children.length) : '无'));
    dialog('<h3>诊断</h3><div class="body"><pre style="white-space:pre-wrap;font-size:12px;line-height:1.7">'
      + esc(lines.join('\n')) + '</pre></div><div class="foot"><button class="fbtn solid" id="dgOk">好</button></div>',
      ()=>{ $('#dgOk').onclick = closeDialog; });
  };
  $('#lightSlider').oninput = ev=>{
    S.light = parseFloat(ev.target.value);
    $('#lightVal').textContent = S.light.toFixed(2) + '×';
    applyLightLevel();
  };
  if($('#autoExpo')) $('#autoExpo').onchange = ev=>{
    S.autoExpo = ev.target.checked;
    try{ localStorage.setItem('zipview.autoExpo', S.autoExpo ? '1' : '0'); }catch(e){}
    if(!R) return;
    if(!S.autoExpo){
      R.toneMappingExposure = 1.0;
      if(OBJ) OBJ.userData._expoFixed = false;
      return;
    }
    if(OBJ){
      const e = autoExposure(OBJ);
      if(e != null){ R.toneMappingExposure = e; OBJ.userData._expoFixed = true; }
    }
    if(SC && CAM) R.render(SC, CAM);
  };
  if($('#lightColor')) $('#lightColor').oninput = ev=>{
    S.lightColor = ev.target.value || '#ffffff';
    try{ localStorage.setItem('zipview.lightColor', S.lightColor); }catch(e){}
    applyLightLevel();
  };
  $$('#vFoot [data-lb]').forEach(el=>el.onclick = ()=>openLb(el.dataset.lb));
}

/* ---------- 外置面部表情贴图 ---------- */
let _faceOrig = null;
let _modelInner = '';

/* 游戏导出的角色常把「脸」做成：map=纯黑底 / emissiveMap=真正的脸。
   emissive 为黑时自发光贴图不显示 → 黑脸；为白时又叠加发白。
   统一把自发光贴图提为颜色贴图交给正常光照。贴图可能稍后才解码完，所以可重复调用。 */
function refineFaceMaterial(m){
  if(!m || !m.emissiveMap) return false;
  if(m.userData && m.userData._flatFace) return false;   // 已经合成好的脸，别再动
  if(!(m.isMeshStandardMaterial || m.isMeshPhongMaterial)) return false;
  // 只在「颜色贴图缺失或近乎纯黑」时才把自发光贴图提上来，不按材质名猜
  if(m.map && !isDarkTexture(m.map)) return false;
  m.map = m.emissiveMap;
  m.emissiveMap = null;
  m.emissive.setRGB(0, 0, 0);
  m.emissiveIntensity = 1;
  m.color.setRGB(1, 1, 1);
  m.needsUpdate = true;
  return true;
}

function refineAllMaterials(obj){
  let n = 0;
  obj.traverse(o=>{
    if(!o.material) return;
    (Array.isArray(o.material) ? o.material : [o.material]).forEach(m=>{
      if(refineFaceMaterial(m)) n++;
      if(normalizeToonMaterial(m)) n++;
    });
  });
  return n;
}

/* 判断贴图是否近乎纯黑（游戏导出的脸部材质常用黑底占位） */
function isDarkTexture(tex){
  try{
    const im = tex && tex.image;
    if(!im) return false;
    const w = im.width || im.videoWidth, h = im.height || im.videoHeight;
    if(!w || !h) return false;
    const cv = document.createElement('canvas');
    cv.width = cv.height = 24;
    const cx = cv.getContext('2d', {willReadFrequently:true});
    cx.drawImage(im, 0, 0, 24, 24);
    const d = cx.getImageData(0, 0, 24, 24).data;
    let sum = 0, n = 0;
    for(let i = 0; i < d.length; i += 16){ sum += (d[i] + d[i+1] + d[i+2]) / 3; n++; }
    return sum / Math.max(1, n) < 26;
  }catch(e){ return false; }
}

function faceCandidates(){
  // 表情图集（bq1/bq2/bq3 之类）不是完整脸，优先级放后面；bq0 / 无编号的优先
  const all = S.files.filter(f=>f.is_image && /face/i.test(f.name) &&
                                !/mask|normal|bump/i.test(f.name));
  const score = f => {
    const n = f.name.toLowerCase();
    if(/atlas|sheet|set|bq[1-9]|exp/i.test(n)) return 2;
    if(/bq0|face\./i.test(n)) return 0;
    return 1;
  };
  return all.sort((a,b)=>score(a)-score(b) || a.name.length-b.name.length);
}

function faceMaterials(){
  const out = [];
  if(!OBJ) return out;
  OBJ.traverse(o=>{
    if(!o.isMesh) return;
    (Array.isArray(o.material)?o.material:[o.material]).forEach(m=>{
      if(/face/i.test(m.name||'')) out.push(m);
    });
  });
  // FBX 材质常叫 Default-Material，用几何推断出的脸部材质组兜底
  if(!out.length && S.faceMatIdx != null){
    OBJ.traverse(o=>{
      if(!o.isMesh || !Array.isArray(o.material)) return;
      const m = o.material[S.faceMatIdx];
      if(m && !out.includes(m)) out.push(m);
    });
  }
  return out;
}
function hasFaceMaterial(){ return faceMaterials().length > 0; }

async function applyFaceTexture(path){
  const mats = faceMaterials();
  if(!mats.length) return;
  if(!_faceOrig){
    _faceOrig = mats.map(m=>({m, map:m.emissiveMap, em:m.emissive.clone(), it:m.emissiveIntensity}));
  }
  if(!path){
    _faceOrig.forEach(x=>{
      x.m.emissiveMap = x.map;
      x.m.emissive.copy(x.em);
      x.m.emissiveIntensity = x.it;
      x.m.needsUpdate = true;
    });
    return;
  }
  if(path === '@compose'){
    const tex = await getComposedFace(mats[0]);
    if(!tex) return false;
    mats.forEach(m=>{
      m.map = tex;
      if(m.emissive && m.emissiveMap !== undefined){
        // 不加自发光：亮度已经烘进合成贴图，脸和身体走同一套光照
        m.emissiveMap = null;
        m.emissive.setRGB(0,0,0);
        m.emissiveIntensity = 1;
        m.color.setRGB(1,1,1);
      }else{
        m.color.setRGB(1,1,1);
      }
      if('metalness' in m) m.metalness = 0;
      if('roughness' in m) m.roughness = 1;
      m.userData = m.userData || {};
      m.userData._flatFace = true;
      m.needsUpdate = true;
    });
    return true;
  }
  try{
    const tex = await new Promise((res, rej)=>{
      new THREE.TextureLoader().load(assetURL('', path), res, undefined, rej);
    });
    if('sRGBEncoding' in THREE) tex.encoding = THREE.sRGBEncoding;
    mats.forEach(m=>{
      m.emissiveMap = tex;
      m.emissive.setRGB(1,1,1);
      m.emissiveIntensity = 1;
      m.needsUpdate = true;
    });
  }catch(e){ console.warn('面部贴图加载失败', e); }
  return false;
}

/* ---------- 用「底妆 + 眼睛图集 + 嘴部图集」重建整张脸 ----------
   这类游戏模型（DtDog 等）把一张脸拆成几张图导出：
     *Face_bq0  底妆：肤色、腮红、鼻影，没有瞳孔和嘴，不透明
     *Face_bq1  眼睛图集：带 alpha，一格一对眼（多种表情）
     *Face_bq2  嘴部图集：带 alpha
   导出 GLB/FBX 时脸部材质常被绑成其中一张图集（甚至绑成嘴图集），
   于是整张脸发白、没有五官。这里切出精灵，按底妆上的眼线痕迹定位后合成一张完整脸。 */
let _composed = null;

function loadImgEl(url){
  return new Promise((res, rej)=>{
    const im = new Image();
    im.onload = ()=>res(im);
    im.onerror = ()=>rej(new Error('image load failed'));
    im.src = url;
  });
}

/* 缩小统计：透明占比 tr、近白占比 wh（图集白底很高） */
function texStats(im){
  const N = 64;
  const cv = document.createElement('canvas');
  cv.width = cv.height = N;
  const cx = cv.getContext('2d', {willReadFrequently:true});
  try{ cx.drawImage(im, 0, 0, N, N); }catch(e){ return {w:0,h:0,tr:0,wh:0}; }
  const d = cx.getImageData(0, 0, N, N).data;
  let tr = 0, wh = 0;
  for(let i = 0; i < d.length; i += 4){
    if(d[i+3] < 24){ tr++; continue; }
    if(d[i] > 232 && d[i+1] > 226 && d[i+2] > 230) wh++;
  }
  const n = N * N;
  return {w: im.naturalWidth || im.width, h: im.naturalHeight || im.height, tr: tr/n, wh: wh/n};
}

/* 用 alpha 投影把图集切成行带 / 列带 */
function alphaBands(im){
  const W = im.naturalWidth || im.width, H = im.naturalHeight || im.height;
  const s = Math.min(1, 900 / Math.max(W, H));
  const w = Math.max(2, Math.round(W*s)), h = Math.max(2, Math.round(H*s));
  const cv = document.createElement('canvas'); cv.width = w; cv.height = h;
  const cx = cv.getContext('2d', {willReadFrequently:true});
  cx.drawImage(im, 0, 0, w, h);
  const d = cx.getImageData(0, 0, w, h).data;
  const rh = new Uint8Array(h), chh = new Uint8Array(w);
  for(let y = 0; y < h; y++){
    const off = y*w*4;
    for(let x = 0; x < w; x++){
      if(d[off + x*4 + 3] > 30){ rh[y] = 1; chh[x] = 1; }
    }
  }
  const pick = (hit, sc)=>{
    const out = []; let st = -1;
    for(let i = 0; i <= hit.length; i++){
      const v = i < hit.length ? hit[i] : 0;
      if(v && st < 0) st = i;
      else if(!v && st >= 0){
        if(i - st >= 2) out.push([Math.round(st/sc), Math.round(i/sc)]);
        st = -1;
      }
    }
    return out;
  };
  return {rows: pick(rh, s), cols: pick(chh, s)};
}

/* 在给定矩形里求 alpha 的紧致包围盒（原图坐标） */
function tightAlphaBox(im, box){
  const W = im.naturalWidth || im.width, H = im.naturalHeight || im.height;
  const x0 = Math.max(0, box[0]), y0 = Math.max(0, box[1]);
  const x1 = Math.min(W, box[2]), y1 = Math.min(H, box[3]);
  const bw = x1 - x0, bh = y1 - y0;
  if(bw < 2 || bh < 2) return null;
  const s = Math.min(1, 256 / Math.max(bw, bh));
  const w = Math.max(2, Math.round(bw*s)), h = Math.max(2, Math.round(bh*s));
  const cv = document.createElement('canvas'); cv.width = w; cv.height = h;
  const cx = cv.getContext('2d', {willReadFrequently:true});
  cx.drawImage(im, x0, y0, bw, bh, 0, 0, w, h);
  const d = cx.getImageData(0, 0, w, h).data;
  let ax = 1e9, ay = 1e9, bx = -1, by = -1;
  for(let y = 0; y < h; y++){
    for(let x = 0; x < w; x++){
      if(d[(y*w + x)*4 + 3] > 30){
        if(x < ax) ax = x; if(x > bx) bx = x;
        if(y < ay) ay = y; if(y > by) by = y;
      }
    }
  }
  if(bx < 0) return null;
  return [x0 + ax/s, y0 + ay/s, x0 + (bx + 1)/s, y0 + (by + 1)/s];
}

/* 给定矩形内，按 alpha 投影切出上下分离的几块（用于把眉毛和眼睛拆开） */
function alphaRowBands(im, box){
  const W = im.naturalWidth || im.width, H = im.naturalHeight || im.height;
  const x0 = Math.max(0, Math.round(box[0])), y0 = Math.max(0, Math.round(box[1]));
  const x1 = Math.min(W, Math.round(box[2])), y1 = Math.min(H, Math.round(box[3]));
  const bw = x1 - x0, bh = y1 - y0;
  if(bw < 2 || bh < 4) return [];
  const cv = document.createElement('canvas'); cv.width = bw; cv.height = bh;
  const cx = cv.getContext('2d', {willReadFrequently:true});
  cx.drawImage(im, x0, y0, bw, bh, 0, 0, bw, bh);
  const d = cx.getImageData(0, 0, bw, bh).data;
  const hit = new Uint8Array(bh);
  for(let y = 0; y < bh; y++){
    for(let x = 0; x < bw; x++){
      if(d[(y*bw + x)*4 + 3] > 30){ hit[y] = 1; break; }
    }
  }
  const out = []; let st = -1;
  for(let i = 0; i <= bh; i++){
    const v = i < bh ? hit[i] : 0;
    if(v && st < 0) st = i;
    else if(!v && st >= 0){
      if(i - st >= 3) out.push([y0 + st, y0 + i]);
      st = -1;
    }
  }
  return out;
}

/* 精灵里「白眼球」占比：越高说明眼睛睁得越开，适合当默认表情 */
function eyeOpenScore(im, box){
  const bw = box[2] - box[0], bh = box[3] - box[1];
  if(bw < 4 || bh < 2) return 0;
  const w = Math.min(160, Math.max(8, Math.round(bw)));
  const h = Math.max(4, Math.round(w * bh / bw));
  const cv = document.createElement('canvas'); cv.width = w; cv.height = h;
  const cx = cv.getContext('2d', {willReadFrequently:true});
  cx.drawImage(im, box[0], box[1], bw, bh, 0, 0, w, h);
  const d = cx.getImageData(0, 0, w, h).data;
  let tot = 0, wh = 0;
  for(let i = 0; i < d.length; i += 4){
    if(d[i+3] < 40) continue;
    tot++;
    if(d[i] > 198 && d[i+1] > 190 && d[i+2] > 200) wh++;
  }
  return tot ? wh / tot : 0;
}

/* 底妆上的淡紫眼线 = 五官位置的锚点；同时返回左右眼的包围盒，方便合成时把它抹掉 */
function eyeAnchor(im){
  const W = im.naturalWidth || im.width, H = im.naturalHeight || im.height;
  const s = Math.min(1, 512 / Math.max(W, H));
  const w = Math.max(2, Math.round(W*s)), h = Math.max(2, Math.round(H*s));
  const cv = document.createElement('canvas'); cv.width = w; cv.height = h;
  const cx = cv.getContext('2d', {willReadFrequently:true});
  cx.drawImage(im, 0, 0, w, h);
  const d = cx.getImageData(0, 0, w, h).data;
  const xs = [], ys = [];
  for(let y = 0; y < h; y++){
    for(let x = 0; x < w; x++){
      const i = (y*w + x)*4;
      const R = d[i], G = d[i+1], B2 = d[i+2], A = d[i+3];
      if(A > 60 && B2 > R + 16 && B2 > G + 6 && B2 > 100){ xs.push(x); ys.push(y); }
    }
  }
  if(xs.length < 30) return null;
  let lo = 1e9, hi = -1;
  for(const x of xs){ if(x < lo) lo = x; if(x > hi) hi = x; }
  const mid = (lo + hi) / 2;
  const part = (a, b)=>{
    const px = [], py = [];
    for(let k = 0; k < xs.length; k++) if(xs[k] >= a && xs[k] < b){ px.push(xs[k]); py.push(ys[k]); }
    if(px.length < 8) return null;
    return {
      cx: (px.reduce((u,v)=>u+v,0)/px.length)/w,
      cy: (py.reduce((u,v)=>u+v,0)/py.length)/h,
      box: [Math.min(...px)/w, Math.min(...py)/h, (Math.max(...px)+1)/w, (Math.max(...py)+1)/h]
    };
  };
  const L = part(-1, mid), Rg = part(mid, 1e9);
  if(!L || !Rg) return null;
  return {L, R: Rg};
}

async function composeFaceTexture(flipY){
  const topOf = p => p.includes('/') ? p.slice(0, p.indexOf('/')) : '';
  const modelTop = topOf(_modelInner || '');
  const cands = S.files.filter(f=>f.is_image && /face|顔|脸/i.test(f.name) &&
                                  !/mask|normal|bump|ao|matcap|toon/i.test(f.name) &&
                                  (!modelTop || topOf(f.path) === modelTop));
  if(cands.length < 2) return null;
  const loaded = [];
  for(const f of cands.slice(0, 10)){
    try{
      const im = await loadImgEl(assetURL('', f.path));
      loaded.push({f, im, st: texStats(im)});
    }catch(e){}
  }
  const opaque = loaded.filter(x=>x.st.tr < 0.02);
  const atlas  = loaded.filter(x=>x.st.tr >= 0.02);
  if(!opaque.length || !atlas.length) return null;
  opaque.sort((a,b)=>a.st.wh - b.st.wh);
  const base = opaque[0];
  atlas.sort((a,b)=>(b.st.w*b.st.h) - (a.st.w*a.st.h));
  const eyeSet = atlas[0];
  const mouthSet = atlas.length > 1 ? atlas[1] : null;

  // 眼睛精灵：优先用第一行（通常就是默认表情），第一行明显不够「睁眼」时再看后面的行
  const eb = alphaBands(eyeSet.im);
  if(!eb.rows.length || !eb.cols.length) return null;
  let best = null, bestScore = -1, firstRowBest = null, firstRowScore = -1;
  const maxRows = Math.min(eb.rows.length, 8);
  for(let ri = 0; ri < maxRows; ri++){
    const row = eb.rows[ri];
    for(let i = 0; i < eb.cols.length; i++){
      const c0 = eb.cols[i], c1 = eb.cols[i+1];
      const wide = c0[1] - c0[0];
      let box;
      if(c1 && c1[0] - c0[1] < wide * 0.9){
        box = [c0[0], row[0], c1[1], row[1]];   // 相邻两只合成「一对眼」
        i++;                                     // 已经用掉 c1，别再把单只眼当候选
      }else{
        continue;                                // 落单的单个眼睛不参与
      }
      const tb = tightAlphaBox(eyeSet.im, [box[0]-6, box[1]-6, box[2]+7, box[3]+7]);
      if(!tb) continue;
      const sc = eyeOpenScore(eyeSet.im, tb);
      if(ri === 0 && sc > firstRowScore){ firstRowScore = sc; firstRowBest = tb; }
      if(sc > bestScore){ bestScore = sc; best = tb; }
    }
  }
  if(!best) return null;

  // 左右各留一点余量，避免睫毛尖被切平（不做上下切分：图集里眉毛和眼睛常连成一体，
  // 按行带硬切会把整条睫毛带当成眼睛，脸上出现一条黑条）
  {
    const padX = Math.max(1, Math.round((best[2]-best[0]) * 0.03));
    best = [Math.max(0, best[0]-padX), best[1], best[2]+padX, best[3]];
  }

  // 嘴：在所有精灵里挑一个形态最「正常」的（宽高比接近 0.3 的闭合小嘴）
  let mBox = null;
  if(mouthSet){
    const mb = alphaBands(mouthSet.im);
    let mBest = null, mScore = 1e9, maxW = 1;
    const boxes = [];
    for(let ri = 0; ri < Math.min(mb.rows.length, 8); ri++){
      for(let ci = 0; ci < mb.cols.length; ci++){
        const r = mb.rows[ri], c = mb.cols[ci];
        const tb = tightAlphaBox(mouthSet.im, [c[0]-4, r[0]-4, c[1]+5, r[1]+5]);
        if(!tb) continue;
        boxes.push(tb);
        maxW = Math.max(maxW, tb[2]-tb[0]);
      }
    }
    for(const tb of boxes){
      const w = tb[2]-tb[0], h = tb[3]-tb[1];
      if(w < maxW * 0.55) continue;                 // 太小的多半是被切碎的
      const ar = h / Math.max(1, w);
      if(ar < 0.08 || ar > 0.8) continue;
      const sc = Math.abs(ar - 0.30);
      if(sc < mScore){ mScore = sc; mBest = tb; }
    }
    mBox = mBest;
  }

  const N = 1024;
  const cv = document.createElement('canvas');
  cv.width = cv.height = N;
  const cx = cv.getContext('2d');
  cx.imageSmoothingEnabled = true;
  cx.imageSmoothingQuality = 'high';
  cx.drawImage(base.im, 0, 0, N, N);

  const anc = eyeAnchor(base.im);
  const eyeCx = anc ? (anc.L.cx + anc.R.cx) / 2 : 0.5;
  // 底妆上那两道眼线比实际眼睛位置偏低一点，抬高 0.065 才是自然的眼睛高度
  const eyeCy = (anc ? anc.L.cy : 0.545) - 0.065;
  const span  = anc ? (anc.R.cx - anc.L.cx) : 0.394;

  // 先把底妆上残留的淡紫眼线抹掉，否则会留在眼睛下方变成紫色小点
  if(anc){
    const erase = b=>{
      const bx = b.box;
      const sx = Math.round(((bx[0] + bx[2]) / 2) * N);
      const sy = Math.min(N - 2, Math.round((bx[3] + 0.015) * N));
      let col = 'rgb(246,228,226)';
      try{
        const d = cx.getImageData(sx, sy, 1, 1).data;
        if(d[3] > 40) col = `rgb(${d[0]},${d[1]},${d[2]})`;
      }catch(e){}
      const pad = Math.round(0.008 * N);
      cx.save();
      cx.filter = 'blur(4px)';
      cx.fillStyle = col;
      cx.fillRect(bx[0]*N - pad, bx[1]*N - pad,
                  (bx[2]-bx[0])*N + pad*2, (bx[3]-bx[1])*N + pad*2);
      cx.restore();
    };
    erase(anc.L); erase(anc.R);
  }

  const ew = Math.min(0.62 * N, Math.max(0.20 * N, span * 1.35 * N));
  const eh = ew * (best[3]-best[1]) / Math.max(1, best[2]-best[0]);
  cx.drawImage(eyeSet.im, best[0], best[1], best[2]-best[0], best[3]-best[1],
               eyeCx*N - ew/2, eyeCy*N - eh/2, ew, eh);

  if(mBox){
    const mw = 0.109 * N;
    const mh = Math.max(4, mw * (mBox[3]-mBox[1]) / Math.max(1, mBox[2]-mBox[0]));
    const my = ((anc ? anc.L.cy : 0.545) + 0.145) * N;
    cx.drawImage(mouthSet.im, mBox[0], mBox[1], mBox[2]-mBox[0], mBox[3]-mBox[1],
                 eyeCx*N - mw/2, my - mh/2, mw, mh);
  }

  // 底妆本身已经很浅（接近 246,228,226），再提亮就会过曝成「白模」，
  // 所以这里不再做亮度增益：脸和身体走同一套光照，稍微暗一点也比白脸自然
  const tex = new THREE.CanvasTexture(cv);
  if('sRGBEncoding' in THREE) tex.encoding = THREE.sRGBEncoding;
  tex.flipY = !!flipY;
  tex.anisotropy = 8;
  tex.needsUpdate = true;
  return tex;
}

async function getComposedFace(mat){
  const flipY = (mat && mat.map) ? mat.map.flipY : false;
  if(_composed && _composed.flipY === flipY) return _composed.tex;
  const tex = await composeFaceTexture(flipY);
  if(tex) _composed = {tex, flipY};
  return tex;
}

/* 脸部贴图里到底有没有五官：睫毛/瞳孔是深色，纯底妆几乎没有深色像素 */
function faceHasFeatures(im){
  const N2 = 96;
  const cv = document.createElement('canvas');
  cv.width = cv.height = N2;
  const cx = cv.getContext('2d', {willReadFrequently:true});
  try{ cx.drawImage(im, 0, 0, N2, N2); }catch(e){ return true; }
  const d = cx.getImageData(0, 0, N2, N2).data;
  let n = 0, dark = 0;
  for(let i = 0; i < d.length; i += 4){
    if(d[i+3] < 40) continue;
    n++;
    if(d[i]*0.299 + d[i+1]*0.587 + d[i+2]*0.114 < 110) dark++;
  }
  return n > 50 ? (dark / n) > 0.002 : false;
}

/* 脸需不需要重建：没贴图 / 绑成了白底图集 / 只有底妆没有五官。
   真正的把关在 composeFaceTexture 里——找不到「底妆 + 带 alpha 的眼睛图集」
   这一对素材时它返回 null，所以没有拆脸素材的模型不会被瞎改。 */
function faceNeedsCompose(){
  const fm = faceMaterials();
  if(!fm.length) return false;
  for(const m of fm){
    if(m.userData && m.userData._flatFace) return false;
    if(!m.map && !m.emissiveMap) return true;
    const im = (m.map && m.map.image) || (m.emissiveMap && m.emissiveMap.image);
    if(!im || !im.width || im.width < 8) return false;   // 还没解码完，下一轮再看
    const st = texStats(im);
    if(st.tr > 0.9) return true;                          // 整张全透明（导出时五官层被剥掉了）
    if(st.wh > 0.5) return true;                          // 白底图集
    if(!faceHasFeatures(im)) return true;                 // 只有底妆
  }
  return false;
}

/* 从同目录贴图里按名字挑一张“颜色图”（排除 mask/法线/特效/球面图） */
function pickTexFor(key){
  const keyl = (key||'').replace(/\.[^.]+$/,'').trim().toLowerCase();
  if(!keyl) return null;
  const cands = [];
  for(const f of S.files){
    if(!f.is_image || f.ext==='.dds') continue;
    const base = f.name.replace(/\.[^.]+$/,'').toLowerCase();
    // 实际素材常带编号前缀（4516_3_Face_bq0），所以也接受「词内包含」
    if(base===keyl || base.startsWith(keyl+'_') || base.endsWith('_'+keyl) ||
       keyl.startsWith(base+'_') || base.includes(keyl)){
      cands.push({f, base});
    }
  }
  if(!cands.length) return null;
  // 表情图集 / 差分不是完整贴图，优先排除
  const isColor = b => !/(^|_)(mask|fx|dissolve|bump|normal|ao|alpha|diffuse|sp|toon|matcap|atlas|sheet|set)(_|$)/i.test(b)
                    && !/bq[1-9]/i.test(b);
  let pool = cands.filter(x=>isColor(x.base));
  if(!pool.length) pool = cands;
  pool.sort((a,b)=>{
    const ax = a.base===keyl, bx = b.base===keyl;
    if(ax!==bx) return ax ? -1 : 1;
    const ap = /\.(png|jpe?g)$/i.test(a.f.name), bp = /\.(png|jpe?g)$/i.test(b.f.name);
    if(ap!==bp) return ap ? -1 : 1;
    return a.base.length - b.base.length;
  });
  return pool[0].f.path;
}

/* 从几何分组里推断「脸部」材质组：
   取跨度最大的轴当高度轴（FBX 常是 Z-up 躺着导入，standUp 只旋转对象不改几何），
   头部 = 高度轴最上端的组；同样靠上时优先顶点数少的那个（脸比头发/身体小）。 */
function guessFaceGroup(mesh, fallback){
  const g = mesh.geometry;
  if(!g || !g.groups || !g.groups.length) return fallback;
  if(!g.boundingBox) g.computeBoundingBox();
  const box = g.boundingBox, sz = new THREE.Vector3();
  box.getSize(sz);
  const zUp = sz.z > sz.y * 1.15;
  const lo = zUp ? box.min.z : box.min.y, hi = zUp ? box.max.z : box.max.y;
  const H = Math.max(1e-6, hi - lo);
  const pos = g.attributes.position, idx = g.index;
  let best = fallback, bestScore = Infinity;
  for(const gr of g.groups){
    if(gr.materialIndex == null) continue;
    let sum = 0, n = 0;
    const end = Math.min(gr.start + gr.count, idx ? idx.count : pos.count);
    const step = Math.max(1, Math.floor(gr.count / 300));
    for(let i = gr.start; i < end; i += step){
      const j = idx ? idx.getX(i) : i;
      sum += zUp ? pos.getZ(j) : pos.getY(j);
      n++;
    }
    const rel = ((sum / Math.max(1, n)) - lo) / H;
    const score = Math.abs(1 - rel) * 2 + Math.min(1, gr.count / 30000);
    if(score < bestScore){ bestScore = score; best = gr.materialIndex; }
  }
  return best;
}

/* FBX/OBJ 修正贴图绑定：
   有的模型材质全叫 Default-Material 且没有贴图，需要按网格名补；
   有的（DtDog）所有材质都错误地指向同一张 Body 贴图，需要按材质分组重新分配到
   Face / Hair / 其它部件贴图。两种情况分别处理。 */
function autoBindTextures(allowShared){
  if(!OBJ) return false;
  const loader = new THREE.TextureLoader();
  let acted = false;
  const apply = (m, path)=>{
    const url = assetURL('', path);
    loader.load(url, t=>{
      if('sRGBEncoding' in THREE) t.encoding = THREE.sRGBEncoding;
      t.anisotropy = 4;
      m.map = t;
      m.needsUpdate = true;
      if(R && SC && CAM) R.render(SC, CAM);
    }, undefined, ()=>{});
  };

  OBJ.traverse(o=>{
    if(!o.isMesh || !o.material) return;
    const mats = Array.isArray(o.material) ? o.material : [o.material];

    // 情况 1：所有材质共用同一张贴图（FBX 贴图路径丢失后的典型症状）
    const srcs = mats.map(m => (m.map && m.map.image && m.map.image.src) || '');
    const uniq = [...new Set(srcs.filter(Boolean))];
    if(allowShared && mats.length > 1 && uniq.length === 1){
      const wantFace = pickTexFor('Face');
      const wantHair = pickTexFor('Hair');
      if(wantFace){
        const faceIdx = guessFaceGroup(o, mats.length - 1);
        S.faceMatIdx = faceIdx;
        const m = mats[faceIdx];
        if(m){ apply(m, wantFace); acted = true; }
      }
      if(wantHair && !acted){
        // 没有脸部贴图时，至少把头发从「全用 Body」里拆出来
        const m = mats[1];
        if(m){ apply(m, wantHair); acted = true; }
      }
      return;
    }

    // 情况 2：有材质完全没贴图，按网格名补
    if(mats.every(m=>m.map)) return;
    let key = o.name || (o.geometry && o.geometry.name) || '';
    if(!key){
      const mn = mats.map(m=>m.name).find(n=>n && !/default/i.test(n));
      key = mn || '';
    }
    const texPath = pickTexFor(key);
    if(!texPath) return;
    mats.forEach(m=>{
      if(m.map) return;
      apply(m, texPath);
      acted = true;
    });
  });
  return acted;
}

async function openEditor(inner){
  const d = await post('/api/open-editor', {path:S.cur, inner, password:S.pwd});
  if(d.error) alert('打开失败：' + d.error);
}

/* ===================== 大图 ===================== */
function openLb(path){
  S.lbIdx = S.lbList.indexOf(path);
  if(S.lbIdx < 0){ S.lbList = [path]; S.lbIdx = 0; }
  showLb();
}
function showLb(){
  const p = S.lbList[S.lbIdx];
  const b = `path=${enc(S.cur)}&inner=${enc(p)}&password=${enc(S.pwd)}`;
  $('#lbImg').src = `/api/image?${b}`;
  $('#lbCap').textContent = `${p}  (${S.lbIdx+1}/${S.lbList.length})`;
  $('#lb').classList.add('on');
}
function closeLb(){ $('#lb').classList.remove('on'); $('#lbImg').src=''; }
function stepLb(d){
  if(!S.lbList.length) return;
  S.lbIdx = (S.lbIdx + d + S.lbList.length) % S.lbList.length;
  showLb();
}
$('#lbX').onclick = closeLb;
$('#lb').onclick = e=>{ if(e.target.id==='lb') closeLb(); };
$('#lbPrev').onclick = e=>{ e.stopPropagation(); stepLb(-1); };
$('#lbNext').onclick = e=>{ e.stopPropagation(); stepLb(1); };

/* ===================== 右键菜单 ===================== */
const ctx = $('#ctx');
function showCtx(ev, items){
  ctx.innerHTML = items.map((it,i)=>{
    if(it==='-') return '<div class="hr"></div>';
    return `<div class="it ${it.danger?'danger':''}" data-i="${i}">${it.icon||''} ${esc(it.label)}</div>`;
  }).join('');
  ctx.style.left = Math.min(ev.clientX, innerWidth-200) + 'px';
  ctx.style.top = Math.min(ev.clientY, innerHeight-280) + 'px';
  ctx.classList.add('on');
  $$('#ctx .it').forEach(el=>{
    el.onclick = ()=>{
      const it = items[+el.dataset.i];
      ctx.classList.remove('on');
      if(it && it.run) it.run();
    };
  });
}
document.addEventListener('click', e=>{ if(!ctx.contains(e.target)) ctx.classList.remove('on'); });

function archiveMenu(ev, path){
  const a = S.archives.find(x=>x.path===path);
  showCtx(ev, [
    {icon:'', label:'进入批量模式', run:()=>batchEnter(path)},
    '-',
    {icon:'', label:'移动到…', run:()=>pickFolder('移动到…', dst=>moveTo(path, dst))},
    {icon:'', label:'打开所在文件夹', run:()=>post('/api/fs/reveal',{path})},
    {icon:'', label:'复制完整路径', run:()=>copyText(path)},
    '-',
    {icon:'', label:'删除预览图', run:()=>delCover(path)},
    {icon:'', label:'解压到…', run:()=>askExtract(path, a)},
    {icon:'', label:'重命名…', run:()=>askRename(path)},
    '-',
    {icon:'', label:'删除到回收站', danger:true, run:()=>askTrash(path)}
  ]);
}

async function delCover(path){
  const d = await post('/api/cover/delete', {path, password:S.pwd});
  if(d.error) return toast(d.error);
  S.coverMap = null; S.coverVer++;
  toast(d.removed ? '预览图已删除' : '这个包没有预览图');
  renderArchiveList();
  // 如果删的就是当前打开的那个包：重新读一遍包内列表，封面文件也要从列表里消失
  if(S.cur === path){
    if(S.contentMode === 'split' && $('#paneRight')) batchShowArchive(path);
    else openArchive(path);
  }
}

function fileMenu(ev, inner){
  const f = S.files.find(x=>x.path===inner);
  const items = [];
  if(f && f.is_3d) items.push({icon:'', label:'在视口预览', run:()=>loadModel(inner)});
  if(f && f.is_pmx && !(S.openers && S.openers['.pmx']))
    items.push({icon:'', label:'用 PMXEditor 打开', run:()=>openEditor(inner)});
  if(f && S.openers && S.openers[f.ext]){
    const nm = (S.openers[f.ext].split(/[\\/]/).pop() || '外部程序').replace(/\.exe$/i, '');
    items.push({icon:'', label:`用 ${nm} 打开`, run:()=>openExternal(f)});
  }else if(f && TEXT_EXT && TEXT_EXT.has(f.ext)){
    items.push({icon:'', label:'用记事本打开', run:()=>openExternal(f)});
  }
  // 包内的封面文件（ZipPreview/xxx.png）：可以直接删预览图
  const coverRe = new RegExp('^' + S.coverFolder.replace(/[.*+?^${}()|[\]\\]/g, '\\$&') + '/.+\\.(png|jpg|jpeg|webp)$', 'i');
  if(coverRe.test(inner)){
    items.push({icon:'', label:'删除预览图', run:()=>delCover(S.cur)});
  }
  items.push({icon:'', label:'下载这个文件', run:()=>download(inner)});
  items.push({icon:'', label:'复制包内路径', run:()=>copyText(inner)});
  items.push('-');
  items.push({icon:'', label:'打开压缩包所在文件夹', run:()=>post('/api/fs/reveal',{path:S.cur})});
  showCtx(ev, items);
}

function post(url, body){
  return fetch(url, {method:'POST', headers:{'Content-Type':'application/json'}, body:JSON.stringify(body)})
    .then(r=>r.json());
}

function download(inner){
  window.open(`/api/download?path=${enc(S.cur)}&inner=${enc(inner)}&password=${enc(S.pwd)}`, '_blank');
}

function copyText(t){
  navigator.clipboard.writeText(t).catch(()=>{
    const ta = document.createElement('textarea');
    ta.value = t; document.body.appendChild(ta); ta.select();
    document.execCommand('copy'); ta.remove();
  });
}

/* ===================== 对话框 ===================== */
function dialog(html, onOpen){
  $('#dlg').innerHTML = html;
  $('#mask').classList.add('on');
  if(onOpen) onOpen();
}
function closeDialog(){
  $('#mask').classList.remove('on');
  $('#dlg').innerHTML='';
  $('#dlg').style.width='';          // 设置对话框会临时加宽，关掉时还原
}
$('#mask').onclick = e=>{ if(e.target.id==='mask') closeDialog(); };

function askRename(path){
  const cur = path.split('/').pop();
  dialog(`<h3>重命名</h3>
    <div class="body">
      <input id="rnInput" value="${esc(cur)}">
      <div class="note">只改文件名，扩展名会自动保留</div>
    </div>
    <div class="foot">
      <button class="fbtn" id="rnCancel">取消</button>
      <button class="fbtn solid" id="rnOk">确定</button>
    </div>`, ()=>{ $('#rnInput').focus(); $('#rnInput').select(); });
  $('#rnCancel').onclick = closeDialog;
  $('#rnOk').onclick = async ()=>{
    const name = $('#rnInput').value.trim();
    if(!name) return;
    const d = await post('/api/fs/rename', {path, name});
    if(d.error) return alert(d.error);
    closeDialog(); await loadMeta(); renderArchiveList();
  };
  $('#rnInput').onkeydown = e=>{ if(e.key==='Enter') $('#rnOk').click(); };
}

function askTrash(path){
  const name = path.split('/').pop();
  dialog(`<h3>删除</h3>
    <div class="body">
      <div class="note">将把 <b>${esc(name)}</b> 移到本工具的回收站<br>
      （<code>_cache\\trash</code>，不进系统回收站，可手动还原）</div>
    </div>
    <div class="foot">
      <button class="fbtn" id="trCancel">取消</button>
      <button class="fbtn solid" id="trOk" style="background:var(--red);border-color:var(--red)">移到回收站</button>
    </div>`);
  $('#trCancel').onclick = closeDialog;
  $('#trOk').onclick = async ()=>{
    const d = await post('/api/fs/trash', {path});
    if(d.error) return alert(d.error);
    closeDialog(); await loadMeta(); renderArchiveList();
  };
}

function askExtract(path, a){
  const stem = (a?a.name:path.split('/').pop()).replace(/\.[^.]+$/,'');
  const def = (a?a.dir:path.slice(0,path.lastIndexOf('/'))) + '/' + stem;
  dialog(`<h3>解压到</h3>
    <div class="body">
      <input id="exInput" value="${esc(def)}">
      <div class="note">这是真实解压，会把全部文件写到目标文件夹</div>
    </div>
    <div class="foot">
      <button class="fbtn" id="exCancel">取消</button>
      <button class="fbtn solid" id="exOk">开始解压</button>
    </div>`, ()=>{ $('#exInput').focus(); });
  $('#exCancel').onclick = closeDialog;
  $('#exOk').onclick = async ()=>{
    const target = $('#exInput').value.trim();
    if(!target) return;
    $('#exOk').textContent = '解压中…';
    $('#exOk').disabled = true;
    const d = await post('/api/fs/extract', {path, target, password:S.pwd});
    if(d.error){
      alert(d.error);
      $('#exOk').textContent = '开始解压';
      $('#exOk').disabled = false;
      return;
    }
    closeDialog();
    await loadMeta();
    alert('已解压到：\n' + d.target);
  };
}

/* ===================== 设置 ===================== */
const OPENER_EXTS = ['.pmx', '.pmd', '.glb', '.gltf', '.fbx', '.obj',
                     '.zprj', '.blend', '.uemodel', '.dae', '.stl', '.abc',
                     '.txt', '.md', '.json', '.log', '.ini', '.csv'];

/* 文本类：没配外部程序时用记事本打开 */
const TEXT_EXT = new Set(['.txt', '.md', '.json', '.xml', '.ini', '.cfg', '.log', '.csv',
                          '.yml', '.yaml', '.py', '.bat', '.ps1', '.html', '.htm', '.srt', '.ass']);

let _opRows = null;

function syncOpRows(){
  _opRows = $$('#openerRows .rootrow').map(row=>{
    const sel = row.querySelector('select'), inp = row.querySelector('input');
    return { ext: sel ? sel.value : '', path: inp ? inp.value.trim() : '' };
  });
}

function renderOpenerRows(){
  const rows = _opRows || [];
  $('#openerRows').innerHTML = rows.length
    ? rows.map((r, i)=>{
        const list = OPENER_EXTS.includes(r.ext) ? OPENER_EXTS : OPENER_EXTS.concat([r.ext]);
        return `<div class="rootrow">
          <select data-i="${i}" style="flex:none;width:92px">${list.map(e=>
            `<option ${e===r.ext?'selected':''}>${e}</option>`).join('')}</select>
          <input data-i="${i}" value="${esc(r.path||'')}" placeholder="threeJS 或程序完整路径">
          <button class="fbtn" data-b="${i}">打开</button>
          <button class="fbtn" data-d="${i}">✕</button>
        </div>`;
      }).join('')
    : '<div class="note" style="margin-bottom:6px">还没有配置</div>';
  $$('#openerRows [data-b]').forEach(b=>b.onclick = async ()=>{
    const inp = $$('#openerRows input')[+b.dataset.b];
    const d = await post('/api/pick_file', {});
    if(d && d.path && inp) inp.value = d.path;
  });
  $$('#openerRows [data-d]').forEach(b=>b.onclick = ()=>{
    syncOpRows();
    _opRows.splice(+b.dataset.d, 1);
    renderOpenerRows();
  });
}

function openSettings(){
  const roots = S.meta.roots.map(r=>r.path);
  const pws = (S.passwords || []).slice();
  const renderPwList = ()=>{
    const el = $('#pwList');
    if(!el) return;
    el.innerHTML = pws.length
      ? pws.map((p,i)=>`<div class="rootrow">
          <input value="${esc(p)}" readonly>
          <button class="fbtn" data-pwd="${i}">✕</button></div>`).join('')
      : '<div class="note" style="margin-bottom:6px">还没有保存的密码</div>';
    $$('#pwList [data-pwd]').forEach(b=>b.onclick = ()=>{
      pws.splice(+b.dataset.pwd, 1);
      renderPwList();
    });
  };
  if(_opRows === null){
    _opRows = Object.entries(S.openers || {}).map(([ext, path])=>({ext, path}));
  }
  dialog(`<h3>设置</h3>
    <div class="body setwrap">
      <div class="setnav">
        <button class="settab on" data-tab="dirs">文件目录</button>
        <button class="settab" data-tab="shot">截图</button>
        <button class="settab" data-tab="fmt">格式关联</button>
        <button class="settab" data-tab="pwd">密码管理</button>
        <button class="settab" data-tab="browser">鼠标手势</button>
      </div>
      <div class="setbody">
        <div class="setsec" data-sec="dirs">
          <label>读取的文件管理目录</label>
          <div id="rootRows"></div>
          <button class="fbtn" id="addRoot" style="margin:6px 0 10px">+ 添加目录</button>
          <div class="note">工具扫描这些目录下的压缩包（zip / 7z / rar / 自解压 exe）。</div>
        </div>
        <div class="setsec hide" data-sec="shot">
          <label>截图命名</label>
          <input id="shotName" type="text" spellcheck="false" value="${esc((S.coverNames||['ZipPreview.png'])[0]||'ZipPreview.png')}">
          <div class="note">截图存进包内 <b>${esc(S.coverFolder)}/</b> 目录，用这个名字。</div>
        </div>
        <div class="setsec hide" data-sec="fmt">
          <label>格式关联</label>
          <div id="openerRows"></div>
          <button class="fbtn" id="addOpener" style="margin:6px 0 10px">+ 添加格式</button>
          <div class="note">右边写外部程序的完整路径（点「打开」选 exe）。<br>
            留空或写 <code>threeJS</code> = 用内置预览；配了外部程序后，预览栏会出现「用 XXX 打开」按钮。</div>

          <label style="margin-top:16px">外部工具</label>
          <div class="rootrow" style="margin-bottom:6px">
            <input id="tool7z" type="text" spellcheck="false" value="${esc((S.tools||{}).seven_zip || '')}" placeholder="7z.exe">
            <button class="fbtn" id="pick7z">浏览</button>
          </div>
          <div class="note" style="margin-bottom:10px">7-Zip 的 7z.exe。留空 = 自动查找（注册表 / PATH / Program Files）</div>
          <div class="rootrow" style="margin-bottom:6px">
            <input id="toolRar" type="text" spellcheck="false" value="${esc((S.tools||{}).unrar || '')}" placeholder="UnRAR.exe（可选）">
            <button class="fbtn" id="pickRar">浏览</button>
          </div>
          <div class="note" style="margin-bottom:10px">WinRAR 的 UnRAR.exe，可留空</div>
          <div class="rootrow" style="margin-bottom:6px">
            <input id="toolText" type="text" spellcheck="false" value="${esc((S.tools||{}).text_editor || '')}" placeholder="记事本（默认）">
            <button class="fbtn" id="pickText">浏览</button>
          </div>
          <div class="note">文本类默认用记事本；想用 Notepad++ / VS Code 就填在这里</div>
        </div>
        <div class="setsec hide" data-sec="pwd">
          <label>密码管理</label>
          <div class="rootrow" style="margin-bottom:10px">
            <input id="pwNew" type="text" spellcheck="false">
            <button class="fbtn solid" id="pwAdd">保存</button>
          </div>
          <div id="pwList"></div>
          <div class="note">保存的密码会在打开加密压缩包时列出来，点一下就能用。<br>
            明文保存在 config.json 里，别把这份配置发给别人。</div>
        </div>
        <div class="setsec hide" data-sec="browser">
          <label>右键拖动被浏览器抢走了？</label>
          <div class="note" style="margin-bottom:10px">
            Edge 自带的<b>「鼠标手势」</b>会在按住右键拖动时弹出前进 / 后退 / 滚动提示，
            网页这边拦不住它。点下面的按钮打开本工具所用浏览器配置的外观设置，
            把「鼠标手势」关掉，右键按住就能直接旋转了。
          </div>
          <button class="fbtn" id="openEdgeSettings">打开 Edge 外观设置</button>
        </div>
      </div>
    </div>
    <div class="foot">
      <button class="fbtn" id="stCancel">取消</button>
      <button class="fbtn solid" id="stSave">保存</button>
    </div>`, ()=>{
      renderRootRows(roots);
      renderOpenerRows();
      renderPwList();
      $('#dlg').style.width = 'min(720px, 94vw)';   // 设置内容宽（左栏 + 表单），默认 520 太挤
      $$('#dlg .settab').forEach(btn=>btn.onclick = ()=>{
        $$('#dlg .settab').forEach(b=>b.classList.toggle('on', b === btn));
        $$('#dlg .setsec').forEach(s=>s.classList.toggle('hide', s.dataset.sec !== btn.dataset.tab));
      });
    });
  $('#stCancel').onclick = closeDialog;
  // 外部工具路径的「浏览」：选一个 exe
  [['pick7z','tool7z'], ['pickRar','toolRar'], ['pickText','toolText']].forEach(([b, i])=>{
    const btn = $('#' + b);
    if(btn) btn.onclick = async ()=>{
      const d = await post('/api/pick_file', {});
      if(d && d.path && $('#' + i)) $('#' + i).value = d.path;
    };
  });
  if($('#pwAdd')) $('#pwAdd').onclick = ()=>{
    const v = ($('#pwNew').value || '').trim();
    if(!v) return;
    if(!pws.includes(v)) pws.push(v);
    $('#pwNew').value = '';
    renderPwList();
  };
  if($('#pwNew')) $('#pwNew').onkeydown = e=>{ if(e.key==='Enter') $('#pwAdd').click(); };
  if($('#openEdgeSettings')) $('#openEdgeSettings').onclick = async ()=>{
    const d = await post('/api/browser_settings', {});
    if(d && d.error) return alert(d.error);
    toast('已打开 Edge 设置，关掉「鼠标手势」后回到工具即可');
  };
  $('#addRoot').onclick = ()=>{ roots.push(''); renderRootRows(roots); };
  $('#addOpener').onclick = ()=>{
    syncOpRows();
    const used = new Set(_opRows.map(r=>r.ext));
    _opRows.push({ext: OPENER_EXTS.find(e=>!used.has(e)) || '.obj', path: ''});
    renderOpenerRows();
  };
  $('#stSave').onclick = async ()=>{
    const list = $$('#rootRows input').map(i=>i.value.trim()).filter(Boolean);
    if(!list.length) return alert('至少要有一个目录');
    syncOpRows();
    const openers = {};
    for(const r of _opRows){
      if(!r.ext || !r.path) continue;
      if(r.path.toLowerCase() === 'threejs') continue;   // 明确用内置预览
      openers[r.ext] = r.path;
    }
    const name = ($('#shotName').value || '').trim() || 'ZipPreview.png';
    const tools = {
      seven_zip:  ($('#tool7z')   ? $('#tool7z').value.trim()   : ''),
      unrar:      ($('#toolRar')  ? $('#toolRar').value.trim()  : ''),
      text_editor:($('#toolText') ? $('#toolText').value.trim() : ''),
    };
    const d1 = await post('/api/roots', {roots:list});
    if(d1.error) return alert(d1.error);
    const d2 = await post('/api/settings', {cover_names: name, openers, passwords: pws, ...tools});
    if(d2.error) return alert(d2.error);
    closeDialog();
    S.meta = d1.meta; S.archives = d1.meta.archives;
    S.sel = {type:'all'};
    S.coverNames = d2.cover_names;
    S.openers = d2.openers || {};
    S.passwords = d2.passwords || pws;
    S.tools = {seven_zip: d2.seven_zip || '', unrar: d2.unrar || '',
               text_editor: d2.text_editor || ''};
    if(!d2.seven_zip) toast('⚠ 没找到 7z.exe，压缩包读不了：去 设置 → 格式关联 填路径');
    S.coverVer++;
    _opRows = null;
    renderNav(); renderStat(); renderArchiveList();
    if(S.cur) renderFiles();
    refreshExtButton();     // 刚配好的外部程序，视口里的按钮立刻出现/换名
  };
}
$('#settingsBtn').onclick = openSettings;

/* 标题右键：刷新 / 退出程序（退出会真的结束进程，不只是关页面） */
$('#brandBtn').onclick = ()=>location.reload();
$('#brandBtn').oncontextmenu = ev=>{
  ev.preventDefault();
  showCtx(ev, [
    {icon:'', label:'刷新页面', run:()=>location.reload()},
    '-',
    {icon:'', label:'退出程序', danger:true, run:()=>{
      post('/api/quit', {}).catch(()=>{});
      document.body.innerHTML = '<div class="empty">程序已退出，窗口可以关掉了</div>';
    }},
  ]);
};

/* 视口第一颗按钮：配了外部程序就用它，没配的 pmx 退回 PMXEditor */
function refreshExtButton(){
  const row = $('#vFoot .vrow');
  if(!row || !OBJ) return;
  const cur = (S.files || []).find(x=>x.path === _modelInner);
  if(!cur) return;
  const old = $('#vOpenExt'); if(old) old.remove();
  const oldEdit = $('#vEdit');
  const op = (S.openers && S.openers[cur.ext]) || '';
  if(op){
    if(oldEdit) oldEdit.remove();
    const nm = (op.split(/[\\/]/).pop() || '外部程序').replace(/\.(exe|bat|cmd)$/i, '');
    const b = document.createElement('button');
    b.className = 'fbtn'; b.id = 'vOpenExt'; b.textContent = '用 ' + nm + ' 打开';
    b.onclick = ()=>openExternal(cur);
    row.insertBefore(b, row.firstChild);
  }else if(cur.is_pmx && !oldEdit){
    const b = document.createElement('button');
    b.className = 'fbtn'; b.id = 'vEdit'; b.textContent = 'PMXEditor';
    b.onclick = ()=>openEditor(cur.path);
    row.insertBefore(b, row.firstChild);
  }
}

function openManage(){
  const roots = S.meta.roots.map(r=>r.path);
  dialog(`<h3>管理监控目录</h3>
    <div class="body">
      <div id="rootRows"></div>
      <button class="fbtn" id="addRoot" style="margin-bottom:12px">+ 添加目录</button>
      <div class="note">工具会扫描这些目录下的压缩包（zip / 7z / rar / 自解压 exe）</div>
    </div>
    <div class="foot">
      <button class="fbtn" id="mgCancel">取消</button>
      <button class="fbtn solid" id="mgSave">保存并重新扫描</button>
    </div>`, ()=>{ renderRootRows(roots); });
  $('#mgCancel').onclick = closeDialog;
  $('#addRoot').onclick = ()=>{ roots.push(''); renderRootRows(roots); };
  $('#mgSave').onclick = async ()=>{
    const list = $$('#rootRows input').map(i=>i.value.trim()).filter(Boolean);
    if(!list.length) return alert('至少要有一个目录');
    const d = await post('/api/roots', {roots:list});
    if(d.error) return alert(d.error);
    closeDialog();
    S.meta = d.meta; S.archives = d.meta.archives;
    S.sel = {type:'all'};
    renderNav(); renderStat(); renderArchiveList();
  };
}

function renderRootRows(roots){
  $('#rootRows').innerHTML = roots.map((r,i)=>`
    <div class="rootrow">
      <input value="${esc(r)}" data-i="${i}" placeholder="例如 D:\\MODEL">
      <button class="fbtn" data-browse="${i}">浏览</button>
      <button class="fbtn" data-del="${i}">✕</button>
    </div>`).join('');
  $$('#rootRows [data-del]').forEach(b=>b.onclick=()=>{
    roots.splice(+b.dataset.del,1);
    if(!roots.length) roots.push('');
    renderRootRows(roots);
  });
  $$('#rootRows [data-browse]').forEach(b=>b.onclick=async ()=>{
    const idx = +b.dataset.browse;
    const d = await post('/api/pick_folder', {});
    if(d && d.path){
      const inputs = $$('#rootRows input');
      if(inputs[idx]) inputs[idx].value = d.path.replace(/\//g, '\\');
    }
  });
}

let _browseTarget = null, _browsePath = '';

function browseDir(start, cb){
  _browseTarget = cb; _browsePath = start || '';
  const draw = async ()=>{
    const d = await post('/api/browse', {path:_browsePath});
    const list = (d.dirs||[]).map(x=>`<div class="ditem" data-p="${esc(x.path)}">${esc(x.name)}</div>`).join('');
    dialog(`<h3>选择目录</h3>
      <div class="body">
        <div class="note" style="margin-bottom:8px;word-break:break-all">${esc(d.path||'选择磁盘')}</div>
        <div class="dlist">
          ${d.parent ? `<div class="ditem" data-p="${esc(d.parent)}">上一级</div>`:''}
          ${list || '<div class="ditem" style="color:#9c9ca6">（没有子目录）</div>'}
        </div>
      </div>
      <div class="foot">
        <button class="fbtn" id="brCancel">取消</button>
        <button class="fbtn solid" id="brOk">选择当前目录</button>
      </div>`);
    $('#brCancel').onclick = ()=>{ closeDialog(); openManage(); };
    $('#brOk').onclick = ()=>{
      if(!_browsePath) return alert('先进入一个目录');
      const p = _browsePath;
      closeDialog();
      openManage();
      setTimeout(()=>{ if(_browseTarget) _browseTarget(p); }, 30);
    };
    $$('#dlg .ditem[data-p]').forEach(el=>el.onclick=()=>{ _browsePath = el.dataset.p; draw(); });
  };
  draw();
}

/* ===================== 工具栏 ===================== */
$('#q').oninput = ()=>{
  clearTimeout(window.__qt);
  window.__qt = setTimeout(()=>{
    renderNav();
    if(S.cur) renderFiles(); else renderArchiveList();
  }, 220);
};
$$('[data-filter]').forEach(b=>b.onclick = ()=>{
  S.filter = b.dataset.filter;
  syncFilterBtns();
  if(S.cur){ renderFiles(); $('#content').scrollTop = 0; }
});
$('#foldAll').onclick = ()=>{
  const anyOpen = SECTIONS.some(s=>!S.foldSec[s.key]);
  SECTIONS.forEach(s=>{ S.foldSec[s.key] = anyOpen; });
  $('#foldAll').textContent = anyOpen ? '展开全部' : '折叠全部';
  if(S.cur) renderFiles();
};
$('#cmodeBtn').onclick = ()=>{
  S.contentMode = S.contentMode==='split' ? 'stack' : 'split';
  $('#cmodeBtn').textContent = S.contentMode==='split' ? '堆叠分栏' : '左右铺开';
  if(S.cur) renderFiles(); else renderArchiveList();
};
$('#viewBtn').onclick = ()=>{
  S.viewMode = S.viewMode==='grid'?'rows':'grid';
  $('#viewBtn').textContent = S.viewMode==='grid'?'列表':'网格';
  if(S.cur) renderFiles(); else renderArchiveList();
};
$('#trashBtn').onclick = ()=>post('/api/trash/open', {});
function setSideCollapsed(c){
  document.body.classList.toggle('side-collapsed', c);
  $('#sidebar').classList.toggle('hide', c);
  $('#sideTab').textContent = c ? '›' : '‹';
  setTimeout(resizeGL, 80);
}
function setViewCollapsed(c){
  document.body.classList.toggle('view-collapsed', c);
  $('#viewer').classList.toggle('hide', c);
  $('#toggleViewer').classList.toggle('on', !c);
  $('#viewTab').textContent = c ? '‹' : '›';
  setTimeout(resizeGL, 80);
}
$('#sideTab').onclick = ()=> setSideCollapsed(!document.body.classList.contains('side-collapsed'));
$('#viewTab').onclick = ()=> setViewCollapsed(!document.body.classList.contains('view-collapsed'));
$('#toggleViewer').onclick = ()=> setViewCollapsed(!document.body.classList.contains('view-collapsed'));
$('#vClose').onclick = ()=> setViewCollapsed(true);

/* ---------- 拖拽调整三个视口宽度 ---------- */
function applyPaneSizes(side, view){
  const root = document.documentElement.style;
  root.setProperty('--side-w', side + 'px');
  root.setProperty('--view-w', view + 'px');
  try{ localStorage.setItem('zipview.panes', JSON.stringify({side, view})); }catch(e){}
  if(typeof resizeGL === 'function') setTimeout(resizeGL, 20);
}
function loadPaneSizes(){
  try{
    const d = JSON.parse(localStorage.getItem('zipview.panes') || 'null');
    if(d && d.side >= 180 && d.side <= 560 && d.view >= 280 && d.view <= 900){
      applyPaneSizes(d.side, d.view);
    }
  }catch(e){}
}
function bindSplitter(el, side){
  el.addEventListener('pointerdown', ev=>{
    ev.preventDefault();
    el.setPointerCapture(ev.pointerId);
    el.classList.add('drag');
    document.body.classList.add('resizing');
    const startX = ev.clientX;
    const cur = side ? parseFloat(getComputedStyle(document.documentElement).getPropertyValue('--side-w'))
                     : parseFloat(getComputedStyle(document.documentElement).getPropertyValue('--view-w'));
    const onMove = e=>{
      const dx = e.clientX - startX;
      const w = side ? cur + dx : cur - dx;
      const max = Math.min(900, window.innerWidth * 0.62);
      const clamped = Math.max(side ? 180 : 280, Math.min(max, w));
      const root = document.documentElement.style;
      root.setProperty(side ? '--side-w' : '--view-w', clamped + 'px');
      if(typeof resizeGL === 'function') resizeGL();
    };
    const onUp = e=>{
      el.classList.remove('drag');
      document.body.classList.remove('resizing');
      try{ el.releasePointerCapture(ev.pointerId); }catch(_){}
      el.removeEventListener('pointermove', onMove);
      el.removeEventListener('pointerup', onUp);
      const s = parseFloat(getComputedStyle(document.documentElement).getPropertyValue('--side-w'));
      const v = parseFloat(getComputedStyle(document.documentElement).getPropertyValue('--view-w'));
      applyPaneSizes(s, v);
    };
    el.addEventListener('pointermove', onMove);
    el.addEventListener('pointerup', onUp);
  });
}
bindSplitter($('#splitSide'), true);
bindSplitter($('#splitView'), false);
loadPaneSizes();
/* 截图：先显示虚线框（提示会截到哪里），确认后才真正截 */
$('#vShot').onclick = ()=>{
  if(!R) return;
  $('#shotGuide').classList.remove('hide');
};
if($('#shotNo')) $('#shotNo').onclick = ()=> $('#shotGuide').classList.add('hide');
if($('#shotOk')) $('#shotOk').onclick = async ()=>{
  $('#shotGuide').classList.add('hide');
  if(!R) return;
  R.render(SC, CAM);
  const png = $('#c3d').toDataURL('image/png');
  // 有打开压缩包时，优先存成包内封面（ZipPreview/ 目录），同时保留一份下载
  if(S.cur){
    try{
      const d = await post('/api/cover/save', {path:S.cur, password:S.pwd, png});
      if(d.ok){
        S.coverVer++;
        // 左侧网格和文件列表都要重画：封面 URL 带 v=，重画后浏览器才会重新取图
        renderArchiveList();
        if(S.cur) renderFiles();
        toast(`封面已保存到包内 ${S.coverFolder}/ 文件夹`);
        return;
      }
      if(d.error && /不支持写入/.test(d.error)) toast(d.error);
    }catch(e){}
  }
  const a = document.createElement('a');
  a.href = png;
  a.download = (S.coverNames[0] || 'ZipPreview.png').replace(/\.[^.]+$/, '') + '.png';
  a.click();
};

function toast(msg){
  let t = $('#toast');
  if(!t){
    t = document.createElement('div'); t.id = 'toast';
    t.style.cssText = 'position:fixed;bottom:22px;left:50%;transform:translateX(-50%);z-index:999;'+
      'background:#22232b;color:#fff;padding:10px 16px;border-radius:9px;font-size:12.5px;'+
      'box-shadow:0 6px 22px rgba(0,0,0,.22);opacity:0;transition:opacity .2s';
    document.body.appendChild(t);
  }
  t.textContent = msg; t.style.opacity = '1';
  clearTimeout(t._timer);
  t._timer = setTimeout(()=>{ t.style.opacity = '0'; }, 2600);
}

document.addEventListener('keydown', e=>{
  if($('#lb').classList.contains('on')){
    if(e.key==='Escape') closeLb();
    if(e.key==='ArrowLeft') stepLb(-1);
    if(e.key==='ArrowRight') stepLb(1);
    return;
  }
  if(e.key==='Escape'){ closeDialog(); ctx.classList.remove('on'); }
});

/* ===================== 筛选面板 ===================== */
S.flt = {enc:'all', cov:'all'};
S.coverMap = null;

async function loadCovers(){
  if(S.coverMap) return S.coverMap;
  toast('正在统计预览图…');
  try{ const d = await fetch('/api/covers').then(r=>r.json()); S.coverMap = d.map || {}; }
  catch(e){ S.coverMap = {}; }
  return S.coverMap;
}

$('#filterBtn').onclick = ev=>{ ev.stopPropagation(); $('#filterPanel').classList.toggle('hide'); };
$('#filterPanel').onclick = ev=>ev.stopPropagation();
document.addEventListener('click', ()=>{ const p=$('#filterPanel'); if(p) p.classList.add('hide'); });
$$('#filterPanel [data-fenc]').forEach(b=>b.onclick=()=>{
  S.flt.enc = b.dataset.fenc;
  $$('#filterPanel [data-fenc]').forEach(x=>x.classList.toggle('on', x===b));
  renderArchiveList();
});
$$('#filterPanel [data-fcov]').forEach(b=>b.onclick=()=>{
  S.flt.cov = b.dataset.fcov;
  $$('#filterPanel [data-fcov]').forEach(x=>x.classList.toggle('on', x===b));
  if(S.flt.cov !== 'all' && !S.coverMap) loadCovers().then(()=>renderArchiveList());
  else renderArchiveList();
});

/* ===================== 批量模式 ===================== */
S.batch = {on:false, sel:new Set(), anchor:null, order:[]};

const wait = ms => new Promise(r=>setTimeout(r, ms));

function batchEnter(path){
  S.batch.on = true;
  S.batch.sel = new Set(path ? [path] : []);
  S.batch.anchor = path || null;
  $('#batchBar').classList.remove('hide');
  updateBatchUI();
  renderArchiveList();
  // 铺开视图下立刻把右键的那个显示到右侧
  if(path && S.contentMode === 'split' && $('#paneRight')) batchShowArchive(path);
}

/* 批量模式下只在右侧窗格显示某个压缩包的内容（不重画左侧列表，避免滚动条跳回顶部） */
async function batchShowArchive(path){
  const R = $('#paneRight');
  if(!R) return;
  const a = S.archives.find(x=>x.path===path);
  S.cur = path;
  S.curName = a ? a.name : path.split('/').pop();
  R.innerHTML = '<div class="empty"><div class="spin"></div>正在读取压缩包…</div>';
  try{
    const d = await fetch(`/api/list?path=${enc(path)}&password=${enc(S.pwd)}`).then(r=>r.json());
    if(d.need_password){ R.innerHTML = '<div class="err">这个包需要密码：先退出批量模式再打开它</div>'; return; }
    if(d.error){ R.innerHTML = `<div class="err">${esc(d.error)}</div>`; return; }
    S.files = d.files || [];
    S.pwTried = false;
    renderFiles(R, true);
  }catch(e){
    R.innerHTML = `<div class="err">${esc(String(e))}</div>`;
  }
}
function batchExit(){
  S.batch.on = false;
  S.batch.sel = new Set();
  S.batch.anchor = null;
  $('#batchBar').classList.add('hide');
  renderArchiveList();
}
function updateBatchUI(){
  const c = $('#batchCount');
  if(c) c.textContent = '已选 ' + S.batch.sel.size;
}
function batchPaint(){
  $$('#content [data-archive]').forEach(el=>el.classList.toggle('sel', S.batch.sel.has(el.dataset.archive)));
  updateBatchUI();
}
function batchClick(ev, path){
  const sel = S.batch.sel;
  if(ev.shiftKey && S.batch.anchor){
    const a = S.batch.order.indexOf(S.batch.anchor), b = S.batch.order.indexOf(path);
    if(a >= 0 && b >= 0){
      const lo = Math.min(a,b), hi = Math.max(a,b);
      for(let i=lo;i<=hi;i++) sel.add(S.batch.order[i]);
    }
  }else if(ev.ctrlKey || ev.metaKey){
    if(sel.has(path)) sel.delete(path); else sel.add(path);
    S.batch.anchor = path;
  }else{
    sel.clear(); sel.add(path); S.batch.anchor = path;
  }
  batchPaint();
  // 左右铺开视图下，右侧跟着显示「最后点的那个」压缩包内容，可以直接点开预览
  if(S.contentMode === 'split' && $('#paneRight')) batchShowArchive(path);
}

$('#batchBar').onclick = ev=>{
  const b = ev.target.closest('[data-b]');
  if(!b) return;
  const act = b.dataset.b;
  const sel = [...S.batch.sel];
  if(act==='exit'){ batchExit(); return; }
  if(act==='all'){ S.batch.order.forEach(p=>S.batch.sel.add(p)); }
  else if(act==='inv'){ S.batch.order.forEach(p=>{ if(S.batch.sel.has(p)) S.batch.sel.delete(p); else S.batch.sel.add(p); }); }
  else if(act==='none'){ S.batch.sel.clear(); S.batch.anchor = null; }
  else if(act==='move'){ if(!sel.length) return toast('先选几个'); batchMove(sel); return; }
  else if(act==='cover'){ if(!sel.length) return toast('先选几个'); batchCovers(sel); return; }
  else if(act==='delcover'){ if(!sel.length) return toast('先选几个'); batchDelCovers(sel); return; }
  batchPaint();
};

function batchDirs(){
  const out = [];
  const walk = (nodes, root) => {
    for(const g of (nodes||[])){
      out.push({dir: root + '\\' + g.path.replace(/\//g, '\\'),
                label: shortPath(root) + '\\' + g.path.replace(/\//g, '\\')});
      walk(g.children, root);
    }
  };
  for(const r of S.meta.roots){
    out.push({dir:r.path, label: shortPath(r.path)});
    walk(r.groups, r.path);
  }
  return out;
}

/* 目录树（含子级），给「移动到…」用 */
function metaTree(){
  const out = [];
  const walk = (list, root, dst, parent) => {
    for(const g of (list||[])){
      const dir = root + '\\' + g.path.replace(/\//g, '\\');
      const node = {name:g.name, dir, count:g.count, children:[], parent};
      dst.push(node);
      walk(g.children, root, node.children, node);
    }
  };
  for(const r of S.meta.roots){
    const node = {name: shortPath(r.path), dir: r.path, count: r.count, children: [], parent: null};
    walk(r.groups, r.path, node.children, node);
    out.push(node);
  }
  return out;
}

/* 可逐级进入的目录选择器：点文件夹往下钻，点「移动到这里」确认当前层 */
/* 可展开的目录树选择器（像左侧分组那样一层层展开，而不是一层层钻） */
function pickFolder(title, cb, excludeDir){
  const roots = metaTree();
  const bad = (p)=>{
    if(!excludeDir) return false;
    const a = p.toLowerCase(), b = excludeDir.toLowerCase();
    return a === b || a.startsWith(b + '\\');
  };
  const expanded = new Set();          // 展开的目录
  let selected = '';                   // 当前选中的目录

  const renderTree = (nodes, depth)=>{
    let h = '';
    for(const n of nodes){
      if(bad(n.dir)) continue;
      const exp = expanded.has(n.dir);
      const sel = selected === n.dir;
      h += `<div class="ditem pktree ${sel?'on':''}" data-dir="${esc(n.dir)}"
              style="padding-left:${8 + depth*15}px">
              <span class="chev" data-chev="${esc(n.dir)}">${n.children.length ? (exp?'▾':'▸') : ''}</span>
              <span class="pknm" title="${esc(n.dir)}">${esc(n.name)}</span>
              <span class="pkct">${n.count}</span>
            </div>`;
      if(exp && n.children.length) h += renderTree(n.children, depth+1);
    }
    return h;
  };

  const draw = ()=>{
    const body = renderTree(roots, 0) || '<div class="ditem" style="color:#9c9ca6">没有可移动到的目录</div>';
    dialog(`<h3>${esc(title)}</h3><div class="body">
      <div class="dlist" style="max-height:360px" id="pkList">${body}</div>
      <div class="note">点箭头展开子文件夹，点文件夹名选中；最上层就是管理目录。</div>
    </div><div class="foot">
      <button class="fbtn" id="pkCancel">取消</button>
      <button class="fbtn solid" id="pkOk"${selected ? '' : ' disabled'}>移动到这里</button>
    </div>`, ()=>{
      $('#pkCancel').onclick = closeDialog;
      const ok = $('#pkOk');
      if(ok) ok.onclick = ()=>{ if(!selected) return; const d = selected; closeDialog(); cb(d); };
      $$('#dlg [data-chev]').forEach(el=>el.onclick = ev=>{
        ev.stopPropagation();
        const d = el.dataset.chev;
        if(!d) return;
        if(expanded.has(d)) expanded.delete(d); else expanded.add(d);
        draw();
      });
      $$('#dlg .ditem.pktree').forEach(el=>el.onclick = ()=>{
        const d = el.dataset.dir || '';
        if(!d) return;
        selected = d;
        // 选中时顺手展开
        if(!expanded.has(d)){ expanded.add(d); }
        draw();
      });
    });
  };
  draw();
}

function batchMove(paths){
  pickFolder(`移动 ${paths.length} 个到…`, dst=>doBatchMove(paths, dst));
}

async function doBatchMove(paths, dst){
  let overwrite = null, ok = 0, skip = 0;
  for(const p of paths){
    let d = await post('/api/fs/move', {src:p, dst_dir:dst});
    if(d.conflict){
      if(overwrite === null){
        overwrite = await new Promise(res=>askOverwrite(d.name, res));
      }
      if(!overwrite){ skip++; continue; }
      d = await post('/api/fs/move', {src:p, dst_dir:dst, overwrite:true});
    }
    if(d.error){ toast(d.error); }
    else if(d.meta){ S.meta = d.meta; S.archives = d.meta.archives; ok++; }
  }
  S.coverMap = null;
  toast(`移动完成：${ok} 个` + (skip ? `，跳过 ${skip} 个` : ''));
  batchExit(); renderNav(); renderStat();
}

async function batchDelCovers(paths){
  let n = 0;
  for(const p of paths){
    const d = await post('/api/cover/delete', {path:p, password:S.pwd});
    if(d.error){ toast(d.error); continue; }
    if(d.removed) n++;
  }
  S.coverMap = null; S.coverVer++;
  toast(`已删除 ${n} 张预览图`);
  batchExit();
}

function frontView(){
  if(!OBJ) return;
  const box = computeBounds(OBJ);
  const c = box.getCenter(new THREE.Vector3());
  const s = box.getSize(new THREE.Vector3());
  const h = Math.max(s.y, 0.5);
  CAM.position.set(c.x, c.y + h * 0.05, c.z + h * 1.95);
  CTL.target.set(c.x, c.y, c.z);
  CAM.updateProjectionMatrix();
  CTL.update();
}

async function batchCovers(paths){
  if(!R && !initGL()) return;
  let ok = 0, skip = 0, i = 0;
  for(const p of paths){
    i++;
    toast(`生成预览图 ${i}/${paths.length}…`);
    try{
      await openArchive(p);
      const m = (S.files||[]).find(f=>f.is_3d);
      if(!m){ skip++; continue; }
      await loadModel(m.path);
      await wait(1400);
      frontView();
      await wait(260);
      const png = $('#c3d').toDataURL('image/png');
      const d = await post('/api/cover/save', {path:p, password:S.pwd, png});
      if(d.ok) ok++; else skip++;
    }catch(e){ skip++; }
  }
  S.coverMap = null; S.coverVer++;
  toast(`完成：生成 ${ok} 张` + (skip ? `，跳过 ${skip} 个` : ''));
  batchExit();
}
/* ===================== 启动 ===================== */
(async function(){
  await loadMeta();
  S.sel = {type:'all'};
  renderNav();
  renderArchiveList();
  initGL();
})();
</script>
</body>
</html>
"""


WINDOW_TITLE = "Zip2mmd"


def _find_browser():
    """找系统里的 Edge / Chrome。"""
    cands = []
    for env in ("PROGRAMFILES(X86)", "PROGRAMFILES", "LOCALAPPDATA"):
        b = os.environ.get(env)
        if not b:
            continue
        cands.append(os.path.join(b, "Microsoft", "Edge", "Application", "msedge.exe"))
        cands.append(os.path.join(b, "Google", "Chrome", "Application", "chrome.exe"))
    for p in cands:
        if os.path.isfile(p):
            return p
    return None


def _profile_dir():
    """浏览器配置目录放到 %LOCALAPPDATA%，不要放进项目文件夹。
    项目文件夹可能被安全软件/沙箱 ACL 限制（例如禁用删除子项），
    Edge 启动时要清理自己的缓存，被拒绝就会报权限错误，甚至提示「提升权限重启」。"""
    base = os.environ.get("LOCALAPPDATA") or os.path.join(
        os.path.expanduser("~"), "AppData", "Local")
    p = os.path.join(base, "ZipPreviewTool", "browser")
    try:
        os.makedirs(p, exist_ok=True)
    except Exception:
        p = os.path.join(tempfile.gettempdir(), "ZipPreviewTool-browser")
        os.makedirs(p, exist_ok=True)
    return p


def _gesture_off(prof):
    """把本工具浏览器配置里的「鼠标手势」关掉。

    Edge 的开关是 Preferences 里的 `edge_mouse_gesture.enabled`（默认 true）。
    它会在右键拖动时接管手势（前进/后退/关标签页），网页里拦不住——
    拖太远甚至会关掉窗口，程序就跟着退出了。所以启动前直接改配置。"""
    try:
        d = os.path.join(prof, "Default")
        os.makedirs(d, exist_ok=True)
        pf = os.path.join(d, "Preferences")
        data = {}
        if os.path.isfile(pf):
            with open(pf, "r", encoding="utf-8") as f:
                data = json.load(f)
        g = data.get("edge_mouse_gesture")
        if not isinstance(g, dict):
            g = {}
        if g.get("enabled") is False:
            return
        g["enabled"] = False
        data["edge_mouse_gesture"] = g
        tmp = pf + ".zt"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, separators=(",", ":"))
        os.replace(tmp, pf)
    except Exception:
        pass


def _launch_app_window(url):
    """用 Edge/Chrome 的 --app 模式开一个无地址栏窗口（独立配置目录，不碰用户浏览器）。"""
    exe = _find_browser()
    if not exe:
        return None
    prof = _profile_dir()
    _gesture_off(prof)
    args = [
        exe, f"--app={url}", "--window-size=1500,940",
        f"--user-data-dir={prof}",
        "--no-first-run", "--no-default-browser-check",
        "--no-service-autorun", "--disable-sync",
        "--disable-features=msEdgeIdentity,msImplicitSignin,msEdgeSyncPromo,"
        "EdgeIdentity,msEdgeAccountConsistency,EdgeCollections,"
        "msEdgeWebCapture,EdgeSidebar,msEdgeWorkspaces,"
        # 右键拖动会被 Edge 的「鼠标手势」抢走（弹前进/后退/滚动那种提示），
        # 这几个是它可能使用的特性名，写全了总有一个生效
        "msEdgeMouseGesture,msMouseGesture,EdgeMouseGesture,"
        "mouse_gesture,msEdgeGestures,msEdgeMouseGestureSupported,"
        "msEdgeMouseGestureDefaultEnabled",
        "--disable-background-networking",
        "--hide-crash-restore-bubble",
        # 关掉 Edge 的「后台继续运行」，否则最后一个窗口关掉后 Edge 进程还赖着，
        # 我们盯窗口的逻辑虽然照样能退出，但会留下一个没用的浏览器进程
        "--disable-background-mode",
    ]
    try:
        return subprocess.Popen(args, stdout=subprocess.DEVNULL,
                                stderr=subprocess.DEVNULL, stdin=subprocess.DEVNULL)
    except Exception:
        return None


def _console_hwnd():
    """本进程的控制台窗口。它的标题含「Zip2mmd」以外的字样，前缀匹配会把它误认成应用窗口，
    误认的后果就是：关掉黑框时找不到真正要盯的窗口，进程和端口一直挂着。"""
    try:
        import ctypes
        return ctypes.windll.kernel32.GetConsoleWindow() or None
    except Exception:
        return None


def _find_app_hwnd(title, exclude=None):
    """按窗口标题找应用窗口（取最后一个）。
    只做「等于」或「以它开头」的匹配：Edge 有时会在标题后面加配置文件后缀。"""
    try:
        import ctypes
        import ctypes.wintypes as wt
    except Exception:
        return None
    u = ctypes.windll.user32
    exclude = set(exclude or ())
    console = _console_hwnd()
    if console:
        exclude.add(console)
    found = []
    EnumProc = ctypes.WINFUNCTYPE(ctypes.c_bool, wt.HWND, wt.LPARAM)

    def _cb(h, _l):
        if h in exclude or not u.IsWindowVisible(h):
            return True
        cls = ctypes.create_unicode_buffer(64)
        u.GetClassNameW(h, cls, 64)
        if cls.value == 'ConsoleWindowClass':
            return True
        n = u.GetWindowTextLengthW(h)
        if not n:
            return True
        buf = ctypes.create_unicode_buffer(n + 1)
        u.GetWindowTextW(h, buf, n + 1)
        t = buf.value.strip()
        if t == title or t.startswith(title + ' ') or t.startswith(title + ' - '):
            found.append(h)
        return True

    try:
        u.EnumWindows(EnumProc(_cb), 0)
    except Exception:
        return None
    return found[-1] if found else None


_QUIT = threading.Event()


def _window_alive(hwnd):
    try:
        import ctypes
        u = ctypes.windll.user32
        return bool(hwnd) and bool(u.IsWindow(hwnd)) and bool(u.IsWindowVisible(hwnd))
    except Exception:
        return False


@app.route("/api/quit", methods=["POST"])
def api_quit():
    """页面上的「退出程序」：让主循环立刻收尾（关服务、清缓存、退出进程）"""
    _QUIT.set()
    return jsonify({"ok": True})


if __name__ == "__main__":
    # pythonw.exe 启动时没有控制台，sys.stdout / sys.stderr 是 None，print 会直接抛异常。
    # 统一重定向到 _cache/app.log —— 这样双击快捷方式可以完全不出黑框，
    # 出问题也能在这个日志里看。
    if sys.stdout is None or sys.stderr is None:
        os.makedirs(CACHE_DIR, exist_ok=True)
        try:
            _log = open(os.path.join(CACHE_DIR, "app.log"), "a", encoding="utf-8", buffering=1)
        except Exception:
            _log = None

        class _Sink(object):
            def write(self, *_a):
                return 0

            def flush(self, *_a):
                pass

        if sys.stdout is None:
            sys.stdout = _log or _Sink()
        if sys.stderr is None:
            sys.stderr = _log or _Sink()

    ensure_dirs()
    # --skip-cleanup：开发/调试启动用，跳过启动时的过期缓存清理（正常启动无需此参数）
    if "--skip-cleanup" not in sys.argv:
        cleanup_cache()
        prune_extract_cache()
    load_enc_cache()
    cfg = load_config()
    # 外部工具路径从配置里取（代码里不再写死作者机器的路径，方便打包分发）
    for _key, _var in (("seven_zip", "SEVEN_ZIP"), ("unrar", "UNRAR"), ("pmx_editor", "PMX_EDITOR")):
        _v = (cfg.get(_key) or "").strip()
        if _v and os.path.isfile(_v):
            globals()[_var] = _v
    if not SEVEN_ZIP:
        print("  [!] 没找到 7z.exe：压缩包功能不可用。装 7-Zip，或在 config.json 里写 \"seven_zip\"。")
    threading.Thread(target=prewarm_encryption, args=(cfg["watch_dirs"],), daemon=True).start()
    PORT = 5678
    for i, a in enumerate(sys.argv):
        if a == "--port" and i + 1 < len(sys.argv):
            PORT = int(sys.argv[i + 1])
        elif a.startswith("--port="):
            PORT = int(a.split("=", 1)[1])
    url = f"http://127.0.0.1:{PORT}/"
    print("=" * 62)
    print("  Zip2mmd v1.0  ·  压缩包预览工具")
    print("=" * 62)
    print(f"  7z       : {SEVEN_ZIP}")
    print(f"  PMXEditor: {PMX_EDITOR}")
    print(f"  监控目录 : {cfg['watch_dirs']}")
    print(f"  默认密码 : {cfg.get('password')}")
    print(f"  缓存目录 : {CACHE_DIR}")
    print("-" * 62)
    print(f"  访问地址 : {url}")
    print("  关掉应用窗口 = 程序退出（想用普通浏览器加参数 --browser）")
    print("=" * 62)

    from werkzeug.serving import make_server
    try:
        srv = make_server("127.0.0.1", PORT, app, threaded=True)
    except OSError:
        # 端口已被占用：多半是工具已经在跑。别再报一串红字，直接把浏览器指过去。
        print(f"  端口 {PORT} 已被占用（工具应该已经在运行），直接打开浏览器。")
        import webbrowser
        webbrowser.open(url)
        sys.exit(0)
    t = threading.Thread(target=srv.serve_forever, daemon=True)
    t.start()

    install_console_cleanup()
    wipe_on_exit = _should_wipe()
    if wipe_on_exit:
        print("  退出时自动清空解压/PMX 缓存（想保留加参数 --keep-cache）")

    def _finish():
        try:
            srv.shutdown()
        except Exception:
            pass
        if wipe_on_exit:
            print("  正在清空缓存…")
            _wipe_now()
        time.sleep(0.2)
        os._exit(0)

    try:
        if "--browser" in sys.argv:
            import webbrowser
            print(f"  正在用默认浏览器打开 {url}")
            print("  （关掉这个黑框 = 结束程序，端口随即释放）")
            webbrowser.open(url)
            while t.is_alive() and not _QUIT.is_set():
                t.join(1)
        else:
            hwnd = None
            proc = _launch_app_window(url)
            if proc is not None:
                t0 = time.time()
                # 只等 6 秒：等太久什么都没发生，看起来就是「双击没反应」。
                while time.time() - t0 < 6:
                    hwnd = _find_app_hwnd(WINDOW_TITLE)
                    if hwnd:
                        break
                    time.sleep(0.4)

            if hwnd:
                # 正常路径：关窗口 = 进程退出 = 端口释放
                print("  应用窗口已打开。关闭窗口即结束程序（端口随即释放）。")
                while _window_alive(hwnd) and not _QUIT.is_set():
                    time.sleep(0.6)
                print("  窗口已关闭，正在退出…")
            elif proc is not None and proc.poll() is None:
                # 窗口没抓到，但 Edge 进程还在跑：盯着它，窗口关掉进程就退出
                print(f"  没抓到窗口句柄，改为跟踪浏览器进程。若看不到界面，请手动打开 {url}")
                while proc.poll() is None and not _QUIT.is_set():
                    # 中途抓到窗口就以窗口为准（更准：Edge 后台常驻也不影响）
                    h = _find_app_hwnd(WINDOW_TITLE)
                    if h:
                        while _window_alive(h) and not _QUIT.is_set():
                            time.sleep(0.6)
                        break
                    time.sleep(0.6)
                print("  窗口已关闭，正在退出…")
            else:
                # 连窗口都没起来：退到默认浏览器，进程跟随这个黑框
                print(f"  未能启动应用窗口，改用默认浏览器：{url}")
                print("  （关掉这个黑框 = 结束程序，端口随即释放）")
                import webbrowser
                webbrowser.open(url)
                while t.is_alive() and not _QUIT.is_set():
                    t.join(1)
    except KeyboardInterrupt:
        print("\n  已中断")

    _finish()
