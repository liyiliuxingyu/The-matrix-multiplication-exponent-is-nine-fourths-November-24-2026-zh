#!/usr/bin/env python3
"""读取 Lean 注释及 import，并核对本工程的中文注释是否改变了非注释代码。

运行示例：
    python lexlean.py imports Foo.lean
    python lexlean.py comments Foo.lean
    python lexlean.py verify path/to/original path/to/translated

比较保留代码行顺序、行首缩进、行内空白及完整字面量，只忽略注释、
纯空白行和代码行末空白。这个保守的源码检查与运行 Lean 的内核检查互为补充。
"""
import argparse
import difflib
import hashlib
import json
import re
import sys
from dataclasses import dataclass, asdict
from pathlib import Path


@dataclass(frozen=True)
class Comment:
    """start/end 是 Python 字符下标，区间左闭右开；line 从 1 起算。"""

    start: int
    end: int
    kind: str
    text: str
    line: int


_CHAR = re.compile(r"'(?:[^'\\\n]|\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|u\{[0-9a-fA-F]+\}|[^\n]))'")
_RAW = re.compile(r'r(#{0,})"')
_IMPORT = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(.+)$")
_MODULE = re.compile(r"(?:[^\W\d]|_)[\w'.]*\Z", re.UNICODE)


def _error(source, start, message):
    return ValueError(f"第 {source.count(chr(10), 0, start) + 1} 行：{message}")


def _string_end(source, start):
    pos = start + 1
    while pos < len(source):
        if source[pos] == '"':
            return pos + 1
        pos += 2 if source[pos] == "\\" else 1
    raise _error(source, start, "字符串缺少闭合双引号")


def _spans(source):
    """依次产生 (kind, start, end)，源码中的每一个字符恰属其中一段。"""
    pos = 0
    plain_start = 0
    while pos < len(source):
        if source.startswith("--", pos):
            end = source.find("\n", pos + 2)
            end = len(source) if end == -1 else end
            kind = "line"
        elif source.startswith("/-", pos):
            kind = "module" if source.startswith("/-!", pos) else (
                "doc" if source.startswith("/--", pos) else "block"
            )
            depth = 1
            end = pos + 2
            while depth and end < len(source):
                if source.startswith("/-", end):
                    depth += 1
                    end += 2
                elif source.startswith("-/", end):
                    depth -= 1
                    end += 2
                else:
                    end += 1
            if depth:
                raise _error(source, pos, "块注释未闭合")
        elif source[pos] == "«":
            end = source.find("»", pos + 1)
            if end == -1:
                raise _error(source, pos, "带引号的标识符未闭合")
            end += 1
            kind = "literal"
        elif source[pos] == '"':
            end = _string_end(source, pos)
            kind = "literal"
        elif source[pos] == "r" and (
            pos == 0 or not (source[pos-1].isalnum() or source[pos-1] in "_'")
        ) and (match := _RAW.match(source, pos)):
            closing = '"' + match.group(1)
            end = source.find(closing, match.end())
            if end == -1:
                raise _error(source, pos, "原始字符串未闭合")
            end += len(closing)
            kind = "literal"
        elif source[pos] == "'" and (match := _CHAR.match(source, pos)):
            end = match.end()
            kind = "literal"
        else:
            pos += 1
            continue
        if pos > plain_start:
            yield "code", plain_start, pos
        yield kind, pos, end
        pos = plain_start = end
    if plain_start < len(source):
        yield "code", plain_start, len(source)


def comments(source):
    """列出全部最外层注释（保留嵌套内容及起始行号）。"""
    result = []
    line = 1
    for kind, start, end in _spans(source):
        if kind not in ("code", "literal"):
            result.append(Comment(start, end, kind, source[start:end], line))
        line += source.count("\n", start, end)
    return result


def code_lines(source):
    """返回可比较的 Lean 代码行；对字面量单独编码，保留其内部换行和空格。"""
    pieces = []
    for kind, start, end in _spans(source):
        if kind == "code":
            pieces.append(source[start:end])
        elif kind == "literal":
            # NUL 用于标记字符串或字符边界，防止与普通代码混淆。
            pieces.append("\0" + json.dumps(source[start:end], ensure_ascii=False) + "\0")
        else:
            # 空格防止两侧的标识符合并，换行保留 Lean 的排版边界。
            pieces.append(" " + "\n" * source.count("\n", start, end))
    return tuple(line.rstrip() for line in "".join(pieces).split("\n") if line.strip())


def imports(source):
    """提取本工程文件中的 import，包括带 public、meta 或 all 的导入。"""
    modules = []
    for line in code_lines(source):
        match = _IMPORT.fullmatch(line)
        if match:
            for name in match.group(1).split():
                if not _MODULE.fullmatch(name):
                    raise ValueError(f"未识别的 import 模块名：{name!r}")
                modules.append(name)
    return modules


def equivalent(original, translated):
    return code_lines(original) == code_lines(translated)


def code_hash(source):
    return hashlib.sha256("\n".join(code_lines(source)).encode("utf-8")).hexdigest()


def _files(path):
    if path.is_file():
        return {Path("."): path}
    if not path.is_dir():
        raise FileNotFoundError(path)
    return {
        f.relative_to(path): f for f in path.rglob("*.lean")
        if ".lake" not in f.relative_to(path).parts and ".git" not in f.relative_to(path).parts
    }


def verify(original, translated):
    left, right = _files(original), _files(translated)
    if not left and not right:
        raise ValueError("两个目录中均未发现 Lean 文件")
    errors = 0
    for key in sorted(left.keys() | right.keys()):
        if key not in right or key not in left:
            print(f"文件集合不同：{key}", file=sys.stderr)
            errors += 1
            continue
        a = code_lines(left[key].read_text(encoding="utf-8"))
        b = code_lines(right[key].read_text(encoding="utf-8"))
        if a != b:
            errors += 1
            for row in difflib.unified_diff(a, b, str(left[key]), str(right[key]), n=1, lineterm=""):
                print(row.replace("\0", ""), file=sys.stderr)
    if errors:
        print(f"{errors} 个文件未通过检查。", file=sys.stderr)
        return 1
    print(f"{len(left)} 个 Lean 文件的非注释代码与字面量一致。")
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    subs = parser.add_subparsers(dest="action", required=True)
    for action in ("imports", "comments", "hash"):
        sub = subs.add_parser(action)
        sub.add_argument("source", type=Path)
    sub = subs.add_parser("verify")
    sub.add_argument("original", type=Path)
    sub.add_argument("translated", type=Path)
    args = parser.parse_args()
    try:
        if args.action == "verify":
            return verify(args.original, args.translated)
        source = args.source.read_text(encoding="utf-8")
        if args.action == "imports":
            print("\n".join(imports(source)))
        elif args.action == "hash":
            print(code_hash(source))
        else:
            print(json.dumps([asdict(c) for c in comments(source)], ensure_ascii=False, indent=2))
        return 0
    except (OSError, ValueError) as exc:
        print(exc, file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
