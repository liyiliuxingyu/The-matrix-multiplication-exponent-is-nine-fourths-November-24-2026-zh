#!/usr/bin/env python3
"""从主定理重走 import 依赖，核对文件、校验和以及可选的上游快照。"""
import argparse
import hashlib
import json
import sys
from pathlib import Path

from lexlean import code_hash, equivalent, imports


def git_blob(data):
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def verify(root, upstream):
    manifest = json.loads((root / "SOURCE-MANIFEST.json").read_text(encoding="utf-8"))
    modules = manifest["modules"]
    entry = manifest["entry"]
    listed = set(modules)
    actual = {f.relative_to(root).with_suffix("").as_posix().replace("/", ".")
              for f in (root / "OAI").rglob("*.lean")}
    if actual != listed:
        raise ValueError(f"本地模块集合有差异：{sorted(actual ^ listed)}")
    pending, reached = [entry], set()
    edges = 0
    while pending:
        name = pending.pop()
        if name in reached:
            continue
        if name not in listed:
            raise ValueError(f"缺少入口依赖的模块：{name}")
        reached.add(name)
        record = modules[name]
        path = Path(*name.split(".")).with_suffix(".lean")
        data = (root / path).read_bytes()
        source = data.decode()
        if hashlib.sha256(data).hexdigest() != record["sha256_annotated"]:
            raise ValueError(f"中文注释版文件校验失败：{path}")
        if code_hash(source) != record["sha256_code"]:
            raise ValueError(f"去注释后的代码校验失败：{path}")
        deps = imports(source)
        if deps != record["imports"]:
            raise ValueError(f"导入的模块或次序有差异：{path}")
        local = [dep for dep in deps if dep.startswith("OAI.")]
        pending.extend(local)
        edges += len(local)
        if upstream is not None:
            original = (upstream / path).read_bytes()
            if git_blob(original) != record["git_blob_upstream"]:
                raise ValueError(f"原文件与指定上游版本不一致：{path}")
            if not equivalent(original.decode(), source):
                raise ValueError(f"中文注释修改了原文件中的非注释代码：{path}")
    if reached != listed:
        raise ValueError(f"清单中存在从入口无法到达的模块：{sorted(listed - reached)}")
    print(f"通过：{len(reached)} 个模块，{edges} 条本地直接导入。")
    if upstream is not None:
        print("全部原文件的 Git blob 与记录相符，原版与中文版的非注释代码逐行相同。")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=Path, help="固定提交的 openai/math 检出副本中的 lean 目录")
    args = parser.parse_args()
    try:
        verify(Path(__file__).resolve().parents[1], args.upstream)
    except (KeyError, OSError, ValueError) as error:
        sys.exit(str(error))
