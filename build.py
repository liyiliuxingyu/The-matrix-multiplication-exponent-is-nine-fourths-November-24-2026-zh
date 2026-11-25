"""用 XeLaTeX 和 BibTeX 从源文件重建中文译本。"""
from pathlib import Path
from shutil import copytree, which
from subprocess import run
from tempfile import TemporaryDirectory
import sys

import pymupdf


def embed_chinese_text_map(pdf, target, cmap):
    # Fandol 的 GB1 字形编号与 Unicode 不同。显式嵌入映射以支持复制和检索。
    import re

    with pymupdf.open(pdf) as document:
        stream = None
        font_ids = {font[0] for page in document for font in page.get_fonts()}
        for font_id in sorted(font_ids):
            if document.xref_get_key(font_id, "Encoding")[1] != "/Identity-H":
                continue
            if document.xref_get_key(font_id, "ToUnicode")[0] != "null":
                continue
            children = document.xref_get_key(font_id, "DescendantFonts")[1]
            match = re.fullmatch(r"\[\s*(\d+) 0 R\s*\]", children)
            if not match:
                continue
            child = int(match.group(1))
            if document.xref_get_key(child, "CIDSystemInfo/Ordering")[1] != "GB1":
                continue
            if stream is None:
                stream = document.get_new_xref()
                document.update_object(stream, "<<>>")
                document.update_stream(stream, cmap.read_bytes())
            document.xref_set_key(font_id, "ToUnicode", f"{stream} 0 R")
        document.save(target, deflate=True)


def main():
    root = Path(__file__).resolve().parent
    for program in ("xelatex", "bibtex"):
        if which(program) is None:
            sys.exit(f"找不到 {program}，请安装含中文宏包的完整 TeX Live 或 MiKTeX。")

    with TemporaryDirectory() as temporary:
        build = Path(temporary) / "src"
        copytree(root / "src", build)
        latex = ["xelatex", "-interaction=nonstopmode", "-halt-on-error", "main.tex"]
        for command in (latex, ["bibtex", "main"], latex, latex):
            run(command, cwd=build, check=True)
        target = root / "矩阵乘法指数为四分之九_中文译本.pdf"
        embed_chinese_text_map(build / "main.pdf", target, root / "resources" / "Adobe-GB1-UCS2")
        print(target)


if __name__ == "__main__":
    main()
