# 《矩阵乘法指数为四分之九》中文译本

原著署名 OpenAI。英文预印本版本为 2026 年 11 月 24 日。本工程依照该版英文 PDF 与配套 LaTeX 源文译为简体中文。参考文献保留其出版语言、版本及标识符。

- [原始论文 PDF](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/The-matrix-multiplication-exponent-is-nine-fourths-November-24-2026/paper.pdf)
- [原始 LaTeX 源码](https://github.com/openai/math/tree/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/The-matrix-multiplication-exponent-is-nine-fourths-November-24-2026/build)

## Lean 形式化证明

[完整中文注释工程](lean/README.md)收录主定理的完整导入链，共 592 个本地模块（含入口）。[三个主定理](lean/OAI/LinearAlgebra/SpectralBooks/ExactExponent.lean)分别给出方阵指数、对偶指数和矩形通式。[中文证明路径导读](lean/路径导读.md)列出了从主定理到关键引理的跳转位置。

## 阅读和编辑

根目录的 PDF 是编译好的中文译文。original/paper.pdf 是 111 页的英文原版，Git 对象为 d8fd1a42b9cc685eb564b49aca9e947dccce9fba。译文重新分页，跨语言定位请使用节号、定理号、公式号和图号。

编辑入口为 src/main.tex。src/style.tex 控制中文排版，各节正文沿用英文项目的文件名。src/references.bib 包含原版文献数据，src/locators.tex 保留配套论文中被引用结果的编号。

## 重新编译

安装含中文支持、Fandol 字体、TikZ、XeLaTeX 和 BibTeX 的完整 TeX Live 或 MiKTeX。安装 Python 3 后，在工程目录运行：

    python -m pip install PyMuPDF
    python build.py

脚本使用临时目录完成 XeLaTeX、BibTeX 和两次 XeLaTeX 编译，将译本输出到工程根目录。它会为需要显式映射的中文字体嵌入字符映射，便于在不同 PDF 阅读器中复制或检索汉字。映射资源自带授权声明。也可在 src 目录中仅使用 TeX 编译：

    latexmk -xelatex main.tex

## 对照与校验

随包译本共 82 页。已对照全部 27 节和 65 个小节、48 条带编号的定理类结果、11 幅图、1 张表和 60 条参考文献，核对了显示公式的结构以及标签和交叉引用。数学结论按原文表述，本工程完成的是翻译与排版核对。原文有更新时，可从上述固定版本比较差异。

在未编辑的解压目录中运行 python verify.py，可核对发布文件的 SHA-256。重新编译或编辑正文后，文件校验值会随之改变。
