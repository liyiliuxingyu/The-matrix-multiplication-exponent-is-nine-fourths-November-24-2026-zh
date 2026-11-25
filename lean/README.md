# 矩阵乘法指数的 Lean 证明（中文注释版）

从 [ExactExponent.lean](OAI/LinearAlgebra/SpectralBooks/ExactExponent.lean) 可读到论文的三个主定理。目录中收录了这个入口直接或间接导入的全部 592 个 OpenAI 证明模块。展开每个目录即可阅读源码。若想沿方阵下界的论证一直读到批量判重，可从[中文证明路径导读](路径导读.md)开始。

原证明来自 OpenAI 的 2026 年 11 月 24 日预印本及配套代码。本版在保留 Lean 声明、证明项和标识符的基础上添加简体中文注释。来源固定为 [openai/math 的提交 3344da5](https://github.com/openai/math/tree/3344da59991ed94f9ba711217b29c1d760badfa6/lean)。[原版入口文件](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/LinearAlgebra/SpectralBooks/ExactExponent.lean) · [论文中文译本](../矩阵乘法指数为四分之九_中文译本.pdf) · [仓库许可证](../LICENSE)

## 定理与代码

三个定理都位于命名空间 `OAI.LinearAlgebra.SpectralBooks`，均对任意域 $F$ 成立。这里的 `formalOmega` 是计算形式矩阵乘积所需的无除法算术电路的指数。`formalAlpha` 是使 `formalOmega F 1 1 t = 2` 的 $t\in[0,1]$ 的上确界。

| 声明 | 陈述 |
| --- | --- |
| `square_exponent` | 方阵乘法的形式算术指数为 $9/4$。 |
| `dual_exponent` | 对偶矩阵乘法指数为 $1/2$。 |
| `rectangular_exponent` | 对任意实权重 $a,b,c$，分别取非负部，再从大到小排为 $x,y,z$。精确的矩形指数由下式给出。 |

$$
x+y+\frac{\max\{(x+y)z-xy,\,0\}^2}{4xyz}.
$$

在 $z=0$ 的边界上，修正项为零。Lean 中实数除法在零分母处取零。代入方阵权重 $x=y=z=1$，公式给出 $2+1/4=9/4$。若取 $(1,1,t)$ 且 $0\leq t\leq1$，分子中的正部为 $\max(2t-1,0)$，因而指数等于二的最后一个参数值是 $t=1/2$。

## 收录范围与注释

| 源码目录 | 模块数 | 内容 |
| --- | ---: | --- |
| [MatrixExponent](OAI/LinearAlgebra/MatrixExponent) | 514 | 方阵上界和下界、矩形刚性、网络构造、排序与判重归约，以及整系数电路模型 |
| [SpectralBooks](OAI/LinearAlgebra/SpectralBooks) | 28 | 形式算术指数、张量秩与各模型的衔接，汇总三个主定理 |
| [TensorSpectrum](OAI/LinearAlgebra/TensorSpectrum) | 28 | 张量谱、分离、相应的乘法性与熵不等式 |
| [MatrixMultiplication](OAI/LinearAlgebra/MatrixMultiplication) | 22 | 矩阵乘法的算术程序及其成本 |

上游的 257,771 行源码中共有 5,026 处原注释。本版为模块说明、原有声明文档和行注提供中文，另有 22,552 条声明读法和 2,747 条中间推导说明。多数原文档注释保留英文对照，入口等核心文件按证明顺序另作中文讲解。辅助声明的“读法”按 Lean 陈述和证明中实际出现的表达式生成。可用原名在编辑器中跳转到完整定义和证明。

项目固定使用 Lean 4.34.1 和 [mathlib 的提交 d13f23b](https://github.com/leanprover-community/mathlib4/tree/d13f23b723b8a846827a245b89c10fc7d3f11612)。外部依赖由 [Lake 清单](lake-manifest.json)锁定，构建时取回。OpenAI 的比较器题面另有用于对比陈述的占位文件；本目录收录的是主定理实际导入的证明。

## 本仓库补充的非标量门数下界

设 $F$ 为任意域，$n\ge2$。若一个形式算术电路正确计算两个 $n\times n$ 矩阵的乘积，记 $q$ 为非标量乘除门数，则论文推论 1.2 给出

$$
q\;\ge\;\left\lceil \frac{n^{9/4}}{2}\right\rceil.
$$

乘法在两个输入都非常数时计一次，除法在除数非常数时计一次。常数指在输入变量的有理函数域中等于某个基域元素。例如对输入变量 $x$，$x-x$ 是常数，$1/x$ 的除法计一次。在有限域上也按形式恒等式判定。上游发布时将这个逐阶下界列为尚未形式化，本目录的三个补充文件给出所需定义和证明。[上游发布时的说明](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/379.md#matrix-multiplication)

| 文件 | 读法 |
| --- | --- |
| [NonscalarModel.lean](PaperExtensions/NonscalarModel.lean) | 在上游电路的每个门上同时记录总门数和非标量门数。两个方向的转录表明原模型中的所有计算都可按此方式计数。 |
| [NonscalarBilinearize.lean](PaperExtensions/NonscalarBilinearize.lean) | 对每条导线求关于左右矩阵输入的混合偏导。加减及标量操作保留已有的张成空间；每个收费门至多新增两个秩一项。得到有理函数域上的精确秩分解。 |
| [NonscalarLowerBound.lean](PaperExtensions/NonscalarLowerBound.lean) | 把分解特化到基域的代数闭包，得到引理 2.4 的 $\operatorname{rank}_{\overline F}(T_n)\le 2q$。若某个 $n\ge 2$ 的秩严格小于 $n^{9/4}$，则上游的有限秩判据将推出该域上的方阵指数严格小于 $9/4$。结合已证的方阵指数，得到逐阶下界并向上取整。 |

最终声明为 `OAI.LinearAlgebra.MatrixExponent.nonscalar_gate_lower_bound_of_build`，量化每个带门计数的计算及其全部输出。`nonscalar_gate_lower_bound` 给出相同结论的存在型表述。

## 复核源码和运行证明

在本目录执行以下命令。第一条仅需要 Python 3，逐个验证文件校验和、非注释代码摘要，并从主定理重新追踪全部本地导入。

```sh
python3 tools/verify-source.py
```

若已有固定提交的上游检出副本，可直接比较每一行代码、缩进和字面量，并核对每个上游 Git 对象。`--upstream` 指向上游仓库里的 `lean` 子目录。

```sh
python3 tools/verify-source.py --upstream /path/to/openai-math/lean
```

安装 elan 后，通过以下命令下载匹配的数学库缓存、构建入口及其依赖，并运行公理审计。请为 Lean 工具链和 mathlib 缓存预留磁盘空间。

```sh
lake exe cache get
sh verify-lean.sh
```

[Audit.lean](Audit.lean) 逐项打印上游三个指数定理与补充证明的传递公理依赖。允许列表沿用上游比较器的 `propext`、`Quot.sound`、`Classical.choice`。如果实际依赖超出列表，例如含有 `sorryAx`，审计命令会以失败退出。[源文件与导入清单](SOURCE-MANIFEST.json) · [GitHub 构建与公理审计记录](https://github.com/liyiliuxingyu/The-matrix-multiplication-exponent-is-nine-fourths-November-24-2026-zh/actions/workflows/verify-lean.yml)
