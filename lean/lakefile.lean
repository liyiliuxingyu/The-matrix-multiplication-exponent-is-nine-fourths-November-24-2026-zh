import Lake

open Lake DSL

/-- 包名、版本和隐式变量设置与原证明工程一致；Lean 版本由 lean-toolchain 固定。 -/
package OAI where
  version := v!"0.1.0"
  fixedToolchain := true
  leanOptions := #[⟨`autoImplicit, false⟩]

-- 锁定与 OpenAI 原工程一致的 mathlib 提交；其传递依赖记录在 lake-manifest.json 中。
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"

-- OAI 目录中只收录入口的本地依赖。默认构建会检查目录中全部 Lean 模块。
@[default_target] lean_lib OAI where
  globs := #[.submodules `OAI]
