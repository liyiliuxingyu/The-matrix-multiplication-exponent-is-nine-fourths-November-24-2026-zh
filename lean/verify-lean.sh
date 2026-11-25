#!/bin/sh
# 在本工程目录运行；任意构建或公理核对错误都会得到非零退出码。
set -eu
cd "$(dirname "$0")"

# Lake 按 lean-toolchain 选取工具链，按清单中固定的提交解析 mathlib 等依赖。
lake env lean --version
# 显式构建入口模块及其全部本地依赖，不编译无需使用的第三方工程。
lake build +OAI.LinearAlgebra.SpectralBooks.ExactExponent
# 使用刚生成的模块运行公理核对。Audit.lean 会显示依赖并拒绝清单外的公理。
lake env lean Audit.lean
