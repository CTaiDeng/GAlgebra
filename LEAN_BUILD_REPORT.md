# GAlgebra Lean 编译与核验报告

核验日期 **2026-11-25（北京时间）**。构建使用当前 Lean 工程源码的独立副本。

## 编译摘要

| 检查 | 结果 | 实测范围 |
| --- | --- | --- |
| 清洁构建 | 通过 | 46 个 Lake 作业，耗时 20.580 秒。 |
| 内核复核 | 通过 | `GAlgebra` 和 `Audit` 两个入口均通过 `leanchecker`。 |
| 类型与公理核验 | 通过 | 394 个映射声明逐一通过类型检查和传递公理核查。 |
| TeX–Lean 映射 | 通过 | 157 条映射。源码索引含 372 个 Lean 定理声明。 |

## 核验报告

### 工具链与输入

- 固定工具链为 `leanprover/lean4:v4.36.0`。实测为 `Lean (version 4.36.0, x86_64-w64-windows-gnu, commit 611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9, Release)` 和 `Lake version 5.0.0-src+611c117 (Lean version 4.36.0)`。
- 主库导入闭包有 20 个模块，核验入口的导入闭包有 22 个模块，计数包含各自入口。`Audit` 另外接入 `GAlgebra.ZetaWindow` 的有限零点核验。
- 直接导入的官方基础模块为 `Init`，Lake 外部包数为 0。主线到有限零点核验的依赖数为 0。
- 构建副本含 26 项 Lean 工程输入。编译后逐一核对了副本和仓库文件的 SHA-256，映射检查使用的 23 项输入也与核验前一致。[输入文件指纹清单](out/lean-build-report-20261125/inputs.json)

### 实测命令与日志

Lean 命令在独立副本 `out/lean-build-report-20261125/lean` 中运行。映射命令在仓库根目录运行。复现清洁构建时，将 `g_algebra_rh_ns/lean` 的源码和工具链配置复制到 `out/` 下的新目录，再依表执行。

| 命令 | 退出码 | 耗时（秒） | 原始记录 |
| --- | --- | --- | --- |
| `lean --version` | 0 | 0.149 | [日志](out/lean-build-report-20261125/lean-version.txt) |
| `lake --version` | 0 | 0.165 | [日志](out/lean-build-report-20261125/lake-version.txt) |
| `lake build` | 0 | 20.580 | [日志](out/lean-build-report-20261125/lake-build.txt) |
| `lake env leanchecker GAlgebra` | 0 | 12.486 | [日志](out/lean-build-report-20261125/leanchecker-main.txt) |
| `lake env leanchecker Audit` | 0 | 4.392 | [日志](out/lean-build-report-20261125/leanchecker-audit.txt) |
| `lake env lean Audit.lean` | 0 | 2.259 | [日志](out/lean-build-report-20261125/audit.txt) |
| `python -B .\g_algebra_rh_ns\check_mapping.py` | 0 | 0.280 | [日志](out/lean-build-report-20261125/mapping.txt) |

构建日志中报告的警告数为 0。[Lean 命令结果](out/lean-build-report-20261125/lean-steps.json) · [映射命令结果](out/lean-build-report-20261125/mapping-step.json)

### 公理依赖

以下计数来自 `Audit.lean` 的 `#print axioms` 输出。每个映射声明按其传递公理集合计入一行。

| 传递公理集合 | 声明数 |
| --- | ---: |
| 空集 | 109 |
| `Quot.sound` | 5 |
| `propext` | 37 |
| `Classical.choice`、`Quot.sound` | 1 |
| `Quot.sound`、`propext` | 46 |
| `Classical.choice`、`Quot.sound`、`propext` | 196 |
| **合计** | **394** |

本次核验所得公理集合限于 `Classical.choice`、`Quot.sound`、`propext`。[声明与公理输出](out/lean-build-report-20261125/audit.txt)

### 证明覆盖范围

内核复核覆盖编译产物中的 Lean 声明及其证明项。实际算术输入、Hilbert 完备和连续 PDE 推导按证明索引所列范围在正式稿中核对。回读义务与原命题按各自已证推导的原假设、定义域、完整量词登记。[证明索引](g_algebra_rh_ns/proof-index.md) · [正式稿](20261124_g_algebra_rh_ns_formal_system.pdf) · [验收标准](AGENTS.md#法空间回读的验收标准)

本报告按仓库级维护文档的 Apache License 2.0 许可条款提供。[仓库许可范围](README.md#许可)
