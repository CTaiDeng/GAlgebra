# GAlgebra Lean 编译与核验报告

核验日期 **2026-11-25（北京时间）**。构建使用 GAlgebra 1.0.0 Lean 源码的独立副本。[构建与核验记录](LEAN_BUILD_EVIDENCE.txt)

## 编译摘要

| 检查 | 结果 | 实测范围 |
| --- | --- | --- |
| 清洁构建 | 通过 | 46 个 Lake 作业，耗时 23.178 秒。 |
| 内核复核 | 通过 | `GAlgebra` 和 `Audit` 两个入口均通过 `leanchecker`。 |
| 类型与公理核验 | 通过 | 394 个映射声明逐一通过类型检查和传递公理核查。 |
| TeX–Lean 映射 | 通过 | 157 条映射。源码索引含 372 个 Lean 定理声明。 |

## 核验报告

### 工具链与输入

- 固定工具链为 `leanprover/lean4:v4.36.0`。实测为 `Lean (version 4.36.0, x86_64-w64-windows-gnu, commit 611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9, Release)` 和 `Lake version 5.0.0-src+611c117 (Lean version 4.36.0)`。
- 主库导入闭包有 20 个模块，核验入口导入闭包有 22 个模块，均包含各自入口。`Audit` 另外接入 `GAlgebra.ZetaWindow` 的有限零点核验。
- 直接导入的官方基础模块为 `Init`，Lake 外部包数为 0。主线到有限零点核验的依赖数为 0。
- 已逐一核对构建副本与仓库的 26 项 Lean 输入。23 项映射输入的 SHA-256 同列于归档。[输入指纹与命令输出](LEAN_BUILD_EVIDENCE.txt)

### 实测命令

复现清洁构建时，将 `g_algebra_rh_ns/lean` 的源码和工具链配置复制到 `out/` 下的新目录。Lean 命令在该副本中运行，映射命令从仓库根目录运行。

| 命令 | 退出码 | 耗时（秒） |
| --- | --- | --- |
| `lean --version` | 0 | 0.151 |
| `lake --version` | 0 | 0.146 |
| `lake build` | 0 | 23.178 |
| `lake env leanchecker GAlgebra` | 0 | 12.654 |
| `lake env leanchecker Audit` | 0 | 4.599 |
| `lake env lean Audit.lean` | 0 | 1.826 |
| `python -B g_algebra_rh_ns/check_mapping.py` | 0 | 0.277 |

本次构建日志中的警告数为 0。各命令的退出码、构建任务状态、声明类型和公理输出均可在归档中核对。[构建与核验记录](LEAN_BUILD_EVIDENCE.txt)

### 公理依赖

每个映射声明按 `Audit.lean` 报告的传递公理集合计数。

| 传递公理集合 | 声明数 |
| --- | ---: |
| 空集 | 109 |
| `Quot.sound` | 5 |
| `propext` | 37 |
| `Classical.choice`、`Quot.sound` | 1 |
| `Quot.sound`、`propext` | 46 |
| `Classical.choice`、`Quot.sound`、`propext` | 196 |
| **合计** | **394** |

本次核验的公理依赖限于 `Classical.choice`、`Quot.sound`、`propext`。[声明类型与公理输出](LEAN_BUILD_EVIDENCE.txt)

### 证明覆盖范围

Lean 内核核验编译产物里的声明类型和证明项。证明索引逐项标明 Lean 声明建立的结论和正文承担的连续分析。已证的双向等价、充分回读和精确读数按各自陈述验收。具有覆盖原量词的母体证明时，应用已证正向回读即得原命题的证明。[证明索引](g_algebra_rh_ns/proof-index.md) · [专项进度表](g_algebra_rh_ns/README.md#整体证明义务完成进度表) · [验收标准](AGENTS.md#法空间回读的验收标准)

本报告按仓库级维护文档的 Apache License 2.0 许可条款提供。[仓库许可范围](README.md#许可)
