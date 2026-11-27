# GAlgebra Lean 编译与核验报告

核验日期为 **2026-11-27（北京时间）**。核验对象为以 Git 标签 `v2.1.0`（`cc3c68d`）为基线的工作树，具体输入由归档中的 49 项 SHA-256 确定。配套正式稿共 152 页。[核验对象与输入集合摘要](LEAN_BUILD_EVIDENCE.txt#L3)

## 编译摘要

| 检查 | 结果 | 实测范围 |
| --- | --- | --- |
| 清洁构建 | 通过 | 46 个 Lake 作业，20.518 秒，构建警告 0 条。 |
| 内核复核 | 通过 | `leanchecker` 分别复核 `GAlgebra` 和 `Audit`。 |
| 类型与公理依赖 | 通过 | `Audit.lean` 对映射中的 399 个不同声明逐项执行 `#check` 和 `#print axioms`。 |
| TeX–Lean 映射 | 通过 | 6 项公开引文、160 条 TeX–Lean 映射、源码索引中的 377 个 Lean 定理。主线对有限零点核验的依赖为 0。 |

## 核验报告

### 工具链与输入

- 固定工具链为 `leanprover/lean4:v4.36.0`。实测平台为 `x86_64-w64-windows-gnu`，Lean 提交为 `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`，Lake 版本为 `5.0.0-src+611c117`。[版本输出](LEAN_BUILD_EVIDENCE.txt#L12)
- 主库导入闭包有 20 个项目模块，审计入口有 22 个，均计入入口自身。直接导入的官方基础模块为 `Init`，Lake 外部包数为 0。`Audit` 另导入 `GAlgebra.ZetaWindow` 核验附录。[主线依赖检查](LEAN_BUILD_EVIDENCE.txt#L1815)
- 独立副本中的 26 项 Lean 输入逐项与仓库字节一致。正式稿入口、TeX 分节、映射脚本、索引和文献表共 23 项亦已登记。[Lean 输入 SHA-256](LEAN_BUILD_EVIDENCE.txt#L1836) · [映射输入 SHA-256](LEAN_BUILD_EVIDENCE.txt#L1864)

### 实测命令

将 `g_algebra_rh_ns/lean/` 的受版本管理文件复制到 `out/` 下的新目录。Lean 与 Lake 命令在独立副本中运行，映射脚本从仓库根目录运行。各次调用的耗时单独计量。

| 命令 | 退出码 | 耗时（秒） |
| --- | ---: | ---: |
| `lean --version` | 0 | 0.123 |
| `lake --version` | 0 | 0.130 |
| `lake build` | 0 | 20.518 |
| `lake env leanchecker GAlgebra` | 0 | 12.077 |
| `lake env leanchecker Audit` | 0 | 4.028 |
| `lake env lean Audit.lean` | 0 | 2.021 |
| `python -B g_algebra_rh_ns/check_mapping.py` | 0 | 0.429 |

附录另行抽样复算高度 192 的水平证书及其后的首个变号区间，输出 `some (74, 84)` 和 `some [true]`，分别对应零点计数、弦数和变号检查。归档收录了可重跑的 Lean 输入。[抽样命令与输出](LEAN_BUILD_EVIDENCE.txt#L1831)

### 公理依赖

下表按每个声明的完整传递公理集合计数。同一声明在多条映射中出现时只计一次。[完整声明类型及传递公理输出](LEAN_BUILD_EVIDENCE.txt#L52)

| 传递公理集合 | 声明数 |
| --- | ---: |
| 空集 | 109 |
| `Quot.sound` | 5 |
| `propext` | 37 |
| `Classical.choice`、`Quot.sound` | 1 |
| `Quot.sound`、`propext` | 46 |
| `Classical.choice`、`Quot.sound`、`propext` | 201 |
| **合计** | **399** |

### 证明覆盖范围

十四项法空间结果依定理的实际陈述验收，包括七项双向等价、六项充分回读和一项精确读数。覆盖原假设、定义域和完整量词的母体见证 $\pi_\sigma:M_\sigma$ 经已证正向回读 $D_\sigma:M_\sigma\Rightarrow P_\sigma$，原命题即在 $D_\sigma(\pi_\sigma)$ 处证毕。[验收标准](AGENTS.md#法空间回读的验收标准) · [逐项进度与覆盖域](g_algebra_rh_ns/README.md#整体证明义务完成进度表)

在经典黎曼分型，命题 7.24 给出所列多项式乘积族在任意因子数下的统一正性。定理 7.25 在实际预解式的极点上证明 $\mathcal A=1\Longleftrightarrow\mathsf E_\zeta$。若对每一对满足 $p>99q$ 的正整数 $p,q$ 都有 $\sup_{k\ge1}E_{kp,kq}<\infty$，则得到覆盖全部实多项式的 $\pi_\zeta$。正向回读 $D_\zeta(\pi_\zeta)$ 完成原命题的证明。[乘积族及其量词](g_algebra_rh_ns/parts/spectral_moments.texinc#L994) · [全方向判据与正向回读](g_algebra_rh_ns/parts/spectral_moments.texinc#L1031)

Lean 对应核验乘积预算、两条矩下界所用的代数余量、乘积的幂恒等式，以及在阿基米德有序环中由有界正整数幂推出底数至多为一。实际谱的方向上确界、Hilbert 空间完备化和解析回读由正文证明。附录 B.8、B.9 分别给出高度 $0<\Im\rho\le1270$ 内的 $871$ 个临界线单零点及 $99<p/q\le715716$ 的半径下界。[TeX–Lean 证明索引](g_algebra_rh_ns/proof-index.md) · [有限窗口命题](g_algebra_rh_ns/parts/zeta_window.texinc#L284) · [窗口的斜率范围](g_algebra_rh_ns/parts/zeta_window.texinc#L315)

本报告按仓库级维护文档的 Apache License 2.0 许可条款提供。[仓库许可范围](README.md#许可)
