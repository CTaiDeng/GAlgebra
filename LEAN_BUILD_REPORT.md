# GAlgebra Lean 编译与核验报告

核验日期为 **2026-11-28（北京时间）**。核验对象为以 Git 提交 `173b973`（`v3.1.0`）为基线的工作树，归档列出 51 项 Lean 工程、文稿、映射及验收脚本输入的 SHA-256。配套正式稿共 173 页。[核验对象与输入集合摘要](LEAN_BUILD_EVIDENCE.txt#L3)

## 编译摘要

| 检查 | 结果 | 实测范围 |
| --- | --- | --- |
| 清洁构建 | 通过 | 48 个 Lake 作业，21.578 秒，构建警告 0 条。 |
| 内核复核 | 通过 | `leanchecker` 分别复核 `GAlgebra` 和 `Audit`。 |
| 类型与公理依赖 | 通过 | `Audit.lean` 对映射中的 434 个不同声明逐项执行 `#check` 和 `#print axioms`。 |
| TeX–Lean 映射 | 通过 | 6 项公开引文、170 条 TeX–Lean 映射、源码索引中的 410 个 Lean 定理。主线对有限零点核验的依赖为 0。 |

## 核验报告

### 工具链与输入

- 固定工具链为 `leanprover/lean4:v4.36.0`。实测平台为 `x86_64-w64-windows-gnu`，Lean 提交为 `611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9`，Lake 版本为 `5.0.0-src+611c117`。[版本输出](LEAN_BUILD_EVIDENCE.txt#L12)
- 主库导入闭包有 21 个项目模块，审计入口有 23 个，均计入入口自身。直接导入的官方基础模块为 `Init`，Lake 外部包数为 0。`Audit` 另导入 `GAlgebra.ZetaWindow` 核验附录。[主线依赖检查](LEAN_BUILD_EVIDENCE.txt#L1999)
- 独立副本中的 27 项 Lean 输入逐项与仓库字节一致。正式稿入口、TeX 分节、映射脚本、十四项验收脚本、索引和文献表共 24 项亦已登记。[Lean 输入 SHA-256](LEAN_BUILD_EVIDENCE.txt#L2124) · [映射输入 SHA-256](LEAN_BUILD_EVIDENCE.txt#L2153)

### 实测命令

将 `g_algebra_rh_ns/lean/` 的受版本管理文件复制到 `out/` 下的新目录。Lean 与 Lake 命令在独立副本中运行，映射脚本从仓库根目录运行。各次调用的耗时单独计量。

| 命令 | 退出码 | 耗时（秒） |
| --- | ---: | ---: |
| `lean --version` | 0 | 0.119 |
| `lake --version` | 0 | 0.121 |
| `lake build` | 0 | 21.578 |
| `lake env leanchecker GAlgebra` | 0 | 14.192 |
| `lake env leanchecker Audit` | 0 | 4.281 |
| `lake env lean Audit.lean` | 0 | 2.017 |
| `python -B g_algebra_rh_ns/check_mapping.py` | 0 | 0.260 |
| `python -B audit/check_obligations.py --receipt out/trivial_fiber_20261128/verification/obligations.json` | 0 | 0.190 |
| `lake env lean ../RankOneDependencies.lean` | 0 | 61.971 |
| `lake env lean ../RankOneSample.lean` | 0 | 1.559 |
| `lake env lean ../FiniteWindowSample.lean` | 0 | 20.285 |

本次在独立副本中复核高度 192 及其后首个变号区间，输出 `some (74, 84)` 和 `some [true]`，分别对应零点计数、弦数和变号检查。归档收录了可重跑的 Lean 输入。[抽样命令与输出](LEAN_BUILD_EVIDENCE.txt#L2119)

### 公理依赖

下表按每个声明的完整传递公理集合计数。同一声明在多条映射中出现时只计一次。[完整声明类型及传递公理输出](LEAN_BUILD_EVIDENCE.txt#L53)

| 传递公理集合 | 声明数 |
| --- | ---: |
| 空集 | 113 |
| `Quot.sound` | 5 |
| `propext` | 38 |
| `Classical.choice`、`Quot.sound` | 1 |
| `Quot.sound`、`propext` | 48 |
| `Classical.choice`、`Quot.sound`、`propext` | 229 |
| **合计** | **434** |

### 证明覆盖范围

十四项法空间结果均已按其陈述证毕，包括七项双向等价、六项充分回读和一项精确读数。以带外力爆破为例，Lean 声明接收同一母体解的合法性、周期性、非零性及回读映射。正文证明该回读覆盖每个正黏性，这一蕴含按充分回读结项。覆盖原量词的母体见证经保留原假设和定义域的正向回读，在 $D_\sigma(\pi_\sigma)$ 处证毕原命题。[流体回读声明](g_algebra_rh_ns/lean/GAlgebra/Targets.lean#L44) · [正文定理](g_algebra_rh_ns/parts/flow_periodic.texinc#L4950) · [逐项进度与覆盖域](g_algebra_rh_ns/README.md#整体证明义务完成进度表)

正文对固定算术近似证明局部一致收敛，用 Cauchy 系数公式得到实际 $\xi$ 的系数实现。Lean 证明每个截断的矩等式，并无须预设收敛就能证明两侧极限谓词等价。对于实际输入，极限唯一性给出自对偶平方，常数项下界允许级数除法。$-(D^2)'/D^2$ 的各阶系数加倍，对任意实多项式 $q$ 即得 $\mathcal L_{\mathbf1}(q)=2\mathcal L(q)$。给定全秩见证、其平凡分量的完备函数标识及经典正向回读，依次取 $q=tp^2,p^2$，约去 $2$ 并回读。整个证明使用现有主库和 `Init`。[正式稿定理 7.40](g_algebra_rh_ns/parts/grand_riemann.texinc#L231) · [算术输入、系数与回读](g_algebra_rh_ns/lean/GAlgebra/TrivialFiber.lean)

递归读取 `GAlgebra.grh_trivial_xi_readback` 的类型和证明项，确认其依赖实际算术近似、常数项非零、乘法求导、矩恒等式、原有约因子与回读定理。另用七个精确有理等式核验两个截断的归一化、导数符号和 $tp^2,p^2$ 两项测试。[证明项依赖与数值复核](LEAN_BUILD_EVIDENCE.txt#L2003)

十四项验收脚本核对定理 7.40 和定理 7.12 给出的经典回读。定理 7.35 属于经典纤维的独立 G-PDE 判据。Lean 核验有序复合、加权正交分解和有限带符号 Gram 差。实际热解及窗口算子的迹范数估计由正文证明。三维环面上两项全局延拓的拼接论证也见正文。[谱型声明与正文分工](g_algebra_rh_ns/proof-index.md#L129) · [两项条件延拓](g_algebra_rh_ns/parts/kinetic_limit.texinc#L596) · [验收脚本](audit/check_obligations.py) · [十四项逐项审计](src/markdown/1795704572379_GAlgebra%20十四项义务的证据链审计.md)

附录 B.8、B.9 分别给出高度 $0<\Im\rho\le1270$ 内的 $871$ 个临界线单零点及 $99<p/q\le715716$ 的半径下界。[TeX–Lean 证明索引](g_algebra_rh_ns/proof-index.md) · [有限窗口命题](g_algebra_rh_ns/parts/zeta_window.texinc#L284) · [窗口的斜率范围](g_algebra_rh_ns/parts/zeta_window.texinc#L315)

本报告按仓库级维护文档的 Apache License 2.0 许可条款提供。[仓库许可范围](README.md#许可)
