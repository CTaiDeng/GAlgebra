# GAlgebra

> Gao, Z. (2026). G 代数在数论与动力学/PDE 中的统一证明框架:分型求解、法空间回读与 Lean 形式化(A Unified G-Algebra Proof Framework for Number Theory and Dynamics/PDEs: Type-Specific Solution Methods, Law-Space Readback, and Lean Formalization) (Version v3.0). Zenodo. <https://doi.org/10.5281/zenodo.24583564>

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24583564.svg)](https://doi.org/10.5281/zenodo.24583564)

### 作者：GaoZheng（高政）

[作者博客](https://mymetamathematics.blogspot.com) · [![ORCID](https://orcid.org/sites/default/files/images/orcid_16x16.png) 0009-0008-3013-6626](https://orcid.org/0009-0008-3013-6626)

## 项目目的

GAlgebra 的目标是在同一 G 母体上构造数论与动力学/PDE 两族原命题的经典证明。投影域尚未构造出见证时，保留实际输入、合法域与完整量词，沿任务商保结构上卷到 G 母体，再下卷到相应分型内核直接求解。纤维丛协变与多复合反身提供统一闭合，估计覆盖整个合法复合族。回读以同一商坐标和随附证据下的目标读数一致为条件，将母体见证送回投影域。[任务商回读](g_algebra_rh_ns/parts/g_pde_chain.texinc#L4) · [共同证明链](g_algebra_rh_ns/parts/proof_guide.texinc)

## 两族证明义务

以下列出原命题及其量词。各项已证的定理、母体前提和适用域见[专项进度表](g_algebra_rh_ns/README.md#整体证明义务完成进度表)。

### 数论族

- **经典黎曼猜想（最初义务）**。这是有理数域上全秩大黎曼猜想的秩一平凡特例。取导子 $1$ 的平凡特征和虚平移 $\tau=0$，即有 $L(s,\mathbf1)=\zeta(s)$。全秩结论在这一分量上断言 $\zeta$ 的每个非平凡零点 $\rho$ 均满足 $\Re\rho=1/2$。[秩一基例](g_algebra_rh_ns/parts/grand_riemann.texinc#L4)
- **二元哥德巴赫猜想**。证明每个偶数 $N\ge 4$ 都能写成两个素数之和。
- **孪生素数猜想**。证明对任意阈值 $X$，存在 $p>X$，使 $p$ 和 $p+2$ 均为素数。
- **Hardy–Littlewood 素数 $k$ 元组猜想**。对每个 $k\ge 1$ 和每组固定、互异、可容许且以 $0$ 为首项的整数偏移 $\mathbf h$，证明素数元组的对数加权计数满足 $R_{\mathbf h}(X)\sim\mathfrak S(\mathbf h)X$，其中 $\mathfrak S(\mathbf h)$ 为该组的奇异级数。
- **勒让德猜想**。证明对每个整数 $m\ge 1$，开区间 $(m^2,(m+1)^2)$ 内存在素数。
- **有理数域上的全秩大黎曼猜想**。对每个 $n\ge 1$ 和 $GL_n(\mathbb A_{\mathbb Q})$ 的每个单位归一化尖点自守表示 $\pi$，证明标准 $L(s,\pi)$ 的全部非平凡零点均位于临界线。秩一涵盖经典黎曼猜想及原始 Dirichlet 特征的广义黎曼猜想。[谱目标与全秩量词](g_algebra_rh_ns/parts/targets.texinc#L182)

### 动力学/PDE 族

- **带光滑紧支外力的 Navier–Stokes 有限时间爆破（最初义务）**。对每个黏性系数 $\nu>0$，证明在 $\mathbb R^3$ 上存在从零初值出发、在 $0\le t<1$ 光滑且动能一致有界的不可压缩解。外力在 $\mathbb R^3\times(0,\infty)$ 上光滑紧支，且速度满足 $\limsup_{t\uparrow 1}\lVert u(t)\rVert_\infty=\infty$。[爆破目标与回读前提](g_algebra_rh_ns/parts/targets.texinc#L157)
- **硬球到不可压缩 Navier–Stokes–Fourier 的幂律联合极限**。在三维环面上固定相容的近 Maxwell 制备和共同光滑时间窗 $[0,T]$，证明存在独立于硬球直径 $a$ 的 $0<\beta<1$ 和 $\kappa>0$，使 $\delta=a^\beta$、$R_a=a^{-\kappa}$ 时，$\mathbb E[N]a^2\sim\delta^{-1}$，归一化密度与速度矩在 $L^\infty([0,T];L_x^1)$ 中收敛到给定宏观解的密度与速度。联合极限包含三个子义务。[联合极限定义](g_algebra_rh_ns/parts/targets.texinc#L228)

  - 硬球多体相流到 BBGKY 层级，在给定合法粒子参数与可积入射接触迹时精确读取接触通量。
  - BBGKY 层级到硬球玻尔兹曼方程，在同一制备和粒子时间窗上建立碰撞项与速度矩的极限。
  - 硬球玻尔兹曼方程到不可压缩 Navier–Stokes–Fourier 方程，在共同光滑时间窗上回读应力、热通量和运输系数。

- **三维环面硬球玻尔兹曼大数据经典适定性**。对任意幅度的光滑、非负、在速度方向快速衰减且质量与能量有限的初值，证明空间非齐次硬球玻尔兹曼方程有唯一的全局非负经典解。
- **三维周期无外力 Navier–Stokes 全局光滑性**。对每个 $\nu>0$ 和每个光滑周期无散度初速度，证明无外力不可压缩 Navier–Stokes 方程有全局光滑周期速度与配套压力。[两项全局义务的原量词](g_algebra_rh_ns/parts/targets.texinc#L246)

### 已证法空间结果与原命题验收

**十四项义务对应的法空间结果均已按各自的定理陈述证毕**，包括 **7 项双向等价、6 项充分回读和 1 项精确读数**。例如，带外力爆破项已证明，若单位黏性下的完整周期方程存在合法非零解，则对每个正黏性均有满足题设的爆破解。这条蕴含按充分回读结项。[专项进度表](g_algebra_rh_ns/README.md#整体证明义务完成进度表) · [带外力爆破回读定理](g_algebra_rh_ns/parts/flow_periodic.texinc#L4950)

覆盖原量词的母体见证 $\pi_\sigma$ 经已证正向回读 $D_\sigma$ 给出 $D_\sigma(\pi_\sigma)$。所得推导就是原命题 $P_\sigma$ 的证明，原命题在同一回读处证毕。[验收标准](g_algebra_rh_ns/README.md#验收标准)

给定全秩法空间见证 $\Pi$，取秩一平凡分量 $\Pi(1,\mathbf1)$。该纤维的对偶乘积为 $\xi^2$，故 $R_{\mathbf1}=2R$、$\mathcal L_{\mathbf1}=2\mathcal L$。将分量中的两条矩不等式同除以 $2$，即得覆盖全部实多项式的 $\pi_\zeta$。经典命题在 $D_\zeta(\pi_\zeta)$ 处证毕。[全秩矩见证的经典特例](g_algebra_rh_ns/parts/grand_riemann.texinc#L231)

The classical Riemann hypothesis is the rank-one case of the all-ranks Grand Riemann Hypothesis over $\mathbb Q$ for the trivial character with zero imaginary shift. Given a law-space moment witness $\Pi$ for the full family, its component $\Pi(1,\mathbf1)$ tests every real polynomial. On this fiber $L(s,\mathbf1)=\zeta(s)$ and $\mathcal L_{\mathbf1}=2\mathcal L$. Dividing both moment inequalities by $2$ gives $\pi_\zeta$. The forward readback $D_\zeta(\pi_\zeta)$ completes the proof of the classical statement. [Theorem 7.40](g_algebra_rh_ns/parts/grand_riemann.texinc#L231)

## 阅读入口

- [正式稿 PDF](20261124_g_algebra_rh_ns_formal_system.pdf) · [TeX 主文件](20261124_g_algebra_rh_ns_formal_system.tex)
- [证明链、义务与进度](g_algebra_rh_ns/README.md) · [十四项逐项审计](src/markdown/1795704572379_GAlgebra%20十四项义务的证据链审计.md)
- [TeX 与 Lean 声明索引](g_algebra_rh_ns/proof-index.md) · [公开文献登记](g_algebra_rh_ns/sources.json)
- [Lean 编译与核验报告](LEAN_BUILD_REPORT.md)

## 复核

在仓库根目录使用 Python 3 核对 TeX–Lean 映射和十四项结果。经典黎曼条目依次核对定理 7.40 的秩一限制与定理 7.12 的正向回读，定理 7.35 的窗口估计按独立 G-PDE 判据收入全稿索引。[十四项验收脚本](audit/check_obligations.py)

```powershell
python -B .\g_algebra_rh_ns\check_mapping.py
python -B .\audit\check_obligations.py
```

Lean 工程使用 `lean-toolchain` 指定的 Lean 4.36.0。构建、声明核验及公理审计命令见[专项复核步骤](g_algebra_rh_ns/README.md#复核)。

使用带 CJK 宏包的 pdfLaTeX 编译正式稿，输出到 `out/tex/`。

```powershell
.\compile_notebook_tex.ps1 -TexTargets '20261124_g_algebra_rh_ns_formal_system.tex' -OutputDir 'out/tex'
```

## 许可

版权所有 © 2026 GaoZheng（高政）。

| 材料 | 许可 |
| --- | --- |
| 原创代码（包括 Lean 形式化代码和仓库脚本）、构建和维护配置、仓库级维护文档 | [Apache License 2.0](LICENSE) |
| 正式稿的 TeX 与 PDF、TeX 分节及声明所列配套研究材料中的原创内容 | [CC BY-NC-ND 4.0 文稿许可](LICENSE-IP) |

引用内容、第三方材料及已有独立许可声明的材料遵循各自的权利和许可声明。
