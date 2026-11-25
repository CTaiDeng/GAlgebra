# GAlgebra

## 项目目的

GAlgebra 的目标是在同一 G 母体上构造数论与动力学/PDE 两族原命题的经典证明。证明链从实际输入、合法域与完整量词出发，保结构上卷到 G 母体，直接求解各分型内核，经纤维丛协变与多复合反身统一闭合，再从法空间回读原命题。统一估计覆盖整个合法复合族。Lean 工程核验已形式化并登记于证明索引的声明。[共同证明链与验收](g_algebra_rh_ns/parts/proof_guide.texinc)

## 两族证明义务

### 数论族

- **经典黎曼猜想（最初义务）**。证明黎曼 $\zeta$ 函数的每个非平凡零点 $\rho$ 都满足 $\operatorname{Re}\rho=1/2$。
- **二元哥德巴赫猜想**。证明每个偶数 $N\ge 4$ 都能写成两个素数之和。
- **孪生素数猜想**。证明对任意阈值 $X$，存在 $p>X$，使 $p$ 和 $p+2$ 均为素数。
- **Hardy–Littlewood 素数 $k$ 元组猜想**。对每个 $k\ge 1$ 和每组固定、互异、可容许且以 $0$ 为首项的整数偏移 $\mathbf h$，证明素数元组的对数加权计数满足 $R_{\mathbf h}(X)\sim\mathfrak S(\mathbf h)X$，其中 $\mathfrak S(\mathbf h)$ 为该组的奇异级数。
- **勒让德猜想**。证明对每个整数 $m\ge 1$，开区间 $(m^2,(m+1)^2)$ 内存在素数。
- **有理数域上的全秩大黎曼猜想**。对每个 $n\ge 1$ 和 $GL_n(\mathbb A_{\mathbb Q})$ 的每个单位归一化尖点自守表示 $\pi$，证明标准 $L(s,\pi)$ 的全部非平凡零点均位于临界线。每个原始 Dirichlet 特征的 $L$ 函数满足同一零点条件，是秩一子义务。经典黎曼猜想对应秩一的平凡特征。[谱目标与数论族定义](g_algebra_rh_ns/parts/targets.texinc#L182)

### 动力学/PDE 族

- **带光滑紧支外力的 Navier–Stokes 有限时间爆破（最初义务）**。对每个黏性系数 $\nu>0$，证明在 $\mathbb R^3$ 上存在从零初值出发、在 $0\le t<1$ 光滑且动能一致有界的不可压缩解。外力在 $\mathbb R^3\times(0,\infty)$ 上光滑紧支，且速度满足 $\limsup_{t\uparrow 1}\lVert u(t)\rVert_\infty=\infty$。[爆破目标与回读前提](g_algebra_rh_ns/parts/targets.texinc#L157)
- **硬球到不可压缩 Navier–Stokes–Fourier 的幂律联合极限**。在三维环面上固定相容的近 Maxwell 制备和共同光滑时间窗 $[0,T]$，证明存在独立于硬球直径 $a$ 的 $0<\beta<1$ 和 $\kappa>0$，使 $\delta=a^\beta$、$R_a=a^{-\kappa}$ 时，$\mathbb E[N]a^2\sim\delta^{-1}$，归一化密度与速度矩在 $L^\infty([0,T];L_x^1)$ 中收敛到给定宏观解的密度与速度。联合极限包含三个子义务。[联合极限定义](g_algebra_rh_ns/parts/targets.texinc#L228)

  - 硬球多体相流到 BBGKY 层级，在给定合法粒子参数与可积入射接触迹时精确读取接触通量。
  - BBGKY 层级到硬球玻尔兹曼方程，在同一制备和粒子时间窗上建立碰撞项与速度矩的极限。
  - 硬球玻尔兹曼方程到不可压缩 Navier–Stokes–Fourier 方程，在共同光滑时间窗上回读应力、热通量和运输系数。

- **三维环面硬球玻尔兹曼大数据经典适定性**。对任意幅度的光滑、非负、在速度方向快速衰减且质量与能量有限的初值，证明空间非齐次硬球玻尔兹曼方程有唯一的全局非负经典解。
- **三维周期无外力 Navier–Stokes 全局光滑性**。对每个 $\nu>0$ 和每个光滑周期无散度初速度，证明无外力不可压缩 Navier–Stokes 方程有全局光滑周期速度与配套压力。[两项全局义务的原量词](g_algebra_rh_ns/parts/targets.texinc#L246)

### 当前验收

现有进度表登记两族的 14 项义务及子义务，已验收 7 项双向等价、6 项充分回读和 1 项精确读数。经典黎曼猜想已有与实际 $\xi$ 所生成全称矩条件的等价定理，带外力爆破已有以合法非零精确周期存在性为前提的充分回读。原命题在相应母体命题覆盖原量词并经已证回读得到结论时结项。[逐项覆盖范围与进度](g_algebra_rh_ns/README.md#整体证明义务完成进度表)

## 阅读入口

- [正式稿 PDF](20261124_g_algebra_rh_ns_formal_system.pdf) · [TeX 主文件](20261124_g_algebra_rh_ns_formal_system.tex)
- [证明链、义务与进度](g_algebra_rh_ns/README.md)
- [TeX 与 Lean 声明索引](g_algebra_rh_ns/proof-index.md) · [公开文献登记](g_algebra_rh_ns/sources.json)

## 复核

在仓库根目录使用 Python 3 检查文献定位、TeX 标签和 Lean 声明的映射。

```powershell
python -B .\g_algebra_rh_ns\check_mapping.py
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
