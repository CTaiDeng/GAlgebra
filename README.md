# GAlgebra

> Gao, Z. (2026). G 代数在数论与动力学/PDE 中的统一证明框架:分型求解、法空间回读与 Lean 形式化(A Unified G-Algebra Proof Framework for Number Theory and Dynamics/PDEs: Type-Specific Solution Methods, Law-Space Readback, and Lean Formalization) (Version v3.1). Zenodo. <https://doi.org/10.5281/zenodo.24597097>

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24597097.svg)](https://doi.org/10.5281/zenodo.24597097)

### 作者：GaoZheng（高政）

[作者博客](https://mymetamathematics.blogspot.com) · [![ORCID](https://orcid.org/sites/default/files/images/orcid_16x16.png) 0009-0008-3013-6626](https://orcid.org/0009-0008-3013-6626)

## 项目目的

GAlgebra 的目标是在同一 G 母体上构造数论与动力学/PDE 两族原命题的经典证明。**仓库规定的法空间证明义务在内蕴证明下符合经典原命题的无条件证明义务，不构成原命题的附加条件。** 这里的“无条件”指最终证明只依赖原命题认可的数学基础和原始假设。

在周期流体中，整数加法关系筛出可能交换能量的速度模态，实际速度系数给出通量的大小与方向。在有理数域上，从黎曼 $\zeta$ 函数到任意秩的标准自守 $L$ 函数，只要核验了相应的解析输入，就能用同一种算术矩判据表述各自的零点问题。[数论与动力学的联合应用](#数论与动力学的证书化混沌控制工具箱) · [全秩谱型与经典回读](#全秩谱型与经典黎曼猜想)

## 跨域证明的判定与求解

跨域证明须满足**陈述完整、推导合法、每步可核验**三项要求。原题给出实际输入、合法域和完整量词。G 母体用带分型标签的分离和承载各类状态，在法对象中一并登记作用、相容条件、可容许域、观察和证书。一份带证据的法对象还可作为另一法对象的证书。《跨集合论的逻辑域》用广义集合的自指与余归纳解释这种嵌套。具体定理的依据是各自的方程、估计和回读证明。[带任务的法对象](g_algebra_rh_ns/parts/law.texinc#L5)

1. **保结构上卷。** 投影域尚未构造出见证时，沿任务商把原题的对象、参数和初值送入 G 母体，保留原定义域、量词次序及允许的作用。
2. **核验商坐标。** 两个状态属于同一商类，当且仅当它们在全部约定的未来测试中给出相同读数。所得任务商保持观察与后继，是所有满射精确表示的最粗共同像。[共同最粗任务商](g_algebra_rh_ns/parts/law.texinc#L73)
3. **分型下卷求解。** 谱型求实际矩泛函的全称正性见证，加性数论按整数关系读取素数权重，流体求整周期方程的解，动理学读取边缘分布、接触通量与速度矩。解连同实际参数、所证方程或不等式及其适用域，构成该项母体命题的证书。[四类分型内核](g_algebra_rh_ns/parts/g_pde_chain.texinc#L4)
4. **协变运输与反身统一闭合。** 纤维丛协变沿相容的纤维运输测试和证书，多复合反身使合法末态可用于下一次作用。统一估计须覆盖整个合法复合族。例如，在 Banach 空间中，若初始项 $h$ 和有序双线性算子 $\mathcal B$ 满足共同界 $\lVert h\rVert\le s$、$\lVert\mathcal B\rVert\le M$ 且 $4Ms<1$，则全部有序满二叉树的复合之和给出方程 $w=h+\mathcal B(w,w)$ 的解。[有序二叉复合的统一估计](g_algebra_rh_ns/parts/flow_periodic.texinc#L6)
5. **跨域回读。** 将见证连同分型标签和覆盖域带回共同法状态。同一商坐标与随附证据须确定同一目标读数，保证回读与合法代表的选择无关。已证正向回读把这份见证用于原题。[联合纤维上的回读](g_algebra_rh_ns/parts/g_pde_chain.texinc#L32) · [共同证明链](g_algebra_rh_ns/parts/proof_guide.texinc#L15)

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

**十四项义务对应的法空间结果均已按各自的定理陈述证毕**，包括 **7 项双向等价、6 项充分回读和 1 项精确读数**。进度表按“已证结果类型”结项。双向等价须证成两个方向，充分回读须从所列母体前提推出原结论，精确读数须在指定域内证明相应等式。每一项均可查到原量词、实际取得的证据及其覆盖域。[十四项逐项进度表](g_algebra_rh_ns/README.md#整体证明义务完成进度表)

记 $\Gamma_0$ 为经典原命题 $P_\sigma$ 认可的数学基础与原始假设。在 $\Gamma_0$ 内取得覆盖原量词的母体见证 $\pi_\sigma:M_\sigma$，并证得保留同一实际输入、定义域和完整量词的正向回读 $D_\sigma$ 时，蕴含消去给出

$$
\frac{\Gamma_0\vdash\pi_\sigma:M_\sigma
      \qquad \Gamma_0\vdash D_\sigma:(M_\sigma\Rightarrow P_\sigma)}
     {\Gamma_0\vdash D_\sigma(\pi_\sigma):P_\sigma}.
$$

这里 $M_\sigma$ 是经典证明中的已证引理。把 $\pi_\sigma$ 代入回读的前件，整份推导就只依赖 $\Gamma_0$。原命题在 $D_\sigma(\pi_\sigma)$ 处证毕，验收止于同一次回读。原题要求存在性时，即按所得存在性结论验收。原题明确要求显式构造时，构造随同一回读交付。Lean 定理 `GAlgebra.discharge_open_hypotheses` 形式化了用同一底理论中的证明替换开放前提的规则。[验收标准](g_algebra_rh_ns/README.md#验收标准) · [前提替换的 Lean 声明](g_algebra_rh_ns/lean/GAlgebra/Proof.lean#L40)

### 分型见证及其覆盖域

| 原命题或子义务（节选） | 母体前提或读数条件 | 已证回读与实际范围 |
| --- | --- | --- |
| 二元哥德巴赫猜想 | 对每个偶数 $N\ge4$，取和为 $N$ 的素数对的非负加权和 $G_2(N)$。 | $G_2(N)>0$ 与该 $N$ 有素数分拆等价。例如 $G_2(4)=(\log 2)^2>0$ 读出 $4=2+2$。全体偶数对应的母体命题要求上述正性对每个偶数 $N\ge4$ 成立。[和频正性与计数回读](g_algebra_rh_ns/parts/prime_poisson.texinc#L55) |
| 带光滑紧支外力的 Navier–Stokes 爆破 | 单位黏性下的完整周期方程存在合法非零解。 | 由同一周期解及黏性伸缩，对每个 $\nu>0$ 回读零初值、有界动能和光滑紧支外力下的有限时间爆破存在性。这条蕴含按充分回读结项。[周期回读定理](g_algebra_rh_ns/parts/flow_periodic.texinc#L4950) |
| 硬球多体相流到 BBGKY | 固定合法粒子参数，采用同一对称制备，入射接触迹可积。 | 固定粒子数 $N$ 时，第 $k$ 阶接触通量的系数为 $(N-k)a^2$。采用巨正则活动度归一化时，对应系数为 $\lambda a^2=\delta^{-1}$。两式均为适用域内的精确读数。[固定参数的接触通量](g_algebra_rh_ns/parts/kinetic_limit.texinc#L213) |
| 硬球到不可压缩 Navier–Stokes–Fourier 的幂律联合极限 | 同一制备满足中心化尾界。在粒子窗 $0\le s\le T/\delta$ 上，从一粒子边缘到玻尔兹曼解、再到宏观提升的两层未加权 $L^\infty_s L^1_{x,v}$ 误差之和为 $o(\delta)$。 | 该误差条件足以回读归一化密度与速度矩的收敛。在全局 Maxwell 平衡制备上，沿用题设的活动度归一，对任意固定 $T,\kappa>0$，原联合极限恰在 $0<\beta<1/2$ 成立。[联合误差估计](g_algebra_rh_ns/parts/kinetic_limit.texinc#L366) · [平衡子域的证明](g_algebra_rh_ns/parts/kinetic_limit.texinc#L438) |

## 数论与动力学的证书化混沌控制工具箱

数论族给出整数频率关系、谱矩和离散方向分布，动力学族给出速度、碰撞和合法控制场。按应用文章的分法，一阶控制针对状态和轨迹，二阶控制选择算子和参数，三阶控制考察现有控制能力的障碍与合法扩张。每份证书都须指明所控制的量和覆盖域。

- **频带能量。** 对三维环面上的光滑无力不可压缩流，命题 10.10 用满足 $p+q=k$ 的输入对的数量、横向投影和速度模态给出跨带通量的分块上界。应用文章据此推出带外力时的衰减条件。记 $E_A$ 为有限对称频带 $A$ 的能量，$\mathcal D_A$ 为黏性耗散，$C_A(u)$ 为完整跨带通量绝对值的上界。若合法外力的带符号功率在光滑时间窗内满足 $\mathcal P_A\le\mathcal D_A-C_A(u)-\lambda E_A$，其中 $\lambda>0$，则 $E_A(t)\le E_A(0)e^{-\lambda t}$。[跨带通量估计](g_algebra_rh_ns/parts/kinetic_limit.texinc#L467) · [频带衰减推论](src/markdown/1795796342743_数论与动力学的联合应用价值：GAlgebra%20的证书化混沌控制工具箱.md#22-指定频带能量衰减的充分条件)
- **最少控制方向。** 对给定的全空间精确缩放旋转周期，引理 9.63 选出权重 $\beta\in(0,1/2)$。用光滑紧支无散度控制场扩张周期线性化算子，使其在相应的加权空间内具有有界线性右逆。所需的最少控制方向数恰为该周期加权返回算子的增长空间维数，即 $m_{\min}=\dim E_+$。[有限控制与最小性](g_algebra_rh_ns/parts/flow_periodic.texinc#L4815)
- **碰撞误差。** 在硬球速度网格上，整数球壳与模二同余确定保持动量和能量的出射对。球壳与均匀球面的角分布差异给出 Lipschitz 速度测试的单对角积分误差上界。在高斯速度权上界下，高度可除类有单独的加权预算，即只计入满足 $4^j\mid\lvert p-q\rvert^2$ 的网格指标对 $p,q$，其中 $j\ge1$。若该预算在指定时空残差范数中成立，且残差到未放大终端矩的稳定界为 $C_\delta$，则该类对宏观涨落的误差贡献由该预算乘以 $C_\delta\delta^{-3}$ 控制。[球壳角分布](g_algebra_rh_ns/parts/kinetic_limit.texinc#L518) · [高度可除类的误差预算](g_algebra_rh_ns/parts/kinetic_limit.texinc#L555)
- **可达性障碍。** 在有限维线性复形中，设已有控制的像为 $S=\operatorname{im}B$，相容性检验 $D$ 满足 $DB=0$。同调商 $\ker D/S$ 记录相容目标的障碍类。增加满足 $DR=0$ 的控制 $R$ 后，消除的独立障碍数等于 $\dim((S+\operatorname{im}R)/S)$。若两组输入分别限于合法集合 $K,L$，实际可达集为 $B(K)+R(L)$。[兼容扩张的有效方向数](g_algebra_rh_ns/parts/coverage.texinc#L79) · [受约束的可达集](g_algebra_rh_ns/parts/repair.texinc#L10)

这些读数各有检验对象。频带通量度量跨尺度能量传递，动力学混沌考察轨迹敏感性等性质，动理学的传播混沌则考察多粒子极限中固定阶边缘分布能否趋于乘积分布。将算术谱证书用于另一动力系统时，还须验证运输在共同定义域上保持目标测试，并计入复合产生的误差。[纤维算子的协变与组合缺陷](g_algebra_rh_ns/parts/g_pde_chain.texinc#L68)

## 全秩谱型与经典黎曼猜想

全秩路线先将经典 $\zeta$ 与原始 Dirichlet 纤维纳入所有 $n\ge1$ 的标准自守 $L$ 函数族，再把逐纤维的零点问题化为共同的矩测试。对已核验解析输入的每个表示 $\pi$，定理 7.38 由 $\pi$ 与对偶表示的完备函数构造平方谱 $\mu=9/4-(\rho-1/2)^2$，临界线对应实半轴 $[9/4,\infty)$。以实际算术预解式 $R_\pi$ 在原点的 Taylor 系数定义矩泛函 $\mathcal L_\pi$，定理 7.39 给出下列等价式，其中 $Z_*(\pi)$ 是去极点后完备函数的零点集。[对偶平方谱与预解式](g_algebra_rh_ns/parts/grand_riemann.texinc#L145) · [局部化矩正性判据](g_algebra_rh_ns/parts/grand_riemann.texinc#L194)

$$
\bigl[\forall\rho\in Z_*(\pi),\ \Re\rho=\tfrac12\bigr]
\quad\Longleftrightarrow\quad
\bigl[\forall p\in\mathbb R[t],\
  0\le\mathcal L_\pi(tp^2)\le\tfrac49\,\mathcal L_\pi(p^2)\bigr].
$$

矩正性成立时，同一矩泛函给出满足 $0\le T_\pi\le(4/9)I$ 的有界自伴算子。交换 $\pi$ 与其对偶保持同一组矩读数。定理 7.40 对整个秩域取全称，证明全族矩判据与全秩零点命题双向等价。覆盖全部秩、表示和实多项式的矩见证可以按指标限制到任一子族。若从 $n\ge2$ 的高秩结果出发，拼成全秩结论还须提供秩一基例。[正算子闭合](g_algebra_rh_ns/parts/spectral_moments.texinc#L76) · [全秩矩判据](g_algebra_rh_ns/parts/grand_riemann.texinc#L231) · [秩一与高秩的拼接](g_algebra_rh_ns/parts/grand_riemann.texinc#L4)

给定全秩矩见证 $\Pi$，取导子为 $1$ 的平凡特征与零虚平移对应的秩一分量 $\Pi(1,\mathbf1)$。记经典 $\zeta$ 的预解式和矩泛函为 $R,\mathcal L$。该分量自对偶，完备函数的对偶乘积为 $\xi^2$，故 $R_{\mathbf1}=2R$、$\mathcal L_{\mathbf1}=2\mathcal L$。将两条矩不等式同除以 $2$，即得覆盖全部实多项式的 $\pi_\zeta$。若 $\Pi$ 及所用解析输入均从原始数学基础 $\Gamma_0$ 内蕴证得，$D_\zeta(\pi_\zeta)$ 就在同一次回读中给出经典黎曼猜想的无条件证明。[全秩见证的秩一限制](g_algebra_rh_ns/parts/grand_riemann.texinc#L231) · [经典矩判据的正向回读](g_algebra_rh_ns/parts/spectral_moments.texinc#L155)

导子 $1$ 的主特征与其对偶在每个正整数上都取值 $1$，故 $L(s,\mathbf1)=\zeta(s)$。Lean 证明，对每个算术截断和每个测试多项式，平凡纤维的矩都等于经典矩的两倍。经典矩序列趋于 $x$ 当且仅当平凡纤维的矩序列趋于 $2x$。正文由局部一致收敛给出实际 $\xi$ 的 Taylor 系数。Lean 据此识别自对偶平方，对负对数导数取系数，再在 $tp^2$、$p^2$ 上特化同一个矩等式。[算术极限的等价](g_algebra_rh_ns/lean/GAlgebra/TrivialFiber.lean#L341) · [矩恒等式](g_algebra_rh_ns/lean/GAlgebra/TrivialFiber.lean#L418) · [秩一回读](g_algebra_rh_ns/lean/GAlgebra/TrivialFiber.lean#L429)

证明的复用价值也可以按任务核算。按专题文章的成本模型，若共同母体的一次构造与求解耗费 $C$，每项任务相对独立证明在扣除上卷、回读费用后平均节省 $b>0$，则 $N$ 项任务在 $Nb>C$ 时产生净节省。[证明复用的成本模型](src/markdown/1795796903721_从广义黎曼猜想到经典黎曼猜想：GAlgebra%20的高阶统一价值.md#42-两种证明组织方式的成本)

## 阅读入口

- [正式稿 PDF](20261124_g_algebra_rh_ns_formal_system.pdf) · [TeX 主文件](20261124_g_algebra_rh_ns_formal_system.tex)
- [跨域证明的完备性判定：求解在G母体与回读处的证毕](src/markdown/1795691852770_跨域证明的完备性判定：求解在G母体与回读处的证毕.md)
- [跨集合论的逻辑域：GAlgebra的证明世界观与方法论](src/markdown/1795693012000_跨集合论的逻辑域：GAlgebra的证明世界观与方法论.md)
- [GAlgebra 十四项义务的证据链审计](src/markdown/1795704572379_GAlgebra%20十四项义务的证据链审计.md)
- [法空间内蕴证明与经典原命题的无条件证明](src/markdown/1795785591720_法空间内蕴证明与经典原命题的无条件证明.md)
- [数论与动力学的联合应用价值：GAlgebra 的证书化混沌控制工具箱](src/markdown/1795796342743_数论与动力学的联合应用价值：GAlgebra%20的证书化混沌控制工具箱.md)
- [从广义黎曼猜想到经典黎曼猜想：GAlgebra 的高阶统一价值](src/markdown/1795796903721_从广义黎曼猜想到经典黎曼猜想：GAlgebra%20的高阶统一价值.md)
- [证明链、义务与进度](g_algebra_rh_ns/README.md)
- [TeX 与 Lean 声明索引](g_algebra_rh_ns/proof-index.md) · [公开文献登记](g_algebra_rh_ns/sources.json)
- [Lean 编译与核验报告](LEAN_BUILD_REPORT.md)

## 复核

在仓库根目录使用 Python 3 核对 TeX–Lean 映射和十四项结果。经典黎曼条目依次核对定理 7.40 的秩一限制与定理 7.12 的正向回读，定理 7.35 的窗口估计按独立 G-PDE 判据收入全稿索引。[十四项验收脚本](audit/check_obligations.py)

```powershell
python -B .\g_algebra_rh_ns\check_mapping.py
python -B .\audit\check_obligations.py
```

Lean 工程固定为 4.36.0，直接导入的官方基础模块只有 `Init`，Lake 外部包数为 0。2026-11-28 的独立核验覆盖 51 项输入、170 条 TeX–Lean 映射和 434 个不同声明。秩一系数、级数除法和多项式配对均在同一主库内构建。正文给出算术系数的解析收敛论证，完整回读仍以全秩矩见证及经典正向回读为前提。[构建与公理审计](LEAN_BUILD_REPORT.md#证明覆盖范围) · [正式稿定理 7.40](g_algebra_rh_ns/parts/grand_riemann.texinc#L231) · [复核步骤](g_algebra_rh_ns/README.md#复核)

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
