# G 代数的直接上卷、分型内核与法空间回读

正文见 [正式稿](../20261124_g_algebra_rh_ns_formal_system.pdf)。
[证明指引](parts/proof_guide.texinc) 给出各内核的原量词、母体前提与回读。
[证明索引](proof-index.md) 对照正文使用处、对应公开文献或附录位置，以及 Lean 声明与实际核验范围。
[六项公开文献](sources.json) 按指定版本登记作者、年份、题名和 DOI。[附录基础](parts/internal_basis.texinc) 给出有限路径、支持因子化和各题的解析输入。

## 证明链

**固定原命题、实际输入和完整量词 → 保结构上卷到 G 母体 → 分型内核直接求解 → 纤维丛协变与多复合反身统一闭合 → 法空间回读经典推导。**

各分型的母体命题、回读定理与适用域见下表。[法空间证明链与分型回读](parts/proof_guide.texinc)

## 验收标准

**已证的法空间定理按其证明范围结项。** 双向等价要求两个方向均已证明。充分回读在所列前提下推出原结论。精确读数给出适用域内的等式。

**原命题的验收采用国际通行的蕴含消去规则（modus ponens）。** 设 \(\pi_\sigma:M_\sigma\) 是法空间证明，\(D_\sigma:M_\sigma\Rightarrow P_\sigma\) 是保留原假设、定义域和完整量词的已证正向回读。将回读应用于法空间证明，得到

$$
\boxed{\frac{\pi_\sigma:M_\sigma\qquad D_\sigma:M_\sigma\Rightarrow P_\sigma}
{D_\sigma(\pi_\sigma):P_\sigma}}.
$$

所得推导 \(D_\sigma(\pi_\sigma)\) 即为原命题的证明，验收止于同一回读。原命题要求存在性时，以回读所得的存在性结论验收。原命题要求显式构造时，构造随同一推导交付。[共同回读与证明指引](parts/proof_guide.texinc#L32) · [Lean 官方文档《命题与证明》](https://lean-lang.org/theorem_proving_in_lean4/Propositions-and-Proofs/)

## 整体证明义务完成进度表

核对日期 **2026-11-25**。本表对应 **150 页正式稿、157 条 TeX–Lean 映射**。**14 项法空间结果均已结项**，其中 2 项为最初义务，12 项为追加义务或子义务。已证结果包括 **7 项双向等价、6 项充分回读、1 项精确读数**。原命题与量词见 [义务定义](parts/targets.texinc#L140)。

| 归属 | 原命题与量词 | G 母体的命题与已证内容 | 已证回读及覆盖范围 | 结项状态 |
| --- | --- | --- | --- | --- |
| 最初 | **经典黎曼猜想** \(\mathsf B_{\mathbf 1}\)。实际 \(\zeta\) 的每个非平凡零点 \(\rho\) 均满足 \(\Re\rho=\tfrac12\)。 | 实际 \(\xi\) 的 Euler 与 Gamma 数据确定同一 \(R,\mathcal L\)。法空间命题为 \(\mathsf E_\zeta:\ \forall p\in\mathbb R[t],\ 0\le\mathcal L(tp^2)\le(4/9)\mathcal L(p^2)\)。[算术输入与算子闭合](parts/spectral_moments.texinc)（`thm:xi-moment-generator`、`thm:spectral-positive-operator`） | \(\mathsf E_\zeta\Longleftrightarrow\mathsf B_{\mathbf 1}\)，保留全部非平凡零点的量词。[回读定理](parts/spectral_moments.texinc)（`thm:xi-moment-readback`） | **已结项（双向等价）** |
| 最初 | **带光滑紧支外力的 Navier–Stokes 有限时间爆破**。每个 \(\nu>0\)，全空间上零初值、\(0\le t<1\) 光滑、动能有界且 \(\limsup_{t\uparrow1}\lVert u(t)\rVert_\infty=\infty\)，外力在 \(\mathbb R^3\times(0,\infty)\) 光滑紧支。 | 整周期有序复合统一闭合尾部并保存接缝和远场迹。法空间命题 \(\mathsf E_{\rm per}\) 表示单位黏性下存在合法的 \((a,R,v)\) 且 \(F_{a,R}(v)=0,\ v\not\equiv0\)。[整周期闭合](parts/flow_periodic.texinc)（`thm:flow-period-composite`） | \(\mathsf E_{\rm per}\Longrightarrow\mathsf P_{\rm NS}\)。控制右逆及紧支脉冲给出回读，黏性伸缩覆盖每个 \(\nu>0\)。[周期回读](parts/flow_periodic.texinc)（`lem:flow-period-controlled-inverse`、`thm:flow-period-pulse-readback`） | **已结项（充分回读）** |
| 追加 | **二元哥德巴赫猜想**。每个偶数 \(N\ge4\) 为两个素数之和。 | 去阻尼后的和频 \(G_2(N)\) 精确读取加权素数对。[整数关系投影](parts/prime_poisson.texinc)（`thm:prime-poisson-fiber`） | 各 \(N\) 的 \(G_2(N)>0\) 与该 \(N\) 有素数分拆等价。[计数回读](parts/prime_poisson.texinc)（`prop:prime-additive-readback`） | **已结项（双向等价）** |
| 追加 | **孪生素数猜想**。对每个阈值 \(X\) 存在 \(p>X\)，且 \(p,p+2\) 均为素数。 | 差频 \(2\) 的 Abel 迹为 \(T_{(0,2)}(t)\)，项权非负。[差分投影](parts/prime_poisson.texinc)（`thm:prime-poisson-fiber`） | \(T_{(0,2)}(t)\to\infty\)（\(t\downarrow0\)）与素数对首项无界等价。[计数回读](parts/prime_poisson.texinc)（`prop:prime-additive-readback`） | **已结项（双向等价）** |
| 追加 | **Hardy–Littlewood 素数 \(k\) 元组猜想**。每个 \(k\ge1\) 及每个固定、互异、可容许且以 \(0\) 为首项的偏移组。 | 联合纤维精确读取 \(R_{\mathbf h}(X)\)，可容许组的奇异级数 \(\mathfrak S(\mathbf h)\) 为正。[联合投影与权重](parts/prime_poisson.texinc)（`thm:prime-poisson-fiber`、`prop:prime-additive-readback`） | 每组的 \(R_{\mathbf h}(X)\sim\mathfrak S(\mathbf h)X\) 与普通计数 \(\pi_{\mathbf h}(X)\sim\mathfrak S(\mathbf h)X/(\log X)^k\) 等价。[加权渐近回读](parts/prime_poisson.texinc)（`prop:prime-additive-readback`） | **已结项（双向等价）** |
| 追加 | **勒让德猜想**。每个整数 \(m\ge1\) 的 \((m^2,(m+1)^2)\) 含有素数。 | 同一素数场的去阻尼系数在平方区间内求和，得到 \(I(m)\)。[区间读数](parts/prime_poisson.texinc)（`prop:prime-additive-readback`） | 各 \(I(m)>0\) 与对应开区间含有素数等价。[区间回读](parts/prime_poisson.texinc)（`prop:prime-additive-readback`） | **已结项（双向等价）** |
| 全秩子义务 | **原始 Dirichlet 特征的广义黎曼猜想**。每个实际原始特征的全部非平凡零点。 | Fourier–Mellin、对偶平方谱与虚平移给出秩一输入。[秩一构造](parts/grand_riemann.texinc)（`thm:dirichlet-analytic-input`、`lem:grh-rank-one-base`） | 逐纤维全称局部化矩正性与该特征的临界线命题等价。[自守矩回读](parts/grand_riemann.texinc)（`thm:grh-localized-moments`） | **已结项（双向等价）** |
| 追加 | **有理数域上的全秩大黎曼猜想**。每个 \(n\ge1\) 和每个单位归一化尖点自守 \(\pi\) 的标准 \(L(s,\pi)\) 的全部非平凡零点。 | 在所列解析输入下，对偶平方谱保留原零点和中心重数，算子闭合逐秩成立。[平方谱与全秩合成](parts/grand_riemann.texinc)（`thm:grh-square-spectrum`、`thm:grh-family-readback`） | 给定各纤维的解析输入后，全族局部化矩条件与全秩零点命题等价。[矩回读](parts/grand_riemann.texinc)（`thm:grh-localized-moments`、`thm:grh-family-readback`） | **已结项（双向等价）** |
| 联合极限子义务 | **硬球多体相流 → BBGKY**。固定合法粒子参数和可积入射接触迹，取 \(j\le k\le N\)。 | 边缘化由实积分复合，入射面保持弹性碰撞的不变量。[接触通量推导](parts/kinetic_limit.texinc#L213)（`prop:kinetic-contact-flux`） | 保留所列接触迹条件，固定 \(N\) 与活动度归一分别读取系数 \((N-k)a^2\) 与 \(\lambda a^2\)。[通量回读](parts/kinetic_limit.texinc#L213) | **已结项（精确读数）** |
| 联合极限子义务 | **BBGKY → 硬球玻尔兹曼**。同一制备和粒子时间窗 \(s\le T/\delta\) 上的碰撞与速度矩。 | 固定 \(\delta\)，在初值、输运测试和入射接触配对按所列弱式收敛时，接触配对极限为同地乘积。[接触配对](parts/kinetic_limit.texinc#L251)（`prop:kinetic-contact-flux`） | 给定收敛读取 \(Q(f,f)\) 的弱式。中心化尾界下，给定共同窗的 \(D_{\rm BG}=o(\delta)\) 可参与归一化矩的联合读回。[误差合成](parts/kinetic_limit.texinc#L366)（`thm:kinetic-joint-budget`） | **已结项（充分回读）** |
| 联合极限子义务 | **玻尔兹曼 → 不可压缩 Navier–Stokes–Fourier**。近 Maxwell 制备的共同光滑窗。 | 宏观展开与碰撞逆条件给出应力、热通量和相应运输系数。[动理学矩闭合](parts/kinetic_limit.texinc#L308)（`prop:kinetic-nsf-moment-closure`） | 在同一窗口调用所列展开和碰撞逆。中心化尾界下，给定 \(D_{\rm kin}=o(\delta)\) 可参与联合读回。[矩与误差回读](parts/kinetic_limit.texinc#L366)（`thm:kinetic-joint-budget`） | **已结项（充分回读）** |
| 追加 | **硬球 → 不可压缩 Navier–Stokes–Fourier 幂律联合极限**。固定近 Maxwell 制备与共同光滑窗，要求存在与 \(a\) 无关的 \(0<\beta<1,\kappa>0\)，使 \(\delta=a^\beta,\ R_a=a^{-\kappa},\ \mathbb E[N]a^2\sim\delta^{-1}\)，同时归一化矩在 \(L^\infty([0,T];L_x^1)\) 收敛。 | 活动度制备、总比较复形和同一相流的一粒子中心化尾界。给定同窗 \(D_{\rm BG}+D_{\rm kin}=o(\delta)\)，并取正文的指数及截断范围。[跨层估计](parts/kinetic_limit.texinc)（`prop:kinetic-prepared-activity`、`prop:kinetic-centered-tail`、`thm:kinetic-joint-budget`） | 给定共同误差条件回读密度与速度。全局 Maxwell 平衡纤维在 \(0<\beta<1/2\) 及任意固定 \(T,\kappa>0\) 已回读证毕。[误差门禁与平衡子情形](parts/kinetic_limit.texinc#L366)（`thm:kinetic-joint-budget`、`prop:kinetic-equilibrium-joint`） | **已结项（充分回读）** |
| 追加 | **三维环面硬球玻尔兹曼大数据经典适定性**。每个光滑非负、速度快速衰减且质量、能量有限的初值。 | 给定同一解类的局部经典解、合法重启、局部唯一性、重启寿命下界与有限端点的范数有界性，联合得到可延拓的最大解。[条件延拓](parts/kinetic_limit.texinc#L596) | 保留所列局部与有限端点前提，得到原解类的全局存在、非负性及唯一性。[条件延拓回读](parts/kinetic_limit.texinc#L596) | **已结项（充分回读）** |
| 追加 | **三维周期无外力 Navier–Stokes 全局光滑性**。任意 \(\nu>0\) 及光滑周期无散度初值。 | 在原初值解类内调用兼容的局部经典解、重启和有限端点范数上界。通量读取保存带符号的相互作用。[通量与条件延拓](parts/kinetic_limit.texinc#L467)（`prop:lattice-ns-flux`） | 在所列局部与有限端点前提下回读全局光滑速度与空间均值零的压力。[条件延拓回读](parts/kinetic_limit.texinc#L596) | **已结项（充分回读）** |

跟踪以本表义务名称和 TeX 标签为准。只在母体证明、回读方向或覆盖量词有变化时更新对应行和依赖行，并同步 [证明索引](proof-index.md)、日期和版次。

## 已证的补充核验

- **有限算术。** 独立轮廓计数和临界线符号证书核验 \(0<\Im\rho\le1270\) 的 \(871\) 个零点均为临界线单零点。[有限零点证书](parts/zeta_window.texinc)
- **分型引理。** 已证的算术局部估计、周期协变界与动力学误差界，按各自的假设和 TeX 标签核对。[证明索引](proof-index.md)

## 复核

工具链固定为官方 Lean 4.36.0，直接官方基础模块为 \(\texttt{Init}\)，Lake 外部包依赖表为空。
算术矩和整周期的 Lean 声明及其核验范围按定理逐项登记。[TeX–Lean 映射](proof-index.md)
离散主丛的自由传递作用、边运输、有序复合和同端点运输等价已给出完整 Lean 推导。总算子的组合缺陷、分量差商和对偶测试共用同一运输。
附录的有限路径映射给出终点测度、所有加法测试的配对、门禁保持、商上二次推前和代价最小性的完整 Lean 推导。
实复分析、Hilbert 完备与连续 PDE 的证明见正式稿。配套索引逐条区分完整构造与仅核验的引理。

在本页目录运行 `python -B check_mapping.py`。
脚本检查六项公开引文的版本、顺序和正文定位，以及 TeX 主文引用、Lean 的传递导入和逐条映射。复核所需的 TeX、Lean 和索引由本目录及正式稿源码提供。
将 `lean/` 源码复制到工作区 `out/` 下的干净目录。主线复核运行以下命令。

```powershell
lake build
lake env leanchecker GAlgebra
lake env leanchecker Audit
lake env lean Audit.lean
```
统一审计入口核对实际映射的声明和公理。算术主线及附录的有限零点核验由同一构建复核，算术主线的 Lean 导入闭包独立保持。
