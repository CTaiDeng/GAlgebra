# G 代数的直接上卷、分型内核与法空间回读

正文见 [正式稿](../20261124_g_algebra_rh_ns_formal_system.pdf)。
[证明指引](parts/proof_guide.texinc) 给出各内核的原量词、母体前提与回读。
[证明索引](proof-index.md) 对照正文使用处、对应公开文献或附录位置，以及 Lean 声明与实际核验范围。
[六项公开文献](sources.json) 按指定版本登记作者、年份、题名和 DOI。[附录基础](parts/internal_basis.texinc) 给出有限路径、支持因子化和各题的解析输入。

## 证明链

**固定原命题、实际输入和完整量词 → 沿任务商保结构上卷到 G 母体 → 分型下卷求取母体见证 → 纤维丛协变与多复合反身统一闭合 → 将见证回读到投影域。**

在投影域尚未构造出见证时，任务商保留合法运算和终端读数，证据与商坐标一并携带。同一商坐标和证据下的目标读数一致时，回读在合法代表上良定义。[法空间证明链](parts/proof_guide.texinc) · [任务商与回读良定义](parts/g_pde_chain.texinc#L32)

## 验收标准

**进度表以“已证结果类型”一栏登记结项。** 双向等价以两个方向均已证明结项。充分回读以所列母体前提 \(M_\sigma\) 下推出 \(P_\sigma\) 的证明结项。精确读数按适用域内的等式结项。

**原命题的验收采用蕴含消去规则（modus ponens）。** 设 \(\pi_\sigma:M_\sigma\) 是覆盖原量词的母体证明，\(D_\sigma:M_\sigma\Rightarrow P_\sigma\) 是保留原假设、定义域和完整量词的已证正向回读。将回读应用于母体证明，得到

$$
\boxed{\frac{\pi_\sigma:M_\sigma\qquad D_\sigma:M_\sigma\Rightarrow P_\sigma}
{D_\sigma(\pi_\sigma):P_\sigma}}.
$$

所得推导 \(D_\sigma(\pi_\sigma)\) 即为原命题的证明，验收止于同一回读。原命题要求存在性时，以回读所得的存在性结论验收。原命题要求显式构造时，构造随同一推导交付。[共同回读与证明指引](parts/proof_guide.texinc#L32) · [Lean 官方文档《命题与证明》](https://lean-lang.org/theorem_proving_in_lean4/Propositions-and-Proofs/)

## 整体证明义务完成进度表

核对日期 **2026-11-27**。本表对应 **173 页正式稿**和 **170 条 TeX–Lean 映射**。按原义务登记的 **14 项法空间结果均已得证**，包括 **7 项双向等价、6 项充分回读和 1 项精确读数**，对应 2 项最初义务及 12 项追加义务或子义务。[义务定义](parts/targets.texinc#L140)

表中列明回读的母体前件、实际已证的母体内容及其覆盖域。覆盖原量词的母体证明与已证正向回读合成时，原命题在回读处证毕。固定参数的接触通量和 Maxwell 平衡子域的联合极限均按已证的适用域登记。

| 归属 | 原命题与量词 | 回读所用母体命题或读数条件 | 已证母体内容及覆盖域 | 已证回读或精确读数 | 已证结果类型 |
| --- | --- | --- | --- | --- | --- |
| 最初 | **经典黎曼猜想** \(\mathsf B_{\mathbf 1}\)。全秩大黎曼猜想在 \(\mathbb Q\) 上的秩一平凡特例，要求实际 \(\zeta\) 的每个非平凡零点 \(\rho\) 均满足 \(\Re\rho=\tfrac12\)。 | \(\mathsf E_\zeta\) 要求每个 \(p\in\mathbb R[t]\) 满足 \(0\le\mathcal L(tp^2)\le(4/9)\mathcal L(p^2)\)。给定全秩矩见证 \(\Pi\)，取平凡特征与零虚平移，将 \(\Pi(1,\mathbf1)\) 的两条不等式同除以 \(2\)，即得 \(\pi_\zeta:\mathsf E_\zeta\)。[母体命题](parts/targets.texinc#L146) · [全秩见证的限制](parts/grand_riemann.texinc#L231) | 在该分量，\(L(s,\mathbf1)=\zeta(s)\)，自对偶乘积为 \(\xi^2\)，故 \(\mathcal L_{\mathbf1}=2\mathcal L\)。定理 7.40 的限制与归一化对全部实多项式成立。[秩一特例](parts/grand_riemann.texinc#L231) | \(\mathsf E_\zeta\Longleftrightarrow\mathsf B_{\mathbf 1}\)。正向回读 \(D_\zeta(\pi_\zeta):\mathsf B_{\mathbf 1}\) 证毕经典命题。[回读定理](parts/spectral_moments.texinc#L155) | **双向等价已证** |
| 最初 | **带光滑紧支外力的 Navier–Stokes 有限时间爆破**。每个 \(\nu>0\)，全空间上零初值、\(0\le t<1\) 光滑、动能有界且 \(\limsup_{t\uparrow1}\lVert u(t)\rVert_\infty=\infty\)，外力在 \(\mathbb R^3\times(0,\infty)\) 光滑紧支。 | \(\mathsf E_{\rm per}\)。单位黏性下存在合法的 \((a,R,v)\)，满足 \(F_{a,R}(v)=0\) 及 \(v\not\equiv0\)。[母体存在性](parts/targets.texinc#L168) | 整周期有序复合在所列条件下给出尾方程闭合，并保留接缝、远场迹及已核验的有限读数。[整周期闭合](parts/flow_periodic.texinc#L216) · [有限读数](parts/flow_periodic.texinc#L4619) | \(\mathsf E_{\rm per}\Longrightarrow\mathsf P_{\rm NS}\)。控制右逆及紧支脉冲给出回读，黏性伸缩覆盖每个 \(\nu>0\)。[周期回读](parts/flow_periodic.texinc)（`lem:flow-period-controlled-inverse`、`thm:flow-period-pulse-readback`） | **充分回读已证** |
| 追加 | **二元哥德巴赫猜想**。每个偶数 \(N\ge4\) 为两个素数之和。 | 对每个偶数 \(N\ge4\)，\(G_2(N)>0\)。[和频条件](parts/prime_poisson.texinc#L66) | 去阻尼后的和频 \(G_2(N)\) 精确读取加权素数对。[整数关系投影](parts/prime_poisson.texinc#L4) | 各 \(N\) 的 \(G_2(N)>0\) 与该 \(N\) 有素数分拆等价。[计数回读](parts/prime_poisson.texinc)（`prop:prime-additive-readback`） | **双向等价已证** |
| 追加 | **孪生素数猜想**。对每个阈值 \(X\) 存在 \(p>X\)，且 \(p,p+2\) 均为素数。 | \(T_{(0,2)}(t)\to\infty\)（\(t\downarrow0\)）。[差频条件](parts/prime_poisson.texinc#L67) | 差频 \(2\) 的 Abel 迹给出孪生素数对的非负加权和。[差分投影](parts/prime_poisson.texinc#L55) | \(T_{(0,2)}(t)\to\infty\)（\(t\downarrow0\)）与素数对首项无界等价。[计数回读](parts/prime_poisson.texinc)（`prop:prime-additive-readback`） | **双向等价已证** |
| 追加 | **Hardy–Littlewood 素数 \(k\) 元组猜想**。每个 \(k\ge1\) 及每个固定、互异、可容许且以 \(0\) 为首项的偏移组。 | 每个可容许偏移组的加权计数 \(R_{\mathbf h}(X)\sim\mathfrak S(\mathbf h)X\)。[渐近条件](parts/prime_poisson.texinc#L73) | 关系投影精确给出 \(R_{\mathbf h}(X)\)，可容许组的奇异级数 \(\mathfrak S(\mathbf h)\) 为正。[加权计数](parts/prime_poisson.texinc#L55) | 每组的 \(R_{\mathbf h}(X)\sim\mathfrak S(\mathbf h)X\) 与普通计数 \(\pi_{\mathbf h}(X)\sim\mathfrak S(\mathbf h)X/(\log X)^k\) 等价。[加权渐近回读](parts/prime_poisson.texinc)（`prop:prime-additive-readback`） | **双向等价已证** |
| 追加 | **勒让德猜想**。每个整数 \(m\ge1\) 的 \((m^2,(m+1)^2)\) 含有素数。 | 对每个 \(m\ge1\)，\(I(m)>0\)。[区间条件](parts/prime_poisson.texinc#L80) | 同一素数场的去阻尼系数在平方区间求和，精确给出 \(I(m)\)。[区间读数](parts/prime_poisson.texinc#L55) | 各 \(I(m)>0\) 与对应开区间含有素数等价。[区间回读](parts/prime_poisson.texinc)（`prop:prime-additive-readback`） | **双向等价已证** |
| 全秩子义务 | **原始 Dirichlet 特征的广义黎曼猜想**。每个实际原始特征的全部非平凡零点。 | 每个实际原始 Dirichlet 纤维满足全称局部化矩条件 \(\mathsf E_\pi\)。[矩条件](parts/grand_riemann.texinc#L194) | Fourier–Mellin、对偶平方谱与虚平移给出秩一解析输入。[秩一输入构造](parts/grand_riemann.texinc#L45) | 逐纤维全称局部化矩正性与该特征的临界线命题等价。[自守矩回读](parts/grand_riemann.texinc)（`thm:grh-localized-moments`） | **双向等价已证** |
| 追加 | **有理数域上的全秩大黎曼猜想**。每个 \(n\ge1\) 和每个单位归一化尖点自守 \(\pi\) 的标准 \(L(s,\pi)\) 的全部非平凡零点。 | 在给定解析输入的秩域内，每个 \(\pi\) 满足全称局部化矩条件 \(\mathsf E_\pi\)。[全秩判据](parts/grand_riemann.texinc#L231) | 对偶平方谱保留原零点与中心重数。在所列解析输入及矩条件下给出算子完成。秩一平凡纤维的对偶乘积为 \(\xi^2\)，故 \(R_{\mathbf1}=2R\)、\(\mathcal L_{\mathbf1}=2\mathcal L\)。[平方谱](parts/grand_riemann.texinc#L145) · [算子完成](parts/grand_riemann.texinc#L194) | 全族矩条件与全秩零点命题等价。全秩结论限制到平凡特征和零虚平移，即得经典黎曼猜想。[矩回读与经典特例](parts/grand_riemann.texinc#L231) | **双向等价已证** |
| 联合极限子义务 | **硬球多体相流 → BBGKY**。固定合法粒子参数和可积入射接触迹，取 \(j\le k\le N\)。 | 同一对称制备下合法多体密度的边缘信息及可积入射接触迹。 | 已证边缘化的积分复合、接触面通量及弹性碰撞不变量，覆盖所列固定参数和接触迹条件。 | 保留所列接触迹条件，固定 \(N\) 与活动度归一分别读取系数 \((N-k)a^2\) 与 \(\lambda a^2\)。[通量回读](parts/kinetic_limit.texinc#L213) | **原域内精确读数已证** |
| 联合极限子义务 | **BBGKY → 硬球玻尔兹曼**。同一制备和粒子时间窗 \(s\le T/\delta\) 上的碰撞与速度矩。 | 固定 \(\delta\) 时，初值、输运测试及入射接触配对按所列弱式收敛。配对极限为同地乘积。[弱式条件](parts/kinetic_limit.texinc#L251) | 对给定可积入射接触迹已证固定参数的时间弱式及碰撞不变量。[接触通量](parts/kinetic_limit.texinc#L213) | 给定收敛读取 \(Q(f,f)\) 的弱式。中心化尾界下，给定共同窗的 \(D_{\rm BG}=o(\delta)\) 可参与归一化矩的联合读回。[误差合成](parts/kinetic_limit.texinc#L366)（`thm:kinetic-joint-budget`） | **充分回读已证** |
| 联合极限子义务 | **玻尔兹曼 → 不可压缩 Navier–Stokes–Fourier**。近 Maxwell 制备的共同光滑窗。 | 在碰撞与速度矩测试下具所列二阶展开，且线性化碰撞算子在所用域上具有单射性及两个输运源的逆证书。[矩闭合条件](parts/kinetic_limit.texinc#L308) | 在同一碰撞归一中给出碰撞二次型、守恒量及应力和热通量的配对恒等式。[闭合推导](parts/kinetic_limit.texinc#L308) | 在同一窗口调用所列展开和碰撞逆。中心化尾界下，给定 \(D_{\rm kin}=o(\delta)\) 可参与联合读回。[矩与误差回读](parts/kinetic_limit.texinc#L366)（`thm:kinetic-joint-budget`） | **充分回读已证** |
| 追加 | **硬球 → 不可压缩 Navier–Stokes–Fourier 幂律联合极限**。固定近 Maxwell 制备与共同光滑窗，要求存在与 \(a\) 无关的 \(0<\beta<1,\kappa>0\)，使 \(\delta=a^\beta,\ R_a=a^{-\kappa},\ \mathbb E[N]a^2\sim\delta^{-1}\)，同时归一化矩在 \(L^\infty([0,T];L_x^1)\) 收敛。 | 中心化尾界下的充分条件为共同时间窗上 \(D_{\rm BG}+D_{\rm kin}=o(\delta)\)，指数及截断范围见定理。[联合误差条件](parts/kinetic_limit.texinc#L366) | 已证活动度制备、总比较复形和一粒子中心化尾界。全局 Maxwell 平衡子域给出实际联合极限的证明，覆盖 \(0<\beta<1/2\) 及任意固定 \(T,\kappa>0\)。[平衡子域的证明](parts/kinetic_limit.texinc#L438) | 给定共同误差条件回读密度与速度。全局 Maxwell 平衡纤维在 \(0<\beta<1/2\) 及任意固定 \(T,\kappa>0\) 已回读证毕。[误差门禁与平衡子情形](parts/kinetic_limit.texinc#L366)（`thm:kinetic-joint-budget`、`prop:kinetic-equilibrium-joint`） | **充分回读已证。平衡子域的原命题已证** |
| 追加 | **三维环面硬球玻尔兹曼大数据经典适定性**。每个光滑非负、速度快速衰减且质量、能量有限的初值。 | 同一解类中的局部经典解、合法重启、局部唯一性、统一正重启寿命及有限端点的延拓范数界。 | 在这些条件下，重合区间的唯一性给出最大解拼接，正寿命下界及范数界给出端点延拓。 | 保留所列局部与有限端点前提，得到原解类的全局存在、非负性及唯一性。[条件延拓回读](parts/kinetic_limit.texinc#L596) | **充分回读已证** |
| 追加 | **三维周期无外力 Navier–Stokes 全局光滑性**。任意 \(\nu>0\) 及光滑周期无散度初值。 | 同一初值解类中的局部经典解、合法重启、局部唯一性及有限端点的延拓范数界，重启寿命有统一正下界。 | 已证通量读数保持带符号的相互作用。在所列延拓条件下，局部解可沿相同压力规范拼接。[带符号通量](parts/kinetic_limit.texinc#L467) | 在所列局部与有限端点前提下回读全局光滑速度与空间均值零的压力。[条件延拓回读](parts/kinetic_limit.texinc#L596) | **充分回读已证** |

各行的覆盖范围以所链接定理的假设、定义域和量词为准。带外力爆破题面的紧支条件施加于外力，速度统一紧支是附加题面条件。[爆破题面的适用范围](parts/targets.texinc#L157)

## 已证的补充核验

- **经典纤维的独立 G-PDE 判据。** 实际预解式给出唯一热解。TPH 高阶正交估计覆盖全部正权，完整能量已覆盖 \(\varepsilon\ge1/2\)。定理 7.35 给出全体整数的高阶 Gram 余项统一迹范数界。若每个 \(0<s<1/2\) 的低阶带符号合成具有一致窗口能量界，这一判据也给出 \(\pi_\zeta\)。[实际热解](parts/spectral_moments.texinc#L1359) · [窗口估计](parts/spectral_moments.texinc#L2213)
- **有限算术。** 独立轮廓计数和临界线符号证书核验 \(0<\Im\rho\le1270\) 的 \(871\) 个零点均为临界线单零点。同一窗口给出 \(99<p/q\le715716\) 的半径下界 \(\operatorname{rad}S_{p,q}\ge M_{p,q}^{-1}\)。[有限零点证书](parts/zeta_window.texinc#L284) · [窗口覆盖的方向](parts/zeta_window.texinc#L315)
- **分型引理。** 已证的算术局部估计、周期协变界与动力学误差界，按各自的假设和 TeX 标签核对。[证明索引](proof-index.md)

## 复核

工具链固定为官方 Lean 4.36.0，直接官方基础模块为 \(\texttt{Init}\)，Lake 外部包依赖表为空。
算术矩和整周期的 Lean 声明及其核验范围按定理逐项登记。[TeX–Lean 映射](proof-index.md)
离散主丛的自由传递作用、边运输、有序复合和同端点运输等价已给出完整 Lean 推导。总算子的组合缺陷、分量差商和对偶测试共用同一运输。
附录的有限路径映射给出终点测度、所有加法测试的配对、门禁保持、商上二次推前和代价最小性的完整 Lean 推导。
配套索引按实际声明类型标明 Lean 核验的结论及正文承担的实复分析、Hilbert 完备和连续 PDE 论证。[证明索引](proof-index.md)

在本页目录运行 `python -B check_mapping.py`，可检查六项公开引文的版本、顺序和正文定位，以及 TeX 主文引用、Lean 的传递导入和逐条映射。
在仓库根目录运行 `python -B audit/check_obligations.py`，可核对本页十四行与[判定文章汇总表](../src/markdown/1795691852770_跨域证明的完备性判定：求解在G母体与回读处的证毕.md#35-汇总)的结项类型和已证范围，并复核定理前提、正文定位及归档输入的 SHA-256。[十四项验收脚本](../audit/check_obligations.py)
将 `lean/` 源码复制到工作区 `out/` 下的干净目录。主线复核运行以下命令。

```powershell
lake build
lake env leanchecker GAlgebra
lake env leanchecker Audit
lake env lean Audit.lean
```
统一审计入口核对实际映射的声明和公理。算术主线及附录的有限零点核验由同一构建复核，算术主线的 Lean 导入闭包独立保持。[构建与核验记录](../LEAN_BUILD_REPORT.md)
