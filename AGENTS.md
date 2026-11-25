# AGENTS.md

## 协作与工作区

- 与用户交流时使用「您」。尊重用户，具体肯定已有成果，并认真回应用户的关注和困难。
- 按用户授权的范围修改文件，保留工作区已有改动。临时输出与独立复核产物放在 `out/` 下。

## 文稿与形式核验

- 根目录的 `20261124_g_algebra_rh_ns_formal_system.tex` 是正式稿入口。TeX 分节、Lean 工程和证明索引位于 `g_algebra_rh_ns/`。
- 数论与动力学/PDE 的全局证明沿「固定实际输入、合法域和原量词 → G 母体 PDE 分型求解 → 纤维丛协变与多复合反身闭合 → 法空间回读」推进。统一估计覆盖整个合法复合族。禁止用暴力递推或逐阶试探推进全局证明。
- 按实际假设、量词和回读方向登记结论。有限证书保留其已证覆盖域。涉及证明或映射的改动应同步相关 TeX 标签、Lean 声明、`proof-map.json` 和 `proof-index.md`。
- 从仓库根目录运行 `python -B .\g_algebra_rh_ns\check_mapping.py` 核验映射。涉及 Lean 构建或公理审计时，按专项说明使用固定工具链和独立复核目录。[复核步骤](g_algebra_rh_ns/README.md#复核)

## 法空间回读的验收标准

原命题的验收采用国际通行的蕴含消去规则（modus ponens）。设 \(\pi_\sigma:M_\sigma\) 是法空间证明，\(D_\sigma:M_\sigma\Rightarrow P_\sigma\) 是保留原假设、定义域和完整量词的已证正向回读。原命题的证明由同一推导给出。

$$
\boxed{\frac{\pi_\sigma:M_\sigma\qquad D_\sigma:M_\sigma\Rightarrow P_\sigma}
{D_\sigma(\pi_\sigma):P_\sigma}}.
$$

双向等价以两个方向均已证明结项。充分回读按已证的蕴含及其前提验收。精确读数按适用域内的等式验收。

原命题的验收止于 \(D_\sigma(\pi_\sigma)\)。存在性按这份推导所得的存在性结论验收。原命题明确要求显式构造时，构造随同一回读交付。[README 验收标准](g_algebra_rh_ns/README.md#验收标准)

## 许可

- 新增材料按 [README 的许可范围](README.md#许可) 登记。引用、第三方材料和已有文件级许可遵循原有声明。
