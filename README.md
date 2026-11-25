# GAlgebra

GAlgebra 汇集 G 代数研究文稿、Lean 形式化代码和复核工具。正式稿以经典黎曼猜想和带外力的 Navier–Stokes 爆破为主线，给出法空间回读的条件、方向与覆盖范围。

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
| 未单独声明许可的原创代码、构建和维护配置、仓库级维护文档 | [Apache License 2.0](LICENSE) |
| 正式稿的 TeX 与 PDF、TeX 分节及声明所列配套研究材料中的原创内容 | [CC BY-NC-ND 4.0 文稿许可](LICENSE-IP) |
| 标有 `SPDX-License-Identifier: MIT` 的现有脚本 | [MIT License](LICENSES/MIT.txt) |

引用内容、第三方材料及已有独立许可声明的材料遵循各自的权利和许可声明。
