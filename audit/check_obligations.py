from argparse import ArgumentParser
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import re
import sys

parser = ArgumentParser(description="Check the fourteen recorded conclusions against their manuscript locations and the published audit.")
parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
parser.add_argument("--receipt", type=Path)
args = parser.parse_args()
if not __debug__:
    parser.error("Run without -O so all verification checks are active.")
root = args.root.resolve()
project = root / "g_algebra_rh_ns"
sys.path.insert(0, str(project))
import check_mapping as checker

eq, impl, exact = "双向等价", "充分回读", "精确读数"
endpoint = "有限端点的条件延拓回读"
prime = "prop:prime-additive-readback"
grh = "thm:grh-localized-moments"
flux = "prop:kinetic-contact-flux"
joint = "thm:kinetic-joint-budget"
rows = [
    ("经典黎曼猜想", eq, ["thm:grh-family-readback", "thm:xi-moment-readback"],
     r"\mathsf E_\zeta", "实际秩一完备函数的负对数导数与全部 Taylor 系数给出每个实多项式上的矩倍数关系。给定全秩见证，限制到平凡分量、约去 2，再施用经典回读。"),
    ("带光滑紧支外力", impl, ["lem:flow-period-controlled-inverse", "thm:flow-period-pulse-readback"],
     r"\mathsf E_{\rm per}", "单位黏性下合法完整周期有非零解时，回读覆盖全部正黏性。"),
    ("二元哥德巴赫", eq, [prime], "G_2(N)>0", "逐偶数 N≥4 的加权和频正性与存在素数分拆等价。"),
    ("孪生素数", eq, [prime], "T_{(0,2)}", "Abel 迹在 t↓0 发散与孪生素数对首项无界等价。"),
    ("Hardy–Littlewood", eq, [prime], r"\mathfrak S", "对每组固定互异可容许偏移，加权与普通素数组计数的渐近式等价。"),
    ("勒让德", eq, [prime], "I(m)>0", "逐整数 m≥1 的开平方区间内素数对数权重之和为正与存在素数等价。"),
    ("原始 Dirichlet", eq, ["thm:dirichlet-analytic-input", grh], r"\mathsf E_\pi", "每个原始特征的实际解析输入、逐纤维局部化矩判据及正反回读。"),
    ("有理数域上的全秩", eq, [grh, "thm:grh-family-readback"], r"\mathsf E_\pi", "在已核验的解析输入下，覆盖有理数域所有秩与标准尖点自守纤维的矩条件与全族零点命题等价。全秩结论蕴含经典特例。"),
    ("硬球多体相流", exact, [flux], "可积入射", "固定合法参数、同一制备中的可交换标签和可积入射接触迹下的两种归一化通量。"),
    ("BBGKY →", impl, [flux, joint], "同地乘积", "固定 δ、共同粒子时间窗；初值、输运及入射接触配对收敛到所列读数。"),
    ("玻尔兹曼 →", impl, ["prop:kinetic-nsf-moment-closure", joint], "逆证书", "近 Maxwell 共同光滑窗内的二阶展开、碰撞逆与矩测试。"),
    ("幂律联合极限", impl, [joint, "prop:kinetic-equilibrium-joint"], "o(", "共同窗两层误差之和为 o(δ) 足够。Maxwell 平衡子域在 0<β<1/2、任意固定 T,κ>0 已实际回读。"),
    ("环面硬球玻尔兹曼", impl, [endpoint], "重启", "给定局部唯一解、合法重启和有限端点延拓控制；同类全局非负经典解存在且唯一。"),
    ("周期无外力 Navier", impl, [endpoint], "重启", "对每个正黏性和所列无散初值，在共同的重启及端点控制下延拓，压力取空间均值零。"),
]
need = {
    "thm:xi-moment-readback": [r"\forall p\in\RR[t]", r"\Longleftrightarrow", r"\mathsf B_{\mathbf 1}"],
    "lem:flow-period-controlled-inverse": [r"0<\beta<1/2", "有界线性右逆"],
    "thm:flow-period-pulse-readback": ["非零", "零初值", "有界总动能", "全部正黏性", r"\nu^{5/2}"],
    prime: [r"G_2(N)", r"T_{(0,2)}", r"R_{\mathbf h}(X)", "I(m)>0", r"(\log X)^k", r"(m+1)^2"],
    "thm:dirichlet-analytic-input": ["原始 Dirichlet", "导子", "整延拓"],
    grh: [r"\forall\rho", r"\forall p\in\RR[t]", "中心重数"],
    "thm:grh-family-readback": [r"\forall n\ge r", r"\forall\pi", "已核验解析输入",
        r"L(s,\pi_0)=\zeta(s)", r"B_{\pi_0}=\xi^2", r"R_{\pi_0}=2R", r"\mathcal L_{\pi_0}=2\mathcal L",
        r"\Pi(1,\pi_0)", r"p\in\RR[t]", r"D_\zeta(\pi_\zeta)", r"\mathsf P_{\rm GRH}^{\ge1}(\QQ)\Rightarrow\mathsf B_{\mathbf1}",
        r"A_{\pi_0}(z)=D(z)^2", r"\mathcal L_{\pi_0}(q)=2\mathcal L(q)", r"\lean{grh_trivial_xi_readback}"],
    flux: [r"P_{k,j}P_{N,k}=P_{N,j}", "(N-k)a^2", r"\lambda a^2", "收敛到同地乘积", r"Q(f,f)"],
    "prop:kinetic-nsf-moment-closure": [r"o(\delta^2)", "两个输运源", r"L^{-1}", "两个系数"],
    joint: [r"D_{\rm BG}+D_{\rm kin}=o(\delta)", r"s\le T/\delta", r"\kappa>0"],
    "prop:kinetic-equilibrium-joint": [r"0<\beta<1/2", r"\mathbb E[N]a^2", "截断动量恒为零"],
    endpoint: ["局部唯一性", "统一正下界", "延伸越过端点", "非负性", "压力取空间均值零"],
}
def read(path):
    return path.read_text(encoding="utf-8")


def status_text(cell):
    return cell.strip().replace("**", "").rstrip("。")


maps = {r["label"]: r for r in json.loads(read(project / "proof-map.json"))}
blocks = {}
for path in sorted((project / "parts").glob("*.texinc")):
    if path.name == "mapping.texinc":
        continue
    body = read(path)
    for block in checker.PROOF_BLOCK.finditer(body):
        labels = checker.TEX_LABEL.findall(block[0])
        if len(labels) == 1 and labels[0] in need:
            blocks[labels[0]] = path, body.count("\n", 0, block.start()) + 1, block[0]
    marker = r"\begin{remark}[" + endpoint + "]"
    if marker in body:
        start = body.index(marker)
        end = body.index(r"\end{remark}", start) + len(r"\end{remark}")
        blocks[endpoint] = path, body.count("\n", 0, start) + 1, body[start:end]
assert set(blocks) == set(need)
evidence = read(root / "LEAN_BUILD_EVIDENCE.txt")
checksums = re.findall(r"^([a-f0-9]{64})  ([^\r\n]+)$", evidence, re.M)
lean = project / "lean"
expected = [*lean.glob("*.lean"), *(lean / "GAlgebra").glob("*.lean"),
            *(lean / name for name in (".gitignore", "lean-toolchain", "lakefile.toml", "lake-manifest.json")),
            *(project / name for name in ("proof-map.json", "proof-index.md", "sources.json", "check_mapping.py")),
            *(project / "parts").glob("*.texinc"), root / "20261124_g_algebra_rh_ns_formal_system.tex",
            root / "audit/check_obligations.py"]
names = {p.relative_to(root).as_posix() for p in expected}
assert len(checksums) == len(names) and {p for _, p in checksums} == names, "Audit input manifest differs from the project"
for h, relative in checksums:
    assert sha256((root / relative).read_bytes()).hexdigest() == h, relative
inputs = "".join(f"{h}  {name}\n" for h, name in sorted(checksums, key=lambda row: row[1]))
assert "输入集合 SHA-256 " + sha256(inputs.encode()).hexdigest() in evidence
decls = {n for r in maps.values() for n in r["lean"]}
audit_names = re.findall(r"^'(GAlgebra\.[^']+)' (?:does not depend on any axioms|depends on axioms: \[[^\n]*\])$", evidence, re.M)
assert len(decls) == len(audit_names) and set(audit_names) == decls
rank_one = {"GAlgebra." + name for name in (
    "XiArithmetic.completionApprox", "grh_trivial_xi_arithmetic", "grh_trivial_xi_limit",
    "XiTaylorGerm", "grh_trivial_xi_factors", "grh_trivial_moment_scale",
    "grh_trivial_moment_readback", "grh_trivial_xi_square", "grh_xi_regular", "grh_trivial_xi_resolvent",
    "TaylorSeries.deriv_product", "TaylorSeries.resolvent_square", "grh_trivial_xi_coeff", "grh_trivial_xi_moment",
    "grh_trivial_xi_readback")}
assert rank_one <= set(maps["thm:grh-family-readback"]["lean"])
assert "GAlgebra.grand_riemann_rank_one_readback" in maps["lem:grh-rank-one-base"]["lean"]
audit_doc = next((root / "src/markdown").glob("1795704572379_*.md"))
article = read(audit_doc)
sections = re.findall(r"^### 2\.(\d+) (.+)$", article, re.M)
table = [(n, line.split("|")[1:-1]) for n, line in enumerate(read(project / "README.md").splitlines(), 1)
         if line.startswith(("| 最初 |", "| 追加 |", "| 全秩子义务 |", "| 联合极限子义务 |"))]
summary_doc = next((root / "src/markdown").glob("1795691852770_*.md"))
summary_rows = [line.split("|")[1:-1] for line in read(summary_doc).splitlines()
                if line.startswith(("| 最初 |", "| 追加 |", "| 全秩子义务 |", "| 联合极限 |"))]
assert len(table) == len(rows) == len(sections) == len(summary_rows) == 14
out_rows = []
for idx, ((key, kind, refs, symbol, scope), (line, cols), (sn, heading)) in enumerate(zip(rows, table, sections), 1):
    assert len(cols) == 6 and key in cols[1] and int(sn) == idx, key
    status = status_text(cols[-1])
    expected_status = "原域内精确读数已证" if kind == exact else kind + "已证"
    if "prop:kinetic-equilibrium-joint" in refs:
        expected_status += "。平衡子域的原命题已证"
    assert status == expected_status, f"{key}：登记为「{status}」，对应定理的结项为「{expected_status}」"
    summary = summary_rows[idx - 1]
    assert len(summary) == 5 and key in summary[1] and status_text(summary[3]) == status, f"{key}：文章汇总表与专项登记不一致"
    assert symbol in "".join(cols) and re.search(r"\[.+?\]\(.+?\)", cols[4]), key
    section = article.split(f"### 2.{idx} {heading}\n", 1)[1].split("\n### ", 1)[0].split("\n## ", 1)[0]
    assert all(need[ref] and all(test in blocks[ref][2] for test in need[ref]) for ref in refs), key
    locations = []
    for ref in refs:
        p, line_no, text = blocks[ref]
        anchor = (p.relative_to(project).as_posix() + "#L" + str(line_no))
        # A textual proof may link to a line inside a proposition.
        nums = [int(n) for n in re.findall(re.escape(p.name) + r"#L(\d+)", section)]
        within = any(line_no <= n < line_no + len(text.splitlines()) for n in nums)
        assert ref in section or within or anchor in "".join(cols), (key, ref)
        if ref != endpoint:
            assert ref in maps and r"\begin{proof}" in text and r"\end{proof}" in text
        locations.append({"statement": ref, "source": p.relative_to(root).as_posix() + "#L" + str(line_no),
                          "lean": maps[ref]["lean"] if ref != endpoint else [],
                          "argument": "正文延拓论证" if ref == endpoint else "正文论证及索引列明的 Lean 范围"})
    out_rows.append({"id": idx, "entry": heading, "kind": kind, "status": status, "scope": scope, "register_line": line, "evidence": locations})
counts = Counter(r["kind"] for r in out_rows)
assert counts == {eq: 7, impl: 6, exact: 1}
pdf = root / "20261124_g_algebra_rh_ns_formal_system.pdf"
digest = sha256(pdf.read_bytes()).hexdigest()
assert re.search(r"^配套正式稿 PDF [1-9]\d* 页，SHA-256 " + digest, evidence, re.M)
baseline = re.search(r"^Git 基线 [^\n]*，提交 ([a-f0-9]{40})$", evidence, re.M)
assert baseline, "Missing Git baseline in the archived evidence"
result = {"baseline": baseline[1],
          "acceptance": "双向等价以两个方向均已证明结项。充分回读以所列母体前提下推出原结论的证明结项。精确读数按适用域内的等式结项。覆盖原量词的母体见证 π 经已证正向回读，原命题即在 D(π) 处证毕。",
          "counts": dict(counts), "mappings": len(maps), "declarations": len(decls),
          "verified_input_hashes": len(checksums), "pdf_sha256": digest, "rows": out_rows}
if args.receipt:
    args.receipt.write_bytes((json.dumps(result, ensure_ascii=False, indent=2) + "\n").encode())
print(f"14 manuscript entries: {counts[eq]} equivalences, {counts[impl]} implications, {counts[exact]} exact readout. Verified {len(checksums)} input hashes and {len(decls)} declarations.")
