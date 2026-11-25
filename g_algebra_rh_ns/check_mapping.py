from __future__ import annotations

import argparse
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
PARTS = HERE / "parts"
MANUSCRIPT = HERE.parent / "20261124_g_algebra_rh_ns_formal_system.tex"
LEAN = HERE / "lean"
TEX_MAP = PARTS / "mapping.texinc"
LEAN_AUDIT = LEAN / "Audit.lean"
FINITE_ZETA_PARTS = {
    "arithmetic_enclosures.texinc",
    "zeta_window.texinc",
}
FINITE_ZETA_MODULE = "GAlgebra.ZetaWindow"
TEX_LABEL = re.compile(r"\\label\{((?!sec:)[^{}]+)\}")
TEX_REFERENCE = re.compile(r"\\(?:auto|eq)?ref\{([^{}]+)\}")
TEX_CITE = re.compile(r"\\cite(?:\[[^]]*\])?\{([^{}]+)\}")
TEX_LEAN = re.compile(r"\\lean\{([^{}]+)\}")
PROOF_BLOCK = re.compile(
    r"\\begin\{(theorem|lemma|proposition|corollary|definition|example)\}.*?\\end\{\1\}"
    r"(?:\s*\\begin\{proof\}.*?\\end\{proof\})?",
    re.S,
)
DECLARATION = re.compile(
    r"^(?:@\[[^\]]+\]\s*)?(?:noncomputable\s+)?"
    r"(class|structure|inductive|def|theorem)\s+([^\s(:]+)"
)


def read_json(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def read_lean_declarations() -> dict[str, tuple[str, str, int]]:
    declarations = {}
    for path in sorted((LEAN / "GAlgebra").glob("*.lean")):
        stack = []
        source = path.read_text(encoding="utf-8")
        for line_no, line in enumerate(source.splitlines(), 1):
            if line.startswith(("namespace ", "section ")):
                kind, name = line.split(maxsplit=1)
                stack.append((kind, name))
            elif line == "end" or line.startswith("end "):
                stack.pop()
            elif match := DECLARATION.match(line):
                kind, name = match.groups()
                prefix = [name for kind, name in stack if kind == "namespace"]
                qualified = ".".join([*prefix, name])
                if qualified in declarations:
                    raise ValueError(f"Repeated declaration {qualified}")
                declarations[qualified] = (kind, path.name, line_no)
        if stack:
            raise ValueError(f"Unclosed namespace or section in {path.name}")
        if re.search(r"\b(?:sorry|admit|native_decide|axiom)\b", source):
            raise ValueError(f"Unexpected unfinished proof or added axiom in {path.name}")
        for module in re.findall(r"^import (\S+)", source, re.M):
            if module != "Init" and not module.startswith("GAlgebra."):
                raise ValueError(f"Unexpected proof import {module}")
    lakefile = (LEAN / "lakefile.toml").read_text(encoding="utf-8")
    if re.search(r"^\s*(?:\[\[?\s*require\b|require\s*=)", lakefile, re.M):
        raise ValueError("Unexpected Lake dependency")
    manifest = LEAN / "lake-manifest.json"
    if manifest.exists() and read_json(manifest)["packages"]:
        raise ValueError("Unexpected package in the Lake manifest")
    return declarations


def verify_public_sources(source_map: dict, labels: set[str]) -> None:
    references = source_map["references"]
    expected = (
        (2025, "v1.0", "17651584"),
        (2025, "v1.2", "17686133"),
        (2025, "v1.1", "17744672"),
        (2025, "v1.0", "17762295"),
        (2026, "v5.2", "22739417"),
        (2026, "v1.1", "24175031"),
    )
    provided = tuple((item["year"], item["version"], item["doi"].removeprefix("10.5281/zenodo."))
                     for item in references)
    keys = {item["key"] for item in references}
    if provided != expected or len(keys) != len(expected):
        raise ValueError("Public references must use the six requested releases in order")
    for item in references:
        if (item["author"] != "Gao, Z." or not item["title"] or not item["scope"]
                or not item["locator"] or not item["labels"] or not set(item["labels"]) <= labels):
            raise ValueError(f"Incomplete public reference {item}")
    manuscript = "\n".join(path.read_text(encoding="utf-8")
                           for path in [MANUSCRIPT, *PARTS.glob("*.texinc")] if path != TEX_MAP)
    used = {key.strip() for cite in TEX_CITE.findall(manuscript)
            for key in cite.split(",")}
    if used != keys:
        raise ValueError(f"Unmatched public citation keys: {sorted(used ^ keys)}")


def manuscript_locations(mapping: list[dict]) -> dict[str, tuple[str, int]]:
    actual = {}
    for path in sorted(PARTS.glob("*.texinc")):
        if path == TEX_MAP:
            continue
        source = path.read_text(encoding="utf-8")
        for match in TEX_LABEL.finditer(source):
            label = match[1]
            if label in actual:
                raise ValueError(f"Repeated TeX label {label}")
            actual[label] = (path.relative_to(HERE).as_posix(), source.count("\n", 0, match.start()) + 1)
    mapped = {item["label"] for item in mapping}
    if len(mapped) != len(mapping) or mapped != actual.keys():
        raise ValueError(f"Unmatched manuscript labels: {actual.keys() ^ mapped}")
    return actual


def lean_import_closure(roots: set[str]) -> set[str]:
    pending = list(roots)
    seen = set()
    while pending:
        module = pending.pop()
        if module == "Init" or module in seen:
            continue
        seen.add(module)
        path = LEAN.joinpath(*module.split(".")).with_suffix(".lean")
        pending.extend(re.findall(r"^import (\S+)", path.read_text(encoding="utf-8"), re.M))
    return seen


def check_build_entries() -> None:
    lakefile = (LEAN / "lakefile.toml").read_text(encoding="utf-8")
    package, *sections = re.split(r"(?m)^\[\[lean_lib\]\][ \t]*$", lakefile)
    defaults = re.search(r"(?m)^defaultTargets\s*=\s*(\[[^\n]+\])$", package)
    libraries = {}
    for section in sections:
        name = re.search(r'(?m)^name\s*=\s*"([^"]+)"$', section)
        if name is None or name[1] in libraries:
            raise ValueError("Missing or repeated Lean library name")
        libraries[name[1]] = section
    if defaults is None or json.loads(defaults[1]) != ["GAlgebra"]:
        raise ValueError("The default Lake target must be the main library")
    if set(libraries) != {"GAlgebra"}:
        raise ValueError("Expected a single audited Lean library")
    main_globs = re.search(r"(?m)^globs\s*=\s*(\[[^\n]+\])$", libraries["GAlgebra"])
    if main_globs is None or json.loads(main_globs[1]) != ["GAlgebra", "Audit"]:
        raise ValueError("Lake must build the proof library and its audit")


def check_proof_dependencies(
    mapping: list[dict], declarations: dict[str, tuple[str, str, int]]
) -> set[str]:
    check_build_entries()
    named = {name for row in mapping for name in row["lean"]}
    if missing := named - declarations.keys():
        raise ValueError(f"Unknown Lean declaration(s): {sorted(missing)}")

    parts = {path.name: path.read_text(encoding="utf-8")
             for path in PARTS.glob("*.texinc") if path != TEX_MAP}
    finite_labels = {label for name in FINITE_ZETA_PARTS for label in TEX_LABEL.findall(parts[name])}
    finite_names = {name.removeprefix("GAlgebra.") for name, (_, file, _) in declarations.items()
                    if Path(file).stem == "ZetaWindow"}
    front = MANUSCRIPT.read_text(encoding="utf-8").split(r"\appendix", 1)[0]
    for name, contents in [(MANUSCRIPT.name, front), *parts.items()]:
        if name in FINITE_ZETA_PARTS:
            continue
        links = finite_labels.intersection(TEX_REFERENCE.findall(contents))
        inputs = {Path(target).name for target in re.findall(r"\\input\{([^{}]+)\}", contents)}
        finite_inputs = FINITE_ZETA_PARTS.intersection(inputs)
        inline = {entry.removeprefix("GAlgebra.") for entry in TEX_LEAN.findall(contents)}
        finite_reads = finite_names.intersection(inline)
        if links or finite_inputs or finite_reads:
            raise ValueError(f"{name} depends on finite zeta verification: "
                             f"{sorted(links | finite_inputs | finite_reads)}")

    main_modules = lean_import_closure({"GAlgebra"})
    if FINITE_ZETA_MODULE in main_modules:
        raise ValueError("The proof library imports finite zeta verification")
    audited_modules = main_modules | lean_import_closure({FINITE_ZETA_MODULE})
    for row in mapping:
        modules = {f"GAlgebra.{Path(declarations[name][1]).stem}" for name in row["lean"]}
        allowed_modules = audited_modules if row["label"] in finite_labels else main_modules
        if missing := modules - allowed_modules:
            raise ValueError(f"{row['label']} maps outside its Lean imports: {sorted(missing)}")
    return finite_labels


def tex_refs(labels: list[str]) -> str:
    return r"、\allowbreak ".join(r"\ref{" + label + "}" for label in labels)


def make_tex(source_map: dict, proof_map: list[dict], finite_labels: set[str]) -> str:
    head = r"""\section{公开文献与本文的对应构造}
\label{sec:sources}
表中列出指定版本的公开文献及其结构用途。定理的完整推导、实际适用域和终端前提见所列正文及附录。
\small
\begin{longtable}{@{}P{.13\textwidth}P{.48\textwidth}P{.30\textwidth}@{}}
\toprule 文献 & 公开构造的用途 & 本文位置\\\midrule
\endfirsthead
\toprule 文献 & 公开构造的用途 & 本文位置\\\midrule
\endhead
\bottomrule
\endlastfoot
"""
    sources = "\n".join(
        rf"\cite{{{item['key']}}} & {item['scope']} & {tex_refs(item['labels'])}\\"
        for item in source_map["references"]
    )
    middle = r"""
\end{longtable}
\normalsize

\section{正文结论与 Lean 声明逐项映射}
\label{sec:lean-map}
Lean 名称均在 \lean{GAlgebra} 命名空间。文件与行号见配套索引。
所用声明的类型及公理依赖在 \lean{Audit.lean} 中检查。
最后一列按实际声明类型标明 Lean 核验的结论及正文的证明环节。
\small
\begin{longtable}{@{}P{.09\textwidth}P{.55\textwidth}P{.29\textwidth}@{}}
\toprule 正文 & Lean 声明 & 证明覆盖\\\midrule
\endfirsthead
\toprule 正文 & Lean 声明 & 证明覆盖\\\midrule
\endhead
\bottomrule
\endlastfoot
"""
    proof_rows = []
    for row in proof_map:
        names = r"\par ".join(r"\lean{" + n.removeprefix("GAlgebra.") + "}" for n in row["lean"])
        scope = "有限核验。" if row["label"] in finite_labels else ""
        proof_rows.append(rf"\ref{{{row['label']}}} & {names} & {scope}{row['note']}\\[.25em]")
    tail = r"""
\end{longtable}
\normalsize

\clearpage
\phantomsection
\addcontentsline{toc}{section}{参考文献}
\begingroup\small
\begin{thebibliography}{9}
\raggedright
\setlength{\itemsep}{0pt}
"""
    bibliography = []
    for item in source_map["references"]:
        title = item["title"].replace("—", "---").replace("–", "--")
        bibliography.append(
            rf"\bibitem{{{item['key']}}} {item['author']} ({item['year']}). \emph{{{title}}}."
            + "\n"
            + rf"\newblock Zenodo，{item['version']}。DOI：\url{{https://doi.org/{item['doi']}}}。"
        )
    return (head + sources + middle + "\n".join(proof_rows) + tail
            + "\n\n".join(bibliography) + "\n"
            + "\\end{thebibliography}\n\\endgroup\n")


def make_lean_audit(imports: list[str], mapping: list[dict]) -> str:
    checked = sorted({name for row in mapping for name in row["lean"]})
    rows = [
        *(f"import {module}" for module in imports),
        "",
        "-- Generated by check_mapping.py. Checks declarations cited in this part of the manuscript.",
        "",
    ]
    rows.extend(f"#check {name}" for name in checked)
    rows.append("")
    rows.extend(f"#print axioms {name}" for name in checked)
    return "\n".join(rows) + "\n"


def lean_links(declarations: dict[str, tuple[str, str, int]], names: list[str]) -> str:
    result = []
    for name in names:
        _, file, line = declarations[name]
        result.append(f"[{name.removeprefix('GAlgebra.')}](lean/GAlgebra/{file}#L{line})")
    return "<br>".join(result)


def manuscript_link(file: str, line: int, title: str | None = None) -> str:
    return f"[{title or Path(file).name + ':' + str(line)}]({file}#L{line})"


def reference_index(
    locations: dict[str, tuple[str, int]], publications: dict[str, dict], proof_map: dict[str, dict],
    declarations: dict[str, tuple[str, str, int]],
) -> list[str]:
    rows = []
    for path in [MANUSCRIPT, *sorted(PARTS.glob("*.texinc"))]:
        if path == TEX_MAP or path.name == "internal_basis.texinc" or path.name in FINITE_ZETA_PARTS:
            continue
        source = path.read_text(encoding="utf-8")
        if path == MANUSCRIPT:
            source = source.split(r"\appendix", 1)[0]
            file = "../" + path.name
        else:
            file = path.relative_to(HERE).as_posix()
        seen = set()
        for match in TEX_REFERENCE.finditer(source):
            target = match[1]
            if target not in locations or locations[target][0] != "parts/internal_basis.texinc":
                continue
            line = source.count("\n", 0, match.start()) + 1
            if (line, target) in seen:
                continue
            seen.add((line, target))
            appendix = manuscript_link(*locations[target], target)
            lean = lean_links(declarations, proof_map[target]["lean"])
            rows.append(f"| {manuscript_link(file, line)} | {appendix} | {lean} |")
        proof_blocks = []
        for block in PROOF_BLOCK.finditer(source):
            labels = TEX_LABEL.findall(block[0])
            if len(labels) == 1:
                proof_blocks.append((block.start(), block.end(), labels[0]))
        for citation in TEX_CITE.finditer(source):
            keys = citation[1].split(",")
            offset = citation.start()
            line = source.count("\n", 0, offset) + 1
            label = next((name for start, end, name in proof_blocks if start <= offset < end), None)
            public = "<br>".join(public_location(publications[key.strip()]) for key in keys)
            if label is None:
                lean = "结构说明。文献与对应构造见下表。"
            else:
                lean = lean_links(declarations, proof_map[label]["lean"])
            rows.append(f"| {manuscript_link(file, line, label)} | {public} | {lean} |")
    return rows


def public_location(publication: dict) -> str:
    return (f"[{publication['doi']} {publication['version']}](https://doi.org/{publication['doi']})"
            f" · {publication['locator']}")


def make_index(
    declarations: dict[str, tuple[str, str, int]], mapping: list[dict],
    finite_labels: set[str], locations: dict[str, tuple[str, int]], source_map: dict,
) -> str:
    lines = [
        "# 正文与 Lean 声明索引", "",
        "正文与附录的 TeX 标签直接定位原式。正文的文献引用及内化附录调用均定位到使用行。"
        "第二表按声明类型标明 Lean 核验的结论及正文的证明环节。"
        "声明类型和公理依赖在 Audit.lean 核验。母体见证、回读及其覆盖域见[专项进度表](README.md#整体证明义务完成进度表)。", "",
        "## 正文引用位置", "",
        "| 正文调用处 | 公开文献或内化附录 | Lean 声明 |", "| --- | --- | --- |",
    ]
    publications = {item["key"]: item for item in source_map["references"]}
    proof_map = {item["label"]: item for item in mapping}
    lines.extend(reference_index(locations, publications, proof_map, declarations))
    lines.extend([
        "", "## 定理、构造与核验范围", "",
        "| TeX 定位 | 公开文献定位 | Lean 声明与位置 | 覆盖范围 |",
        "| --- | --- | --- | --- |",
    ])
    for row in mapping:
        label = row["label"]
        link = manuscript_link(*locations[label], label)
        sources = "<br>".join(public_location(item) for item in publications.values()
                               if label in item["labels"]) or "文稿推导"
        scope = "有限核验。" if label in finite_labels else ""
        lines.append(f"| {link} | {sources} | {lean_links(declarations, row['lean'])} | {scope}{row['note']} |")
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true", help="Regenerate the appendix and audit")
    args = parser.parse_args()
    mapping = read_json(HERE / "proof-map.json")
    source_map = read_json(HERE / "sources.json")
    locations = manuscript_locations(mapping)
    verify_public_sources(source_map, set(locations))
    declarations = read_lean_declarations()
    finite_labels = check_proof_dependencies(mapping, declarations)
    mapping.sort(key=lambda row: row["label"] in finite_labels)
    outputs = {
        TEX_MAP: make_tex(source_map, mapping, finite_labels),
        LEAN_AUDIT: make_lean_audit(["GAlgebra", FINITE_ZETA_MODULE], mapping),
        HERE / "proof-index.md": make_index(declarations, mapping, finite_labels, locations, source_map),
    }
    for path, content in outputs.items():
        if args.write:
            with path.open("w", encoding="utf-8", newline="\n") as out:
                out.write(content)
        elif path.read_text(encoding="utf-8") != content:
            raise ValueError(f"Generated file differs: {path.name}")
    proofs = sum(kind == "theorem" for kind, _, _ in declarations.values())
    print(f"{len(source_map['references'])} public references, {len(mapping)} TeX mappings, "
          f"{proofs} Lean theorems, 0 main-route dependencies on finite zeta verification")


if __name__ == "__main__":
    main()

