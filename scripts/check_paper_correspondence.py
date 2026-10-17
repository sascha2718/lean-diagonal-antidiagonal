#!/usr/bin/env python3
"""Static consistency checks for the paper--Lean correspondence manifest.

The manifest `paper-correspondence.yaml` records, for every numbered statement of the
manuscript and for selected unnumbered prose, a fingerprint of its LaTeX source, its printed
number, its status in the formalisation and the Lean declarations that correspond to it. This
script checks that the manifest agrees with the manuscript, the Lean sources,
`comparator-config.json`, `formalization.yaml` and `docs/correspondence.md`:

* every numbered statement environment of the manuscript has exactly one entry, with the
  environment kind and the printed number the manuscript gives it;
* the fingerprint of every statement, of every prose span and of the whole manuscript is
  unchanged since the correspondence was last reviewed, so that an edit of the manuscript is
  reported until its Lean side has been checked;
* every Lean name the manifest mentions is declared in the sources, every literature hypothesis
  is a `Prop`-valued definition, the sources declare no axiom and contain no `sorry` outside
  `Challenge.lean`;
* the headline entries, `comparator-config.json`, `Challenge.lean`, `Solution.lean` and the
  alignment section of `formalization.yaml` name the same audited theorems;
* `docs/correspondence.md` mentions every numbered statement and every audited theorem.

Fingerprints hash the TeX tokens of a span, ignoring comments and layout whitespace. After a
manuscript change has been reviewed against the Lean side, `--write-fingerprints` records the
new fingerprints in place; `--print-fingerprints` only prints them.

This script deliberately does not invoke Lean or LaTeX. A successful run is not a substitute
for elaboration by Lean, and it does not establish mathematical equivalence.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any


# The theorem-like environments of the manuscript that share the theorem counter, which is
# numbered within sections. `claim` is starred in the preamble and so unnumbered.
NUMBERED_ENVIRONMENTS = {
    "theorem",
    "proposition",
    "lemma",
    "corollary",
    "conjecture",
    "remark",
    "remarks",
    "example",
    "definition",
    "question",
}
# Label prefixes the manuscript uses for statement environments.
LABEL_PREFIXES = ("thm", "lem", "prop", "cor", "def", "rem", "ex", "q", "conj")
LABEL_RE = re.compile(r"\\label\{((?:" + "|".join(LABEL_PREFIXES) + r"):[^}]+)\}")
SOURCE_LABEL_RE = re.compile(r"^(?:" + "|".join(LABEL_PREFIXES) + r"):")
BEGIN_RE = re.compile(r"\\begin\{(" + "|".join(sorted(NUMBERED_ENVIRONMENTS)) + r")\}")
NEWTHEOREM_RE = re.compile(r"\\newtheorem\{([A-Za-z]+)\}")
NUMBERING_RE = re.compile(
    r"\\section\*?\{|\\appendix\b|\\begin\{(" + "|".join(sorted(NUMBERED_ENVIRONMENTS)) + r")\}"
)
ALLOWED_STATUSES = {"formalized", "partially_formalized", "cited", "intentionally_unformalized"}
MAPPED_STATUSES = {"formalized", "partially_formalized"}
ALLOWED_RELATIONS = {
    "exact",
    "split",
    "representation",
    "specialization",
    "generalization",
    "stronger",
    "partial",
}
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
# Directories under the Lean root that hold no library source.
EXCLUDED_DIRECTORIES = {".lake", "Archive", "tools"}
DECL_RE = re.compile(
    r"^\s*"
    r"(?:@\[[^\]]*\]\s+)*"
    r"(?:(?:private|protected|public|noncomputable|unsafe|nonrec|partial)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|class|inductive|axiom|opaque|instance)\s+"
    r"([^\s\(\{\[:]+)"
)
SHA_RE = re.compile(r"[0-9a-f]{64}")


class ManifestError(ValueError):
    pass


@dataclass(frozen=True)
class PaperDeclaration:
    label: str | None
    kind: str
    number: str
    file: Path
    line: int
    text: str


@dataclass(frozen=True)
class LeanDeclaration:
    name: str
    kind: str
    file: Path
    line: int
    span: str


# ---------------------------------------------------------------------------------------------
# Manifest loading: a dependency-free YAML subset.


def _scalar(raw: str, path: Path, line: int) -> Any:
    raw = raw.strip()
    if not raw:
        return None
    if raw.startswith(("\"", "'", "[", "{")):
        if raw.startswith("'"):
            if not raw.endswith("'"):
                raise ManifestError(f"{path}:{line}: unterminated quoted scalar")
            return raw[1:-1].replace("''", "'")
        try:
            return json.loads(raw)
        except json.JSONDecodeError as exc:
            raise ManifestError(f"{path}:{line}: invalid quoted/inline value: {exc}") from exc
    if raw in {"true", "false"}:
        return raw == "true"
    if raw in {"null", "~"}:
        return None
    if re.fullmatch(r"-?\d+", raw):
        return int(raw)
    if raw.startswith((">", "|")):
        raise ManifestError(
            f"{path}:{line}: folded and literal YAML blocks are unsupported; "
            "use a one-line quoted scalar"
        )
    return raw


def _key_value(text: str, path: Path, line: int) -> tuple[str, Any]:
    if ":" not in text:
        raise ManifestError(f"{path}:{line}: expected 'key: value'")
    key, raw = text.split(":", 1)
    key = key.strip()
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", key):
        raise ManifestError(f"{path}:{line}: invalid key {key!r}")
    return key, _scalar(raw, path, line)


def load_manifest(path: Path) -> dict[str, Any]:
    """Load the documented YAML subset used by the manifest.

    JSON is accepted as well because it is a YAML subset. The YAML form supports top-level
    scalars and inline JSON values, a top-level ``manuscript_files`` list, and a top-level
    ``entries`` list of mappings whose values are scalars, inline JSON values or scalar lists.
    """

    text = path.read_text(encoding="utf-8")
    try:
        value = json.loads(text)
    except json.JSONDecodeError:
        value = None
    if value is not None:
        if not isinstance(value, dict):
            raise ManifestError(f"{path}: top-level JSON/YAML value must be a mapping")
        return value

    result: dict[str, Any] = {}
    top_list: str | None = None
    current_entry: dict[str, Any] | None = None
    entry_list: str | None = None

    for line_no, original in enumerate(text.splitlines(), 1):
        if not original.strip() or original.lstrip().startswith("#"):
            continue
        if "\t" in original[: len(original) - len(original.lstrip())]:
            raise ManifestError(f"{path}:{line_no}: indentation must use spaces")
        indent = len(original) - len(original.lstrip(" "))
        stripped = original.strip()

        if indent == 0:
            key, scalar = _key_value(stripped, path, line_no)
            if key in result:
                raise ManifestError(f"{path}:{line_no}: duplicate top-level key {key!r}")
            if scalar is None and key in {"manuscript_files", "entries"}:
                result[key] = []
                top_list = key
            else:
                result[key] = scalar
                top_list = None
            current_entry = None
            entry_list = None
            continue

        if top_list == "manuscript_files":
            if indent != 2 or not stripped.startswith("- "):
                raise ManifestError(f"{path}:{line_no}: expected a two-space-indented list item")
            result[top_list].append(_scalar(stripped[2:], path, line_no))
            continue

        if top_list == "entries":
            if indent == 2 and stripped.startswith("- "):
                current_entry = {}
                result["entries"].append(current_entry)
                entry_list = None
                remainder = stripped[2:].strip()
                if remainder:
                    key, scalar = _key_value(remainder, path, line_no)
                    current_entry[key] = scalar
                continue
            if current_entry is None:
                raise ManifestError(f"{path}:{line_no}: entry field precedes the first entry")
            if indent == 4:
                key, scalar = _key_value(stripped, path, line_no)
                if key in current_entry:
                    raise ManifestError(f"{path}:{line_no}: duplicate entry key {key!r}")
                if scalar is None:
                    current_entry[key] = []
                    entry_list = key
                else:
                    current_entry[key] = scalar
                    entry_list = None
                continue
            if indent == 6 and stripped.startswith("- ") and entry_list:
                current_entry[entry_list].append(_scalar(stripped[2:], path, line_no))
                continue
            raise ManifestError(f"{path}:{line_no}: unsupported entries indentation or syntax")

        raise ManifestError(f"{path}:{line_no}: unexpected indentation")

    return result


def _name_list(entry: dict[str, Any], key: str, where: str) -> list[str]:
    value = entry.get(key, [])
    if isinstance(value, str):
        value = [value]
    if not isinstance(value, list) or not all(isinstance(name, str) and name for name in value):
        raise ManifestError(f"{where}: {key} must be a list of nonempty declaration names")
    entry[key] = value
    return value


def validate_manifest(data: dict[str, Any], path: Path) -> tuple[list[str], list[dict[str, Any]]]:
    manuscript_files = data.get("manuscript_files")
    entries = data.get("entries")
    if not isinstance(manuscript_files, list) or not manuscript_files or not all(
        isinstance(item, str) and item for item in manuscript_files
    ):
        raise ManifestError(f"{path}: manuscript_files must be a nonempty list of paths")
    if not isinstance(entries, list) or not entries:
        raise ManifestError(f"{path}: entries must be a nonempty list")
    snapshots = data.get("manuscript_sha256")
    if not isinstance(snapshots, dict) or set(snapshots) != set(manuscript_files):
        raise ManifestError(f"{path}: manuscript_sha256 must cover every manuscript file")
    for digest in snapshots.values():
        if not isinstance(digest, str) or not SHA_RE.fullmatch(digest):
            raise ManifestError(f"{path}: invalid manuscript SHA-256 fingerprint")
    revision = data.get("manuscript_revision")
    if revision is not None and not (isinstance(revision, str) and re.fullmatch(r"[0-9a-f]{40}", revision)):
        raise ManifestError(f"{path}: manuscript_revision must be a full git commit hash")

    seen_sources: set[str] = set()
    seen_labels: set[str] = set()
    for index, entry in enumerate(entries, 1):
        where = f"{path}: entry {index}"
        if not isinstance(entry, dict):
            raise ManifestError(f"{where} must be a mapping")
        source = entry.get("source")
        kind = entry.get("kind")
        status = entry.get("status")
        if not isinstance(source, str) or not source:
            raise ManifestError(f"{where}: source must be a nonempty string")
        where = f"{path}: entry {index} ({source})"
        if source in seen_sources:
            raise ManifestError(f"{where}: duplicate source")
        seen_sources.add(source)
        if kind not in NUMBERED_ENVIRONMENTS | {"prose"}:
            raise ManifestError(f"{where}: kind must be a numbered environment or 'prose'")
        digest = entry.get("sha256")
        if not isinstance(digest, str) or not SHA_RE.fullmatch(digest):
            raise ManifestError(f"{where}: a reviewed sha256 fingerprint is required")
        if kind == "prose":
            if entry.get("file") not in manuscript_files:
                raise ManifestError(f"{where}: prose needs a manuscript file")
            if not all(isinstance(entry.get(k), str) and entry[k] for k in ("start", "end")):
                raise ManifestError(f"{where}: prose needs nonempty start and end anchors")
            for key in ("label", "match", "number"):
                if key in entry:
                    raise ManifestError(f"{where}: prose carries no {key}")
        else:
            # A labelled statement uses `label`; an unlabelled one uses a unique text `match`.
            if ("label" in entry) == ("match" in entry):
                raise ManifestError(f"{where}: provide exactly one of label or match")
            if "label" in entry:
                label = entry["label"]
                if not isinstance(label, str) or not SOURCE_LABEL_RE.match(label):
                    raise ManifestError(f"{where}: label must be a paper statement label")
                if label in seen_labels:
                    raise ManifestError(f"{where}: duplicate label {label}")
                seen_labels.add(label)
            elif not isinstance(entry["match"], str) or not entry["match"].strip():
                raise ManifestError(f"{where}: an unlabelled entry needs a unique text match")
            number = entry.get("number")
            if not isinstance(number, str) or not re.fullmatch(r"[A-Z0-9]+\.\d+", number):
                raise ManifestError(f"{where}: number must be the printed number, such as \"3.10\"")
        if status not in ALLOWED_STATUSES:
            raise ManifestError(f"{where}: status must be one of {sorted(ALLOWED_STATUSES)}")
        lean = _name_list(entry, "lean", where)
        library = _name_list(entry, "library", where)
        hypotheses = _name_list(entry, "hypotheses", where)
        if status in MAPPED_STATUSES and not lean:
            raise ManifestError(f"{where}: a formalized entry needs at least one Lean declaration")
        if status == "cited" and not hypotheses:
            raise ManifestError(
                f"{where}: a cited entry needs the Prop-valued definitions stating it"
            )
        if status == "intentionally_unformalized" and (lean or library or hypotheses):
            raise ManifestError(f"{where}: an intentionally unformalized entry must have no Lean names")
        if status in {"intentionally_unformalized", "partially_formalized"}:
            if not isinstance(entry.get("reason"), str) or not entry["reason"]:
                raise ManifestError(f"{where}: an unformalized or partially formalized entry needs a reason")
        if "headline" in entry and not isinstance(entry["headline"], bool):
            raise ManifestError(f"{where}: headline must be true or false")
        if library and not entry.get("headline"):
            raise ManifestError(f"{where}: only headline entries carry library declarations")
        relation = entry.get("relation")
        if relation is not None and relation not in ALLOWED_RELATIONS:
            raise ManifestError(f"{where}: relation must be one of {sorted(ALLOWED_RELATIONS)}")
        if status in MAPPED_STATUSES and relation is None:
            raise ManifestError(f"{where}: a formalized entry needs a relation")
    return manuscript_files, entries


# ---------------------------------------------------------------------------------------------
# The manuscript.


def strip_tex_comments(text: str) -> str:
    lines: list[str] = []
    for line in text.splitlines(keepends=True):
        body = line.rstrip("\r\n")
        cut = len(body)
        for index, char in enumerate(body):
            if char == "%" and (index == 0 or body[index - 1] != "\\"):
                cut = index
                break
        ending = "\n" if line.endswith(("\n", "\r")) else ""
        lines.append(body[:cut] + ending)
    return "".join(lines)


def source_fingerprint(text: str) -> str:
    """Hash TeX tokens, ignoring comments and layout whitespace, but retaining word boundaries."""
    tokens = re.findall(r"\\[A-Za-z@]+|\\.|[A-Za-z0-9]+|[^\s]", strip_tex_comments(text))
    return hashlib.sha256("\x1f".join(tokens).encode("utf-8")).hexdigest()


def normalized_text(text: str) -> str:
    return " ".join(strip_tex_comments(text).split())


def _appendix_letter(index: int) -> str:
    letters = ""
    while index > 0:
        index, rem = divmod(index - 1, 26)
        letters = chr(ord("A") + rem) + letters
    return letters


def scan_paper_file(path: Path) -> tuple[list[PaperDeclaration], list[str]]:
    """Return the numbered statements of a manuscript file with their printed numbers.

    The theorem counter is shared by every numbered environment and reset by every numbered
    `\\section`; after `\\appendix` the sections are lettered. Only the document body is
    scanned. The second component lists numbered environments that the preamble declares and
    the body uses but that this script does not know.
    """

    text = strip_tex_comments(path.read_text(encoding="utf-8"))
    body_start = text.find(r"\begin{document}")
    preamble = text[: body_start if body_start >= 0 else 0]
    body_offset = body_start if body_start >= 0 else 0
    unknown: list[str] = []
    for name in NEWTHEOREM_RE.findall(preamble):
        if name not in NUMBERED_ENVIRONMENTS and re.search(r"\\begin\{" + name + r"\}", text[body_offset:]):
            unknown.append(name)

    declarations: list[PaperDeclaration] = []
    section = 0
    appendix = False
    counter = 0
    for match in NUMBERING_RE.finditer(text, body_offset):
        token = match.group(0)
        if token.startswith(r"\section*"):
            continue
        if token.startswith(r"\section"):
            section += 1
            counter = 0
            continue
        if token.startswith(r"\appendix"):
            appendix = True
            section = 0
            counter = 0
            continue
        kind = match.group(1)
        counter += 1
        prefix = _appendix_letter(section) if appendix else str(section)
        end = re.search(rf"\\end\{{{kind}\}}", text[match.end() :])
        line = text.count("\n", 0, match.start()) + 1
        if end is None:
            raise ManifestError(f"{path}:{line}: missing \\end{{{kind}}}")
        labels = LABEL_RE.findall(text[match.end() : match.end() + end.start()])
        if len(labels) > 1:
            raise ManifestError(f"{path}:{line}: {kind} environment has multiple primary labels: {labels}")
        statement = text[match.start() : match.end() + end.end()]
        declarations.append(
            PaperDeclaration(labels[0] if labels else None, kind, f"{prefix}.{counter}", path, line, statement)
        )
    return declarations, unknown


def prose_span(text: str, start: str, end: str) -> str:
    text, start, end = map(normalized_text, (text, start, end))
    for name, anchor in (("start", start), ("end", end)):
        count = text.count(anchor)
        if count != 1:
            raise ManifestError(f"the {name} anchor occurs {count} times; it must occur exactly once")
    first = text.index(start)
    last = text.index(end)
    if last < first:
        raise ManifestError("the end anchor precedes the start anchor")
    return text[first : last + len(end)]


def check_paper_coverage(
    repo_root: Path,
    manuscript_files: list[str],
    entries: list[dict[str, Any]],
    snapshots: dict[str, str],
    fingerprints: dict[str, str],
) -> tuple[list[str], list[PaperDeclaration]]:
    """Check the manifest against the manuscript; record every current fingerprint."""

    errors: list[str] = []
    declarations: list[PaperDeclaration] = []
    texts: dict[str, str] = {}
    for relative in manuscript_files:
        path = repo_root / relative
        try:
            texts[relative] = path.read_text(encoding="utf-8")
            found, unknown = scan_paper_file(path)
        except (OSError, ManifestError) as exc:
            errors.append(str(exc))
            continue
        declarations.extend(found)
        for name in unknown:
            errors.append(
                f"{relative}: the numbered environment {name!r} is used but unknown to this script; "
                "add it to NUMBERED_ENVIRONMENTS"
            )
        current = source_fingerprint(texts[relative])
        fingerprints[f"manuscript:{relative}"] = current
        if current != snapshots[relative]:
            errors.append(
                f"{relative}: manuscript content changed; review the correspondence, including "
                "unmapped prose and proofs, before updating manuscript_sha256"
            )

    covered: set[tuple[Path, int]] = set()
    for entry in entries:
        source = entry["source"]
        if entry["kind"] == "prose":
            if entry["file"] not in texts:
                continue
            try:
                body = prose_span(texts[entry["file"]], entry["start"], entry["end"])
            except ManifestError as exc:
                errors.append(f"{source}: {exc}")
                continue
        else:
            if "match" in entry:
                candidates = [
                    d
                    for d in declarations
                    if d.label is None
                    and d.kind == entry["kind"]
                    and normalized_text(entry["match"]) in normalized_text(d.text)
                ]
            else:
                candidates = [d for d in declarations if d.label == entry["label"]]
            if len(candidates) != 1:
                errors.append(f"{source}: expected exactly one matching statement, found {len(candidates)}")
                continue
            declaration = candidates[0]
            key = (declaration.file, declaration.line)
            if key in covered:
                errors.append(f"{source}: statement already covered by another entry")
            covered.add(key)
            if declaration.kind != entry["kind"]:
                errors.append(
                    f"{source}: manifest kind {entry['kind']!r} does not match the environment "
                    f"{declaration.kind!r} at {declaration.file.name}:{declaration.line}"
                )
            if declaration.number != entry["number"]:
                errors.append(
                    f"{source}: manifest number {entry['number']} differs from the printed number "
                    f"{declaration.number}; renumber the manifest, docs/correspondence.md and the "
                    "Lean doc comments"
                )
            body = declaration.text
        current = source_fingerprint(body)
        fingerprints[source] = current
        if current != entry["sha256"]:
            errors.append(f"{source}: content changed; review its Lean correspondence before updating sha256")

    for d in declarations:
        if (d.file, d.line) not in covered:
            what = d.label or f"unlabelled {d.kind}"
            errors.append(f"{d.file.name}:{d.line}: {d.kind} {d.number} ({what}) is missing from the manifest")
    return errors, declarations


# ---------------------------------------------------------------------------------------------
# The Lean sources.


def strip_lean_comments(text: str) -> str:
    """Remove line and nested block comments while preserving line boundaries."""

    out: list[str] = []
    index = 0
    block_depth = 0
    in_string = False
    while index < len(text):
        pair = text[index : index + 2]
        char = text[index]
        if block_depth:
            if pair == "/-":
                block_depth += 1
                out.extend("  ")
                index += 2
            elif pair == "-/":
                block_depth -= 1
                out.extend("  ")
                index += 2
            else:
                out.append("\n" if char == "\n" else " ")
                index += 1
            continue
        if not in_string and pair == "/-":
            block_depth = 1
            out.extend("  ")
            index += 2
            continue
        if not in_string and pair == "--":
            while index < len(text) and text[index] != "\n":
                out.append(" ")
                index += 1
            continue
        if char == '"' and (index == 0 or text[index - 1] != "\\"):
            in_string = not in_string
        out.append(char)
        index += 1
    return "".join(out)


def scan_lean_file(path: Path) -> list[LeanDeclaration]:
    """Return the declarations of a Lean file, each with its comment-free source span.

    A span runs from the declaration to the next declaration or scope command. A module-level
    ``public section`` is never closed and so opens no scope.
    """

    lines = strip_lean_comments(path.read_text(encoding="utf-8")).splitlines()
    scopes: list[tuple[str, list[str]]] = []
    found: list[tuple[str, str, int]] = []
    boundaries: list[int] = []
    for line_no, line in enumerate(lines, 1):
        namespace_match = re.match(r"^\s*namespace\s+([^\s]+)\s*$", line)
        if namespace_match:
            scopes.append(("namespace", namespace_match.group(1).split(".")))
            boundaries.append(line_no)
            continue
        if re.match(r"^\s*(?:noncomputable\s+)?section(?:\s+[^\s]+)?\s*$", line):
            scopes.append(("section", []))
            boundaries.append(line_no)
            continue
        if re.match(r"^\s*mutual\s*$", line):
            scopes.append(("mutual", []))
            boundaries.append(line_no)
            continue
        if re.match(r"^\s*end(?:\s+[^\s]+)?\s*$", line):
            if scopes:
                scopes.pop()
            boundaries.append(line_no)
            continue

        match = DECL_RE.match(line)
        if not match:
            continue
        kind, raw_name = match.groups()
        namespace = [piece for scope, parts in scopes if scope == "namespace" for piece in parts]
        if raw_name.startswith("_root_."):
            name = raw_name.removeprefix("_root_.")
        else:
            name = ".".join(namespace + [raw_name])
        found.append((name, kind, line_no))
        boundaries.append(line_no)

    declarations: list[LeanDeclaration] = []
    for name, kind, line_no in found:
        following = [boundary for boundary in boundaries if boundary > line_no]
        end = following[0] - 1 if following else len(lines)
        span = "\n".join(lines[line_no - 1 : end])
        declarations.append(LeanDeclaration(name, kind, path, line_no, span))
    return declarations


def is_prop_definition(declaration: LeanDeclaration) -> bool:
    return declaration.kind in {"def", "abbrev"} and re.search(
        r":\s*Prop\s*:=", declaration.span
    ) is not None


# ---------------------------------------------------------------------------------------------
# Fingerprint maintenance.


def write_fingerprints(manifest_path: Path, entries: list[dict[str, Any]], fingerprints: dict[str, str]) -> int:
    """Rewrite the sha256 lines of the manifest in place; return the number of lines changed."""

    lines = manifest_path.read_text(encoding="utf-8").splitlines(keepends=True)
    changed = 0
    current_source: str | None = None
    for index, line in enumerate(lines):
        stripped = line.strip()
        if stripped.startswith("- source:"):
            _, value = _key_value(stripped[2:], manifest_path, index + 1)
            current_source = value
            continue
        if line.startswith("manuscript_sha256:"):
            prefix, _ = line.split(":", 1)
            digests = {
                key.removeprefix("manuscript:"): value
                for key, value in fingerprints.items()
                if key.startswith("manuscript:")
            }
            new_line = f"{prefix}: {json.dumps(digests)}\n"
            if new_line != line:
                lines[index] = new_line
                changed += 1
            continue
        if current_source is not None and stripped.startswith("sha256:"):
            digest = fingerprints.get(current_source)
            if digest is None:
                continue
            indent = line[: len(line) - len(line.lstrip())]
            new_line = f'{indent}sha256: "{digest}"\n'
            if new_line != line:
                lines[index] = new_line
                changed += 1
    manifest_path.write_text("".join(lines), encoding="utf-8")
    return changed


# ---------------------------------------------------------------------------------------------


def main() -> int:
    script = Path(__file__).resolve()
    default_lean_root = script.parent.parent
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument(
        "--manifest",
        type=Path,
        default=default_lean_root / "paper-correspondence.yaml",
        help="paper correspondence manifest (default: lean/paper-correspondence.yaml)",
    )
    parser.add_argument(
        "--lean-root",
        type=Path,
        default=default_lean_root,
        help="Lean project root (default: inferred from this script)",
    )
    parser.add_argument(
        "--print-fingerprints",
        action="store_true",
        help="print the current fingerprint of every entry and manuscript file",
    )
    parser.add_argument(
        "--write-fingerprints",
        action="store_true",
        help="record the current fingerprints in the manifest; only after reviewing the changes",
    )
    parser.add_argument(
        "--allow-incomplete", action="store_true",
        help="check correspondence metadata while reporting known proof gaps as warnings",
    )
    args = parser.parse_args()
    manifest_path = args.manifest.resolve()
    lean_root = args.lean_root.resolve()
    repo_root = lean_root.parent

    errors: list[str] = []
    warnings: list[str] = []
    try:
        data = load_manifest(manifest_path)
        manuscript_files, entries = validate_manifest(data, manifest_path)
    except (OSError, ManifestError) as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 2

    # The manuscript.
    fingerprints: dict[str, str] = {}
    coverage_errors, paper_declarations = check_paper_coverage(
        repo_root, manuscript_files, entries, data["manuscript_sha256"], fingerprints
    )
    errors.extend(coverage_errors)
    labelled = [d for d in paper_declarations if d.label is not None]
    unlabelled = [d for d in paper_declarations if d.label is None]

    revision = data.get("manuscript_revision")
    if revision:
        try:
            head = subprocess.run(
                ["git", "-C", str(repo_root), "rev-parse", "HEAD"],
                capture_output=True,
                text=True,
                check=True,
            ).stdout.strip()
            if head != revision:
                warnings.append(
                    f"the manuscript repository is at {head[:12]}, the manifest was reviewed at "
                    f"{revision[:12]}; the fingerprints decide whether the statements changed"
                )
        except (OSError, subprocess.CalledProcessError):
            warnings.append("cannot read the manuscript repository's HEAD; manuscript_revision not compared")

    if args.print_fingerprints or args.write_fingerprints:
        stale = {
            source: digest
            for source, digest in fingerprints.items()
            if digest
            != (
                data["manuscript_sha256"].get(source.removeprefix("manuscript:"))
                if source.startswith("manuscript:")
                else next(entry["sha256"] for entry in entries if entry["source"] == source)
            )
        }
        for source, digest in sorted(fingerprints.items()):
            marker = " (changed)" if source in stale else ""
            print(f"{source}: {digest}{marker}")
        if args.write_fingerprints:
            changed = write_fingerprints(manifest_path, entries, fingerprints)
            print(f"Recorded {changed} fingerprint(s) in {manifest_path.name}.")
            return 0

    # The Lean sources.
    lean_declarations: dict[str, list[LeanDeclaration]] = {}
    library_sorries = 0
    library_axioms: list[LeanDeclaration] = []
    challenge_path = lean_root / "Challenge.lean"
    for path in sorted(lean_root.rglob("*.lean")):
        relative_parts = path.relative_to(lean_root).parts
        if EXCLUDED_DIRECTORIES & set(relative_parts):
            continue
        for declaration in scan_lean_file(path):
            lean_declarations.setdefault(declaration.name, []).append(declaration)
            if declaration.kind == "axiom":
                library_axioms.append(declaration)
        if path != challenge_path:
            stripped = strip_lean_comments(path.read_text(encoding="utf-8"))
            library_sorries += len(re.findall(r"\bsorry\b", stripped))
    if library_axioms:
        errors.append(
            "the Lean sources declare axioms: "
            + ", ".join(f"{d.name} ({d.file.relative_to(lean_root)}:{d.line})" for d in library_axioms)
        )

    for key in ("lean", "library", "hypotheses"):
        names = {name for entry in entries for name in entry[key]}
        for name in sorted(names):
            if name not in lean_declarations:
                errors.append(f"mapped Lean name ({key}) is not found as a source declaration: {name}")
    hypothesis_names = {name for entry in entries for name in entry["hypotheses"]}
    for name in sorted(hypothesis_names & set(lean_declarations)):
        if not any(is_prop_definition(declaration) for declaration in lean_declarations[name]):
            errors.append(f"literature hypothesis {name} is not a Prop-valued definition")

    # The comparator configuration.
    comparator_path = lean_root / "comparator-config.json"
    comparator: dict[str, Any] = {}
    try:
        comparator = json.loads(comparator_path.read_text(encoding="utf-8"))
        comparator_names = comparator["theorem_names"]
    except (OSError, json.JSONDecodeError, KeyError) as exc:
        errors.append(f"cannot read comparator theorem names from {comparator_path}: {exc}")
        comparator_names = []
    if not isinstance(comparator_names, list) or not all(isinstance(name, str) for name in comparator_names):
        errors.append("comparator theorem_names must be a list of strings")
        comparator_names = []
    endpoint_count = len(comparator_names)
    if endpoint_count == 0:
        errors.append("comparator theorem_names lists no audited theorem")
    if len(set(comparator_names)) != endpoint_count:
        errors.append("comparator theorem_names contains duplicates")
    if comparator.get("definition_names") != []:
        errors.append("comparator definition_names must be the empty list")
    permitted_axioms = comparator.get("permitted_axioms")
    if not isinstance(permitted_axioms, list) or not set(permitted_axioms) <= STANDARD_AXIOMS:
        errors.append(
            "comparator permitted_axioms must be a list drawn from " + ", ".join(sorted(STANDARD_AXIOMS))
        )
        permitted_axioms = []
    comparator_set = set(comparator_names)
    manifest_headlines = {
        name
        for entry in entries
        if entry.get("headline") and entry["status"] in MAPPED_STATUSES
        for name in entry["lean"]
    }
    if manifest_headlines != comparator_set:
        errors.append(
            "manifest headline declarations differ from comparator theorem_names; "
            f"only in manifest={sorted(manifest_headlines - comparator_set)}, "
            f"only in comparator={sorted(comparator_set - manifest_headlines)}"
        )

    # The challenge and solution modules.
    solution_path = lean_root / "Solution.lean"
    for role, path in (("Challenge", challenge_path), ("Solution", solution_path)):
        if not path.is_file():
            errors.append(f"{role} module is missing: {path.relative_to(lean_root)}")
            continue
        declarations = scan_lean_file(path)
        endpoints = {
            d.name: d for d in declarations if d.kind in {"theorem", "lemma"} and d.name in comparator_set
        }
        names = set(endpoints)
        if names != comparator_set:
            missing = comparator_set - names
            recorded_open = {
                name for entry in entries if entry.get("headline")
                and entry["status"] == "partially_formalized" for name in entry["lean"]
            }
            message = (
                f"{role} lacks required headline proofs: {sorted(missing)}; "
                "a restricted theorem does not discharge the full Challenge statement"
            )
            if role == "Solution" and args.allow_incomplete and missing <= recorded_open:
                warnings.append(message)
            else:
                errors.append(message)
        if role == "Challenge":
            propositions = {d.name for d in declarations if d.kind in {"theorem", "lemma"}}
            if propositions != comparator_set:
                errors.append(
                    f"every theorem or lemma in Challenge.lean must be one of the {endpoint_count} "
                    f"audited endpoints; extra={sorted(propositions - comparator_set)}, "
                    f"missing={sorted(comparator_set - propositions)}"
                )
            axioms = [d.name for d in declarations if d.kind == "axiom"]
            if axioms:
                errors.append("Challenge.lean must not declare axioms: " + ", ".join(axioms))
            for name, declaration in sorted(endpoints.items()):
                if not re.search(r"\bsorry\b", declaration.span):
                    errors.append(f"{name} in Challenge.lean is not a theorem hole containing sorry")
        else:
            for name, declaration in sorted(endpoints.items()):
                if re.search(r"\bsorry\b", declaration.span):
                    errors.append(f"Solution proof {name} contains sorry")
                if not re.search(r":=\s*by\b", declaration.span):
                    warnings.append(f"Solution proof {name} does not have an explicit ':= by' body")

    # formalization.yaml against the comparator and the sources.
    formalization_path = lean_root / "formalization.yaml"
    try:
        formalization_text = formalization_path.read_text(encoding="utf-8")
        namespaces = {name.rsplit(".", 1)[0] for name in comparator_names if "." in name}
        alignment_names = {
            name
            for name in re.findall(r'^\s+lean:\s*["\']([^"\']+)["\']\s*$', formalization_text, re.M)
            if name.rsplit(".", 1)[0] in namespaces
        }
        if alignment_names != comparator_set:
            errors.append(
                "formalization.yaml alignment differs from comparator theorem_names; "
                f"only in alignment={sorted(alignment_names - comparator_set)}, "
                f"only in comparator={sorted(comparator_set - alignment_names)}"
            )
        axioms_match = re.search(r"^  axioms:\s*(\[.*\])\s*$", formalization_text, re.M)
        if axioms_match is None:
            errors.append("formalization.yaml has no one-line status axioms list")
        elif set(json.loads(axioms_match.group(1))) != set(permitted_axioms):
            errors.append("formalization.yaml status axioms differ from comparator permitted_axioms")
        sorry_match = re.search(r"^  sorry_count:\s*(\d+)\s*$", formalization_text, re.M)
        if sorry_match is None:
            errors.append("formalization.yaml has no status sorry_count")
        elif int(sorry_match.group(1)) != library_sorries:
            errors.append(
                f"formalization.yaml sorry_count is {sorry_match.group(1)}, but the Lean sources "
                f"outside Challenge.lean contain {library_sorries} sorry"
            )
        for value in re.findall(r'^\s+comparator_config:\s*["\']([^"\']+)["\']\s*$', formalization_text, re.M):
            if value != comparator_path.name:
                errors.append(f"formalization.yaml names the comparator configuration {value!r}; it is {comparator_path.name}")
    except (OSError, json.JSONDecodeError) as exc:
        errors.append(f"cannot read {formalization_path}: {exc}")

    # docs/correspondence.md must assess every numbered statement and name every endpoint.
    correspondence_path = lean_root / "docs" / "correspondence.md"
    try:
        correspondence_text = correspondence_path.read_text(encoding="utf-8")
        for entry in entries:
            if entry["kind"] == "prose":
                continue
            key = entry.get("label") or entry["source"]
            if key not in correspondence_text:
                errors.append(f"docs/correspondence.md does not mention the numbered statement {key}")
        for name in sorted(comparator_set):
            if name.rsplit(".", 1)[-1] not in correspondence_text:
                errors.append(f"docs/correspondence.md does not mention the audited endpoint {name}")
    except OSError as exc:
        errors.append(f"cannot read {correspondence_path}: {exc}")

    incomplete = [entry for entry in entries if entry["kind"] not in {"prose", "question"}
                  and entry["status"] in {"partially_formalized", "intentionally_unformalized"}]
    for entry in incomplete:
        message = f"INCOMPLETE {entry['number']} ({entry.get('label')}): {entry['reason']}"
        (warnings if args.allow_incomplete else errors).append(message)

    counts = {status: sum(entry["status"] == status for entry in entries) for status in sorted(ALLOWED_STATUSES)}
    prose_entries = [entry for entry in entries if entry["kind"] == "prose"]
    print(
        "STATIC CHECK ONLY: declarations are found by scanning source text; the script does not "
        "elaborate Lean or compile LaTeX, and agreement of fingerprints is not mathematical equivalence."
    )
    print(
        f"Scanned {len(labelled)} labelled and {len(unlabelled)} unlabelled numbered statements, "
        f"{len(prose_entries)} fingerprinted prose spans, {len(hypothesis_names)} literature "
        f"hypotheses and {len(lean_declarations)} distinct Lean source declarations. Manifest status: "
        + ", ".join(f"{count} {status}" for status, count in counts.items() if count)
        + f"; {endpoint_count} audited endpoint(s)."
    )
    for warning in warnings:
        print(f"WARNING: {warning}", file=sys.stderr)
    for error in errors:
        print(f"ERROR: {error}", file=sys.stderr)
    if errors:
        print(f"FAILED with {len(errors)} error(s).", file=sys.stderr)
        return 1
    print(
        f"OK: every numbered statement has one entry with its printed number and an unchanged "
        f"fingerprint and every mapped Lean name exists. The {endpoint_count} required headline "
        "statements and any explicitly recorded missing Solution proofs are accounted for. "
        "This is metadata consistency, not complete mathematical formalisation."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
