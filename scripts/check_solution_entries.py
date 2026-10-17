#!/usr/bin/env python3
"""Check the Solution entry ledger and the human-facing Challenge statically.

Every currently numbered manuscript statement must have exactly one standalone
``-- PAPER_ENTRY <label>`` line in Solution.lean. Challenge.lean must contain only
the three headline theorem holes, with its definitions repeated verbatim (ignoring
comments and token whitespace) in Solution/Definitions.lean.

``--require-complete`` additionally rejects every non-question numbered entry whose
manifest status is not ``formalized`` or ``cited``. The latter status records a
conditional literature statement, not a proof of the cited theorem.

This is a source-convention checker, not a Lean parser or kernel check. It does not
establish that an entry proves its labelled statement, that a literature hypothesis
matches its source, or that definitions are minimal. Use the Lean build, comparator
and vocabulary dependency audit for their separate checks.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
from pathlib import Path
import re
import sys
from typing import Any

from check_paper_correspondence import (
    LeanDeclaration,
    ManifestError,
    PaperDeclaration,
    load_manifest,
    scan_lean_file,
    scan_paper_file,
    strip_lean_comments,
)


HEADLINES = {
    "Challenge.audit_main1",
    "Challenge.audit_main2",
    "Challenge.audit_main_extended",
}
DEFINITION_KINDS = {"def", "abbrev", "structure", "class", "inductive"}
TOKEN_RE = re.compile(r'"(?:\\.|[^"\\])*"|[^\W\d][\w\']*|[0-9]+|:=|=>|->|<-|[^\s]')
MARKER_RE = re.compile(r"PAPER_ENTRY\s+(\S+)\s*\Z")
CONTEXT_RE = re.compile(
    r"^(?:universe\b|variable\b|include\b|omit\b|open\b|set_option\b|attribute\b|"
    r"(?:local\s+|scoped\s+)?(?:notation|infix[lr]?|prefix|postfix)\b)"
)
LIMITATIONS = (
    "Static checks only: markers do not certify proofs; text equality does not establish "
    "Lean elaboration, mathematical equivalence, literature fidelity, or vocabulary minimality. "
    "Run the Lean build, comparator and separate vocabulary dependency audit."
)


def code_tokens(text: str) -> tuple[str, ...]:
    """Retain identifiers and string contents, ignoring comments and token whitespace."""
    return tuple(TOKEN_RE.findall(strip_lean_comments(text)))


def line_comments(text: str):
    """Yield real line comments with positions, excluding nested block comments/strings."""
    index = 0
    depth = 0
    line = 1
    line_start = 0
    while index < len(text):
        pair = text[index : index + 2]
        char = text[index]
        if char == "\n":
            line += 1
            line_start = index + 1
        if depth:
            if pair == "/-":
                depth += 1
                index += 2
            elif pair == "-/":
                depth -= 1
                index += 2
            else:
                index += 1
        elif pair == "/-":
            depth = 1
            index += 2
        elif pair == "--":
            end = text.find("\n", index)
            if end < 0:
                end = len(text)
            yield line, text[line_start:index], text[index + 2 : end].strip()
            index = end
        elif char == '"':
            index += 1
            while index < len(text):
                if text[index] == "\\":
                    index += 2
                elif text[index] == '"':
                    index += 1
                    break
                else:
                    if text[index] == "\n":
                        line += 1
                        line_start = index + 1
                    index += 1
        elif char == "'" and (match := re.match(r"'(?:\\.|[^'\\\n])'", text[index:])):
            index += len(match.group(0))
        else:
            index += 1


def check_markers(path: Path, paper: list[PaperDeclaration]) -> list[str]:
    errors: list[str] = []
    locations: dict[str, list[int]] = defaultdict(list)
    for line, prefix, comment in line_comments(path.read_text(encoding="utf-8")):
        if not re.match(r"PAPER_ENTRY\b", comment):
            continue
        match = MARKER_RE.fullmatch(comment)
        if prefix.strip() or match is None:
            errors.append(f"{path}:{line}: use a standalone -- PAPER_ENTRY <label> line")
        else:
            locations[match.group(1)].append(line)
    labels = {declaration.label for declaration in paper if declaration.label}
    for label in sorted(labels - locations.keys()):
        errors.append(f"{path}: missing PAPER_ENTRY {label}")
    for label, lines in sorted(locations.items()):
        if label not in labels:
            errors.append(f"{path}:{lines[0]}: extra PAPER_ENTRY {label}")
        if len(lines) != 1:
            errors.append(f"{path}: duplicate PAPER_ENTRY {label} at lines {lines}")
    return errors


def active_contexts(path: Path, declarations: list[LeanDeclaration]) -> dict[int, tuple]:
    """Capture active variable/universe/open commands for this repository's source style.

    This prevents an unchanged definition body from hiding a changed section variable.
    Context comparison is deliberately conservative: even an unused changed open command
    is reported. It is not an elaborated-type comparison.
    """
    lines = strip_lean_comments(path.read_text(encoding="utf-8")).splitlines()
    declaration_lines = {declaration.line for declaration in declarations}
    frames: list[list[tuple[str, ...]]] = [[]]
    pending: list[tuple[str, ...]] = []
    contexts: dict[int, tuple] = {}
    index = 0
    while index < len(lines):
        stripped = lines[index].strip()
        if index + 1 in declaration_lines:
            contexts[index + 1] = tuple(item for frame in frames for item in frame) + tuple(pending)
            pending.clear()
        elif re.fullmatch(r"(?:namespace|section)(?:\s+\S+)?|noncomputable\s+section(?:\s+\S+)?", stripped):
            frames.append([])
        elif re.fullmatch(r"end(?:\s+\S+)?", stripped):
            if len(frames) > 1:
                frames.pop()
        elif CONTEXT_RE.match(stripped):
            start = index
            indentation = len(lines[start]) - len(lines[start].lstrip())
            while index + 1 < len(lines):
                following = lines[index + 1]
                if following.strip() and len(following) - len(following.lstrip()) <= indentation:
                    break
                index += 1
            tokens = code_tokens("\n".join(lines[start : index + 1]))
            if tokens and tokens[-1] == "in":
                pending.append(tokens)
            else:
                frames[-1].append(tokens)
        index += 1
    return contexts


def proof_body(declaration: LeanDeclaration) -> tuple[tuple[str, ...], tuple[str, ...]]:
    """Split at the outer assignment, excluding default binder values and nested terms."""
    tokens = code_tokens(declaration.span)
    depth = 0
    for index, token in enumerate(tokens):
        if token in {"(", "[", "{", "⦃"}:
            depth += 1
        elif token in {")", "]", "}", "⦄"}:
            depth -= 1
        elif token == ":=" and depth == 0:
            return tokens[:index], tokens[index + 1 :]
    return tokens, ()


def check_challenge(challenge: Path, definitions: Path) -> tuple[list[str], int]:
    errors: list[str] = []
    text = challenge.read_text(encoding="utf-8")
    clean = strip_lean_comments(text)
    declarations = scan_lean_file(challenge)
    mirrors = scan_lean_file(definitions)
    by_name: dict[str, list[LeanDeclaration]] = defaultdict(list)
    for declaration in mirrors:
        by_name[declaration.name].append(declaration)
    challenge_context = active_contexts(challenge, declarations)
    mirror_context = active_contexts(definitions, mirrors)

    for line, source in enumerate(clean.splitlines(), 1):
        if match := re.match(r"^\s*(?:public\s+)?import\s+(.+)$", source):
            for module in match.group(1).split():
                if module != "Mathlib" and not module.startswith("Mathlib."):
                    errors.append(f"{challenge}:{line}: non-Mathlib import {module}")
        if re.match(r"^\s*(?:(?:private|protected|public|noncomputable|unsafe)\s+)*example\b", source):
            errors.append(f"{challenge}:{line}: example/proof commands do not belong in Challenge")

    statements = [d for d in declarations if d.kind in {"theorem", "lemma"}]
    counts = Counter(d.name for d in statements)
    for name in sorted(HEADLINES):
        if counts[name] != 1:
            errors.append(f"{challenge}: expected one theorem {name}, found {counts[name]}")
    for declaration in statements:
        if declaration.name not in HEADLINES or declaration.kind != "theorem":
            errors.append(f"{challenge}:{declaration.line}: unexpected {declaration.kind} {declaration.name}")
        signature, body = proof_body(declaration)
        if body not in {("sorry",), ("by", "sorry")} or "sorry" in signature:
            errors.append(f"{challenge}:{declaration.line}: {declaration.name} must have only := sorry or := by sorry")
    if code_tokens(clean).count("sorry") != 3:
        errors.append(f"{challenge}: expected exactly three sorry tokens, found {code_tokens(clean).count('sorry')}")

    seen: set[str] = set()
    compared = 0
    for declaration in declarations:
        if declaration.name in seen:
            errors.append(f"{challenge}:{declaration.line}: duplicate declaration {declaration.name}")
        seen.add(declaration.name)
        if declaration.kind in {"theorem", "lemma"}:
            continue
        if declaration.kind not in DEFINITION_KINDS:
            errors.append(f"{challenge}:{declaration.line}: unsupported statement declaration {declaration.kind} {declaration.name}")
            continue
        candidates = by_name[declaration.name]
        if len(candidates) != 1:
            errors.append(f"{definitions}: expected one matching definition {declaration.name}, found {len(candidates)}")
            continue
        mirror = candidates[0]
        compared += 1
        if declaration.kind != mirror.kind or code_tokens(declaration.span) != code_tokens(mirror.span):
            errors.append(f"{challenge}:{declaration.line}: definition {declaration.name} differs from {definitions}:{mirror.line}")
        if challenge_context.get(declaration.line) != mirror_context.get(mirror.line):
            errors.append(f"{challenge}:{declaration.line}: active declaration context for {declaration.name} differs from {definitions}:{mirror.line}")
        if "sorry" in code_tokens(declaration.span):
            errors.append(f"{challenge}:{declaration.line}: definition {declaration.name} contains a proof hole")
    return errors, compared


def check_complete(paper: list[PaperDeclaration], data: dict[str, Any], manifest: Path) -> list[str]:
    errors: list[str] = []
    entries = data.get("entries", [])
    if not isinstance(entries, list) or not all(isinstance(entry, dict) for entry in entries):
        return [f"{manifest}: entries must be a list of mappings"]
    for declaration in paper:
        matches = [entry for entry in entries if entry.get("label") == declaration.label]
        if len(matches) != 1:
            errors.append(f"{manifest}: expected one entry for {declaration.label}, found {len(matches)}")
            continue
        entry = matches[0]
        if entry.get("kind") != declaration.kind:
            errors.append(f"{manifest}: kind mismatch for {declaration.label}")
        if declaration.kind != "question" and entry.get("status") not in {"formalized", "cited"}:
            reason = entry.get("reason") or entry.get("note") or "no explanation recorded"
            errors.append(f"{manifest}: incomplete {declaration.number} {declaration.label}: {entry.get('status')!r}; {reason}")
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--lean-root", type=Path, default=Path(__file__).resolve().parent.parent)
    parser.add_argument("--manifest", type=Path, help="default: <lean-root>/paper-correspondence.yaml")
    parser.add_argument("--require-complete", action="store_true", help="fail partial/unformalised numbered results, excluding questions")
    args = parser.parse_args()
    root = args.lean_root.resolve()
    manifest = (args.manifest or root / "paper-correspondence.yaml").resolve()
    errors: list[str] = []
    paper: list[PaperDeclaration] = []
    compared = 0
    try:
        data = load_manifest(manifest)
        files = data.get("manuscript_files")
        if not isinstance(files, list) or not files or not all(isinstance(file, str) for file in files):
            raise ManifestError(f"{manifest}: manuscript_files must be a nonempty string list")
        for relative in files:
            found, unknown = scan_paper_file(root.parent / relative)
            paper.extend(found)
            if unknown:
                errors.append(f"{relative}: unsupported numbered environments {unknown}")
        if not paper:
            errors.append("No numbered manuscript statements were found")
        label_counts = Counter(declaration.label for declaration in paper)
        for declaration in paper:
            if declaration.label is None:
                errors.append(f"{declaration.file}:{declaration.line}: numbered {declaration.kind} {declaration.number} has no label")
        for label, count in label_counts.items():
            if label is not None and count != 1:
                errors.append(f"Manuscript label {label} occurs {count} times")
        errors.extend(check_markers(root / "Solution.lean", paper))
        challenge_errors, compared = check_challenge(root / "Challenge.lean", root / "Solution/Definitions.lean")
        errors.extend(challenge_errors)
        if args.require_complete:
            errors.extend(check_complete(paper, data, manifest))
    except (OSError, ManifestError) as exc:
        errors.append(str(exc))
    print(f"Checked {len(paper)} numbered manuscript entries and {compared} Challenge definitions.")
    print(LIMITATIONS)
    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        print(f"FAILED: {len(errors)} static consistency issue(s).", file=sys.stderr)
        return 1
    mode = " with complete-status enforcement" if args.require_complete else " (coverage statuses not enforced)"
    print(f"PASS: entry markers, Challenge shape and definition consistency{mode}.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
