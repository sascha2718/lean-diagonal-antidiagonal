#!/usr/bin/env python3
"""Check that every Challenge definition occurs in its headline type dependencies.

Lean supplies the dependency graph, including inductive constructors and definition
bodies. This checks redundancy in the chosen vocabulary, not mathematical fidelity.
"""

from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
from check_paper_correspondence import scan_lean_file


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    for command in (["lake", "build", "Challenge"],
                    ["lake", "env", "lean", "tools/AuditVocabulary.lean"]):
        result = subprocess.run(command, cwd=root, text=True, capture_output=True)
        if result.returncode:
            print(result.stdout + result.stderr, file=sys.stderr)
            return result.returncode
    needed = {line.removeprefix("NEEDED ") for line in result.stdout.splitlines()
              if line.startswith("NEEDED ")}
    definitions = [d.name for d in scan_lean_file(root / "Challenge.lean")
                   if d.kind in {"def", "abbrev", "structure", "inductive", "class"}]
    unused = sorted(set(definitions) - needed)
    if unused:
        print("Unused Challenge definitions: " + ", ".join(unused), file=sys.stderr)
        return 1
    print(f"PASS: all {len(definitions)} Challenge definitions are needed by the three "
          "headline types or their explicit hypothesis definitions.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
