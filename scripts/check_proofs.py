#!/usr/bin/env python3
"""Reject unfinished proofs, failing if required source inputs are absent."""

from pathlib import Path
import os
import re
import sys

ROOT = Path(__file__).resolve().parent.parent
UNFINISHED = re.compile(r"\b(?:sorry|admit)\b")


def check_sources(root):
    root = Path(root)
    source_dir = root / "EAB"
    if not source_dir.is_dir():
        raise ValueError("required source directory EAB is missing")
    def fail_walk(error):
        raise error

    modules = []
    for directory, _, names in os.walk(source_dir, onerror=fail_walk):
        modules.extend(Path(directory) / name for name in names
                       if name.endswith(".lean"))
    modules.sort()
    if not modules:
        raise ValueError("no Lean modules found in EAB")
    paths = [root / "EAB.lean", root / "AxiomCheck.lean"] + modules
    failures = []
    for path in paths:
        # Missing, unreadable, or invalid UTF-8 files raise an exception;
        # none is interpreted as a successful empty scan.
        text = path.read_text(encoding="utf-8")
        for number, line in enumerate(text.splitlines(), 1):
            if UNFINISHED.search(line):
                failures.append(f"{path.relative_to(root)}:{number}")
    if failures:
        raise ValueError("unfinished proof markers in:\n" + "\n".join(failures))
    return len(paths)


def main():
    try:
        count = check_sources(ROOT)
    except (OSError, UnicodeError, ValueError) as error:
        print(f"Proof scan failed: {error}", file=sys.stderr)
        return 1
    print(f"OK: {count} Lean files contain no unfinished proof markers")
    return 0


if __name__ == "__main__":
    sys.exit(main())
