#!/usr/bin/env python3
"""Check the required theorem inventory and its kernel axiom dependencies."""

from collections import Counter
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
# Keep this inventory independent of AxiomCheck.lean so deleting an audit
# command cannot silently reduce the verification coverage.
EXPECTED = {
    "EAB.Paper.order_mass_identity",
    "EAB.Paper.Chain.aldous_broder",
    "EAB.Paper.Chain.aldous_broder_normalized",
    "EAB.Paper.Chain.stopped_forest_law",
    "EAB.Paper.Foundation.one_vertex_transfer",
    "EAB.Paper.Foundation.one_vertex_transfer_singleton",
    "EAB.Paper.single_root_normalization",
    "EAB.Paper.Chain.confined_det_pos",
    "EAB.Paper.Chain.IsStationary.cofactorVec_eq",
    "EAB.Paper.Chain.green_reversal",
    "EAB.Paper.Chain.chainLaw_cylinder",
    "EAB.Paper.Chain.chainLaw_prefix_inter_shift",
    "EAB.Paper.Chain.ae_hits_all",
    "EAB.Paper.Chain.chainLaw_orderEvent",
    "EAB.Paper.Chain.chainLaw_orderEvent_eq",
    "EAB.Paper.Chain.chainLaw_forestEvent_marginal",
}


def check_inventory(names):
    """Require exactly one occurrence of every intended audited theorem."""
    counts = Counter(names)
    missing = EXPECTED - counts.keys()
    unexpected = counts.keys() - EXPECTED
    duplicate = {name for name, count in counts.items() if count > 1}
    problems = []
    for label, values in [("missing", missing), ("unexpected", unexpected),
                          ("duplicate", duplicate)]:
        if values:
            problems.append(f"{label} theorems: {', '.join(sorted(values))}")
    if problems:
        raise ValueError("\n".join(problems))


def check_commands(source):
    names = re.findall(r"^\s*#print\s+axioms\s+(\S+)\s*$", source, re.M)
    check_inventory(names)


def check_reports(text):
    reports = re.findall(
        r"'([^']+)' depends on axioms: \[([^\]]*)\]", text, re.S
    )
    clean = re.findall(r"'([^']+)' does not depend on any axioms", text)
    check_inventory([name for name, _ in reports] + clean)
    bad = []
    for name, axioms in reports:
        used = {a.strip() for a in axioms.split(",") if a.strip()}
        if used - ALLOWED:
            bad.append(f"{name}: {sorted(used - ALLOWED)}")
    if bad:
        raise ValueError("unexpected axioms:\n" + "\n".join(bad))


def main():
    try:
        check_commands((ROOT / "AxiomCheck.lean").read_text(encoding="utf-8"))
        out = subprocess.run(
            ["lake", "env", "lean", "AxiomCheck.lean"], cwd=ROOT,
            capture_output=True, text=True, check=False,
        )
        text = out.stdout + out.stderr
        print(text, end="" if text.endswith("\n") else "\n")
        if out.returncode != 0:
            raise ValueError("AxiomCheck.lean failed to compile")
        check_reports(text)
    except (OSError, UnicodeError, ValueError) as error:
        print(f"Axiom audit failed: {error}", file=sys.stderr)
        return 1
    print(f"OK: {len(EXPECTED)} theorems use only {sorted(ALLOWED)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
