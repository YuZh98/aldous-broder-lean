#!/usr/bin/env python3
"""Run AxiomCheck.lean and fail unless every audited theorem depends only on
the standard axioms propext, Classical.choice and Quot.sound."""
import re
import subprocess
import sys

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

out = subprocess.run(
    ["lake", "env", "lean", "AxiomCheck.lean"],
    capture_output=True, text=True,
)
text = out.stdout + out.stderr
print(text)
if out.returncode != 0:
    sys.exit("AxiomCheck.lean failed to compile")

expected = len(re.findall(r"^#print axioms", open("AxiomCheck.lean").read(), re.M))
reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text, re.S)
clean = re.findall(r"'([^']+)' does not depend on any axioms", text)
if len(reports) + len(clean) != expected:
    sys.exit(f"expected {expected} axiom reports, found {len(reports) + len(clean)}")

bad = []
for name, axioms in reports:
    used = {a.strip() for a in axioms.split(",") if a.strip()}
    if used - ALLOWED:
        bad.append(f"{name}: {sorted(used - ALLOWED)}")
if bad:
    sys.exit("unexpected axioms:\n" + "\n".join(bad))
print(f"OK: {expected} theorems use only {sorted(ALLOWED)}")
