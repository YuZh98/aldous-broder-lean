# aldous-broder-lean

[![CI](https://github.com/YuZh98/aldous-broder-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/YuZh98/aldous-broder-lean/actions/workflows/ci.yml)

Lean 4 proofs of the order-mass identity, the Aldous–Broder tree law, and
the stopped covering-walk forest law. The development uses mathlib and
contains no unfinished proofs.

Companion paper: Hugh Zheng, *The Order Mass Identity of Rooted Forests,
with a Direct Proof of the Extended Aldous–Broder Theorem*
(unpublished manuscript, 7 October 2026).

## Results

- **Order-mass identity:** zero-row-sum matrices over any field, with a
  nonempty proper root set and nonzero principal minors on proper
  growth-order bases.
- **Aldous–Broder:** finite irreducible chains started at a fixed state;
  reversibility and two-way support are not required.
- **Stopped forest law:** the first-entrance forest obtained when all
  nonroots have been visited, including the completion identity for
  forests of zero weight.

The chain results assume at least two states. See the
[formalization reference](docs/formalization.md) for theorem names,
the paper correspondence, and scope qualifications.

The general directed Aldous–Broder theorem is due to
[Hu, Lyons and Tang (2021), Theorem 3.4](https://doi.org/10.1214/20-AIHP1101).
This project follows the manuscript's proof through the order-mass identity.

## Verify

Requires [elan](https://github.com/leanprover/elan), git, and Python 3.9+.
Lean and mathlib are pinned to `v4.30.0`; dependency revisions are recorded
in [lake-manifest.json](lake-manifest.json). Python scripts use only the
standard library.

```sh
git clone https://github.com/YuZh98/aldous-broder-lean.git
cd aldous-broder-lean
lake exe cache get
lake build
python3 scripts/check_proofs.py
python3 scripts/check_axioms.py
python3 -m unittest discover -s scripts/tests -v
```

CI runs the build, source scan, axiom audit, and script regression tests.
The scan rejects unfinished proofs and missing or unreadable inputs. The
audit requires every theorem in its fixed inventory and permits only `propext`,
`Classical.choice`, and `Quot.sound`.

## Read

| Resource | Contents |
|---|---|
| [Formalization reference](docs/formalization.md) | Paper map, modeling choices, and omitted results |
| [Blueprint PDF](blueprint/blueprint.pdf) · [LaTeX source](blueprint/blueprint.tex) | Definitions and proofs |
| [Lean sources](EAB/Paper/) | Proof modules; imported by [EAB.lean](EAB.lean) |
| [Change notes](CHANGELOG.md) | Brief notes for releases |
| [Contributing](CONTRIBUTING.md) | Verification and documentation updates |

## Cite

Use [CITATION.cff](CITATION.cff) or GitHub's “Cite this repository” button.
Until a tagged release is available, include the commit hash you used.

Licensed under [Apache 2.0](LICENSE).
