# aldous-broder-lean

[![CI](https://github.com/YuZh98/aldous-broder-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/YuZh98/aldous-broder-lean/actions/workflows/ci.yml)

A Lean 4 formalization of the main results of

> Hugh Zheng, *The Order Mass Identity of Rooted Forests, with a Direct
> Proof of the Extended Aldous–Broder Theorem* (unpublished manuscript,
> 7 October 2026).

It proves, with mathlib only and without `sorry`:

- **the order-mass identity**: for a matrix `L` with zero row sums over any
  field, a nonempty proper root set, and nonzero principal minors on the
  proper bases along the forest's growth orders, the sum of the order
  weights of the growth orders of a rooted forest entering at a root `r`
  equals the principal cofactor at `r` of
  `I - Γ^B M_f`, a matrix on the roots;
- **the Aldous–Broder theorem** for every finite irreducible Markov chain
  started at a fixed state, with no reversibility or two-way support
  assumption;
- **the law of the stopped covering walk**: the forest obtained by stopping
  once every nonroot vertex has been visited, with its completion weight.

The proofs follow those of the paper, as laid out in
[`blueprint/blueprint.pdf`](blueprint/blueprint.pdf); the docstrings cite the
blueprint's labels.

The general directed Aldous–Broder theorem is an existing result: see
Yiping Hu, Russell Lyons and Pengfei Tang, *A reverse Aldous–Broder
algorithm*, Annales de l'Institut Henri Poincaré, Probabilités et
Statistiques **57** (2021), 890–900,
[Theorem 3.4](https://doi.org/10.1214/20-AIHP1101). This project formalizes
the manuscript's proof through the order-mass identity.

## Paper-to-Lean correspondence

Paper numbers refer to the unpublished manuscript version of 7 October
2026. The blueprint is available in this repository and uses its own
numbering; the map below allows the formalization to be read alongside it.
All declarations are in the namespace `EAB.Paper`.

| Paper | Blueprint | Lean declaration |
|---|---|---|
| Definition 2.2, (2.2) | Definition 1.3, Lemma 1.4 | `Foundation.harmonic`, `Foundation.gamma`, `Foundation.harmonic_one` |
| Lemma 2.3 | Lemma 1.4 | `Foundation.harmonic_boundary`, `Foundation.harmonic_interior_row`, `Foundation.harmonic_unique` |
| (2.3) | Definition 1.3 | `Γ^U_{uv}` is `Foundation.gamma L U v u` for `u ∈ U` |
| Lemma 2.1 | Lemma 1.2 | `Foundation.adjugate_apply_eq_principalCofactor`, `Foundation.principalCofactor_left_kernel`, `Foundation.det_add_rank_one_zero_row_sum` |
| Definition 2.5, Lemma 2.6 | Definitions 3.1 and 3.3, Lemma 3.2 | `IsPaperParentMap`, `growthOrders`, `rootIndicator`, `rootBlock_pairwiseDisjoint`, `rootBlocks_cover`, `childDescendants_pairwise`, `childDescendants_cover` |
| (3.3), Definition 4.3 | Definition 3.3 | `orderWeight`, `orderMass` |
| Lemma 5.1 | Lemmas 2.5 and 2.6 | `Foundation.one_vertex_transfer`, `Foundation.one_vertex_transfer_singleton` |
| **Theorem 4.5** (order-mass identity) | Theorems 4.1 and 4.2 | **`order_mass_identity`**, `single_root_normalization` |
| Lemma 3.3 | Lemmas 5.2 and 5.4 | `Chain.reversedMatrix_mulVec_one`, `Chain.det_principal_reversedMatrix`, `Chain.det_principal_reversedMatrix_pos`, `Chain.green_hasSum`, `Chain.green_reversal`, `Chain.inv_diag_eq_det_ratio`, `Chain.inv_column_eq_gamma` |
| Lemma 3.4 | Lemma 5.3 | `Chain.cofactorVec_pos`, `Chain.isStationary_cofactor`, `Chain.IsStationary.cofactorVec_eq` |
| Proposition 3.2, growth-order formula (3.5) | Lemmas 5.6 and 5.7 | `Chain.chainLaw_orderEvent_eq` |
| **Theorem 6.1** (Aldous–Broder) | Theorem 6.2 | **`Chain.aldous_broder`**, **`Chain.aldous_broder_normalized`** |
| **Theorem 6.4** (stopped covering walk) | Theorem 7.3 | **`Chain.stopped_forest_law`** |

### Modeling choices

- The law of the chain started at `r` is mathlib's Ionescu-Tulcea trajectory
  measure (`Chain.chainLaw`), checked against the cylinder formula
  (`Chain.chainLaw_cylinder`); probabilities are extended nonnegative reals.
- The forest event requires the walk to visit every state, which has
  probability one (`Chain.ae_hits_all`), and its first-entrance parents to
  equal `f`; this is the event `{F_B = F_0}` up to a null set.
- The stationary distribution enters as a hypothesis that `π` is positive,
  normalized and invariant; `Chain.IsStationary.cofactorVec_eq` proves that
  such a `π` is the normalized cofactor vector, hence unique.
- The standing assumption `n ≥ 2` appears as `2 ≤ Fintype.card V`.
- Theorem 4.5 is stated over an arbitrary field. `Chain.stopped_forest_law`
  holds for every parent assignment, including those of weight zero.
- Lemma 2.6 is formalized for the children of roots, the case the proof uses;
  `Foundation.one_vertex_transfer` allows a fold along any weights summing to
  one, of which Lemma 5.1 is the fold into a single root.
- Proposition 3.2 is formalized for growth orders in its general form (3.5);
  `Chain.chainLaw_orderEvent_eq` also states that the real number on the
  right is nonnegative, so the probability equals it rather than its
  truncation at zero. The statement for incompatible orderings and the
  single-root simplification (3.6) are not stated separately as matching
  corollaries.
- `Chain.stopped_forest_law` states the law of Theorem 6.4 in the form
  `det L[B] w(F_0) g(B,f)ᵀ L[B]⁻¹ e_r / (π_r ∏_{v∉B} π_v · 1ᵀλ)` from the
  paper's proof, together with (6.3). Combined, they give the second
  expression of (6.2). Its first expression, a ratio of sums of tree weights,
  follows from `Chain.chainLaw_forestEvent_marginal` and
  `Chain.aldous_broder_normalized` but is not stated as one theorem.

### Completion-weight notation

`Chain.completionFactor L B f r` is the algebraic factor
`g(B,f)ᵀ L[B]⁻¹ e_r`. The blueprint calls this factor `φ_r(f)`.
The manuscript's completion weight `φ_r(F_0)` is instead the sum of the
added-edge weights over all tree completions. In Lean this sum is
`∑ h ∈ Chain.completions B r r.2 f, Chain.completionWeight P π B r h`.
The second conclusion of `Chain.stopped_forest_law` identifies it with
`det L[B] * (∏ j ∈ B \ {r}, π j) * Chain.completionFactor L B f r`,
where `L = Chain.reversedMatrix P π`.

### Not formalized

Theorem 6.2, Corollaries 4.9 and 6.6, the determinant formula (6.4) for the
completion weight, the worked examples of Appendix A, Appendices C and D of the
paper, and its numerical experiments.

## Verification

Requirements: [elan](https://github.com/leanprover/elan) (the toolchain
`leanprover/lean4:v4.30.0` is selected by `lean-toolchain`), git, and Python
3.9 or later. The verification scripts use only Python's standard library.
Mathlib is pinned to `v4.30.0`, commit
`c5ea00351c28e24afc9f0f84379aa41082b1188f`, in
`lake-manifest.json`.

```sh
git clone https://github.com/YuZh98/aldous-broder-lean.git
cd aldous-broder-lean
lake exe cache get              # download compiled mathlib
lake build                      # compile the development
python3 scripts/check_proofs.py # reject unfinished proofs
python3 scripts/check_axioms.py # axiom audit
python3 -m unittest discover -s scripts/tests -v # check the verification scripts
```

The audit runs `lake env lean AxiomCheck.lean` and fails unless each of the
16 listed theorems, the four endpoints and their principal proof obligations,
depends only on `propext`, `Classical.choice` and `Quot.sound`. Its required
inventory is checked independently of `AxiomCheck.lean`: missing, duplicate,
or unexpected theorem names are rejected. The unfinished-proof scan covers
all project Lean files, including `EAB.lean` and `AxiomCheck.lean`, and
fails on missing or unreadable inputs. Continuous integration runs these
checks and the script regression tests on every push and pull request.

## Layout

| Path | Contents |
|---|---|
| `EAB/Paper/` | the 21 Lean files |
| `EAB.lean` | imports all of them |
| `AxiomCheck.lean`, `scripts/check_axioms.py` | the axiom audit |
| `scripts/check_proofs.py`, `scripts/tests/` | the unfinished-proof scan and verification-script regression tests |
| `blueprint/` | the blueprint the proofs follow |

## Citation

See [`CITATION.cff`](CITATION.cff), or use GitHub's "Cite this repository"
button.

For reproducibility, cite a tagged release rather than the changing `main`
branch.

## License

[Apache License 2.0](LICENSE).
