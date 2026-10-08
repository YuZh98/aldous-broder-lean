# aldous-broder-lean

[![CI](https://github.com/YuZh98/aldous-broder-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/YuZh98/aldous-broder-lean/actions/workflows/ci.yml)

A Lean 4 formalization of the main results of

> Hugh Zheng, *The Order Mass Identity of Rooted Forests, with a Direct
> Proof of the Extended Aldous–Broder Theorem* (arXiv link to be added).

It proves, with mathlib only and without `sorry`:

- **the order-mass identity**: for a matrix `L` with zero row sums over any
  field, the sum of the order weights of the growth orders of a rooted
  forest entering at a root `r` equals the principal cofactor at `r` of
  `I - Γ^B M_f`, a matrix on the roots;
- **the Aldous–Broder theorem** for every finite irreducible Markov chain
  started at a fixed state, with no reversibility or two-way support
  assumption;
- **the law of the stopped covering walk**: the forest obtained by stopping
  once every nonroot vertex has been visited, with its completion weight.

The proofs follow those of the paper, as laid out in
[`blueprint/blueprint.pdf`](blueprint/blueprint.pdf); the docstrings cite the
blueprint's labels.

## Paper-to-Lean correspondence

Numbers refer to the manuscript version of 7 October 2026. All declarations
are in the namespace `EAB.Paper`.

| Paper | Lean declaration |
|---|---|
| Definition 2.2, (2.2) | `Foundation.harmonic`, `Foundation.gamma`, `Foundation.harmonic_unique`, `Foundation.harmonic_one` |
| (2.3) | `Γ^U_{uv}` is `Foundation.gamma L U v u` for `u ∈ U` |
| Lemma 2.1 | `Foundation.adjugate_apply_eq_principalCofactor`, `Foundation.principalCofactor_left_kernel`, `Foundation.det_add_rank_one_zero_row_sum` |
| Definition 2.5, Lemma 2.6 | `IsPaperParentMap`, `growthOrders`, `rootIndicator`, `rootBlock_pairwiseDisjoint`, `rootBlocks_cover`, `childDescendants_cover` |
| (3.3), Definition 4.3 | `orderWeight`, `orderMass` |
| Lemma 5.1 | `Foundation.one_vertex_transfer`, `Foundation.one_vertex_transfer_singleton` |
| **Theorem 4.5** (order-mass identity) | **`order_mass_identity`**, `single_root_normalization` |
| Lemma 3.3 | `Chain.det_principal_reversedMatrix_pos`, `Chain.green_hasSum`, `Chain.green_reversal`, `Chain.inv_diag_eq_det_ratio`, `Chain.inv_column_eq_gamma` |
| Lemma 3.4 | `Chain.isStationary_cofactor`, `Chain.IsStationary.cofactorVec_eq` |
| Proposition 3.2 | `Chain.chainLaw_orderEvent_eq` |
| **Theorem 6.1** (Aldous–Broder) | **`Chain.aldous_broder`**, **`Chain.aldous_broder_normalized`** |
| **Theorem 6.4** (stopped covering walk) | **`Chain.stopped_forest_law`** |

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
- Proposition 3.2 is formalized for growth orders in its general form (3.5).

### Not formalized

Theorem 6.2, Corollaries 4.9 and 6.6, Appendices C and D of the paper, and its
numerical experiments.

## Verification

Requirements: [elan](https://github.com/leanprover/elan) (the toolchain
`leanprover/lean4:v4.30.0` is selected by `lean-toolchain`) and git. Mathlib is
pinned to `v4.30.0`, commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`, in
`lake-manifest.json`.

```sh
git clone https://github.com/YuZh98/aldous-broder-lean.git
cd aldous-broder-lean
lake exe cache get              # download compiled mathlib
lake build                      # compile the development
python3 scripts/check_axioms.py # axiom audit
```

The audit runs `lake env lean AxiomCheck.lean` and fails unless each of the
16 listed theorems, the four endpoints and their principal proof obligations,
depends only on `propext`, `Classical.choice` and `Quot.sound`. Continuous
integration runs the build, a search for `sorry`/`admit`, and the audit on
every push.

## Layout

| Path | Contents |
|---|---|
| `EAB/Paper/` | the 21 Lean files |
| `EAB.lean` | imports all of them |
| `AxiomCheck.lean`, `scripts/check_axioms.py` | the axiom audit |
| `blueprint/` | the blueprint the proofs follow |

## Citation

See [`CITATION.cff`](CITATION.cff), or use GitHub's "Cite this repository"
button.

## License

[Apache License 2.0](LICENSE).
