# Formalization reference

Paper numbers refer to the unpublished manuscript dated 7 October 2026.
The [blueprint](../blueprint/blueprint.pdf) uses separate numbering.
Lean docstrings cite its labels.

## Main results

Names below are in `EAB.Paper`.

| Paper | Blueprint | Lean theorem |
|---|---|---|
| Theorem 4.5: order-mass identity | Theorems 4.1–4.2 | `order_mass_identity`, `single_root_normalization` |
| Theorem 6.1: Aldous–Broder | Theorem 6.2 | `Chain.aldous_broder`, `Chain.aldous_broder_normalized` |
| Theorem 6.4: stopped forest | Theorem 7.3 | `Chain.stopped_forest_law` |

The order-mass identity equates the sum of growth-order weights entering
at root `r` with the principal cofactor at `r` of `I - Γ^B M_f`.
It holds over any field for zero-row-sum matrices, nonempty proper root
sets, and nonzero principal minors on proper growth-order bases.

## Supporting results

### Matrix lemmas

Names in this table are in `EAB.Paper.Foundation`.

| Paper | Blueprint | Lean declarations |
|---|---|---|
| Lemma 2.1 | Lemma 1.2 | `adjugate_apply_eq_principalCofactor`<br>`principalCofactor_left_kernel`<br>`det_add_rank_one_zero_row_sum` |
| Definition 2.2, (2.2) | Definition 1.3, Lemma 1.4 | `harmonic`, `gamma`, `harmonic_one` |
| Lemma 2.3 | Lemma 1.4 | `harmonic_boundary`<br>`harmonic_interior_row`<br>`harmonic_unique` |
| Lemma 5.1 | Lemmas 2.5–2.6 | `one_vertex_transfer`<br>`one_vertex_transfer_singleton` |

In (2.3), `Γ^U_{uv}` is `Foundation.gamma L U v u` for `u ∈ U`.

### Forest definitions

Names in this table are in `EAB.Paper`.

| Paper | Blueprint | Lean declarations |
|---|---|---|
| Definition 2.5, Lemma 2.6 | Definitions 3.1, 3.3; Lemma 3.2 | `IsPaperParentMap`, `growthOrders`, `rootIndicator`<br>`rootBlock_pairwiseDisjoint`, `rootBlocks_cover`<br>`childDescendants_pairwise`, `childDescendants_cover` |
| (3.3), Definition 4.3 | Definition 3.3 | `orderWeight`, `orderMass` |

### Chain lemmas

Names in this table are in `EAB.Paper.Chain`.

| Paper | Blueprint | Lean declarations |
|---|---|---|
| Lemma 3.3 | Lemmas 5.2, 5.4 | `reversedMatrix_mulVec_one`<br>`det_principal_reversedMatrix`<br>`det_principal_reversedMatrix_pos`<br>`green_hasSum`, `green_reversal`<br>`inv_diag_eq_det_ratio`, `inv_column_eq_gamma` |
| Lemma 3.4 | Lemma 5.3 | `cofactorVec_pos`<br>`isStationary_cofactor`<br>`IsStationary.cofactorVec_eq` |
| Proposition 3.2, (3.5) | Lemmas 5.6–5.7 | `chainLaw_orderEvent_eq` |

## Modeling and scope

- **Trajectories:** `Chain.chainLaw` is mathlib's Ionescu–Tulcea measure;
  `Chain.chainLaw_cylinder` proves the cylinder formula. Probabilities
  use extended nonnegative reals.
- **Forest event:** requires eventual coverage of every state. This has
  probability one (`Chain.ae_hits_all`), so the event agrees with the
  stopped-forest event up to a null set.
- **Stationarity:** `π` is assumed positive, normalized, and invariant.
  `Chain.IsStationary.cofactorVec_eq` identifies it with the normalized
  cofactor vector and establishes uniqueness.
- **Boundary cases:** chain results assume `2 ≤ Fintype.card V`.
  `Chain.stopped_forest_law` accepts every parent assignment, including
  forests of zero weight.
- **Lemma 2.6:** child partitions are stated for children of roots.
  `Foundation.one_vertex_transfer` generalizes Lemma 5.1 to any fold
  weights summing to one.
- **Proposition 3.2:** `Chain.chainLaw_orderEvent_eq` states (3.5) for growth
  orders and proves its right side nonnegative. Incompatible orderings
  and the single-root formula (3.6) have no separate matching corollaries.
- **Theorem 6.4:** `Chain.stopped_forest_law` gives the probability formula
  from the paper's proof and the completion identity (6.3). Together they
  yield the second expression of (6.2). The first expression follows from
  `Chain.chainLaw_forestEvent_marginal` and
  `Chain.aldous_broder_normalized`; it has no separate theorem.

## Completion notation

With `L = Chain.reversedMatrix P π`:

| Quantity | Meaning |
|---|---|
| `Chain.completionFactor L B f r` | `g(B,f)ᵀ L[B]⁻¹ e_r`; called `φ_r(f)` in the blueprint |
| Manuscript `φ_r(F_0)` | Sum of added-edge weights over tree completions |

The latter is `∑ h ∈ Chain.completions B r r.2 f,
Chain.completionWeight P π B r h`. The second conclusion of
`Chain.stopped_forest_law` identifies it with
`det L[B] * (∏ j ∈ B \ {r}, π j) * Chain.completionFactor L B f r`.

## Not formalized

- Theorem 6.2; Corollaries 4.9 and 6.6.
- Completion-weight determinant formula (6.4).
- Appendix A's worked examples; Appendices C and D; numerical experiments.
