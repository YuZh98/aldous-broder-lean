import EAB.Paper.FirstEntranceForest

/-!
# The law of the first-entrance forest

Equation `eq:stopped` of the blueprint. The joint law of the forest
and its discovery order, Lemma `lem:joint-order`, is summed over the
growth orders grouped by the root that is the parent of their first
vertex. The sum is the completion factor
`φ_r(f) = g(B,f)ᵀ L[B]⁻¹ e_r`. For one root this is the computation
behind the Aldous--Broder theorem, and for several roots it is the
stopped forest law.
-/

open MeasureTheory ProbabilityTheory Finset

namespace EAB.Paper.Chain

open Foundation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The forest weight `w_P(f) = ∏_{v ∉ B} π_{f(v)} P_{f(v) v}`. -/
noncomputable def forestWeight (P : Matrix V V ℝ) (π : V → ℝ)
    (B : Finset V) (f : ParentAssignment B) : ℝ :=
  ∏ v : (univ \ B : Finset V), π (f v) * P (f v) v

/-- The completion factor `φ_r(f) = g(B,f)ᵀ L[B]⁻¹ e_r`. -/
noncomputable def completionFactor (L : Matrix V V ℝ) (B : Finset V)
    (f : ParentAssignment B) (r : B) : ℝ :=
  ∑ i : B, orderMass L B f i * (Foundation.principal L B)⁻¹ i r

variable {P : Matrix V V ℝ} {π : V → ℝ}

theorem forestWeight_nonneg (hP : IsStochastic P)
    (hπ : IsStationary P π) (B : Finset V) (f : ParentAssignment B) :
    0 ≤ forestWeight P π B f :=
  Finset.prod_nonneg fun v _ =>
    mul_nonneg (hπ.pos (f v)).le (hP.nonneg (f v) v)

/-- Along an ordering of the non-roots, the product of the
stationary weights is the product over the non-roots. -/
theorem orderPi_eq (π : V → ℝ) (B : Finset V) {τ : List V}
    (hτ : τ ∈ orderings B) :
    orderPi π τ = ∏ v ∈ univ \ B, π v := by
  obtain ⟨hnodup, hfin⟩ := (mem_orderings B τ).mp hτ
  rw [orderPi, ← hfin, List.prod_toFinset _ hnodup]

/-- Along an ordering of the non-roots, the product of the edge
weights is the forest weight. -/
theorem orderEdgeWeight_eq (P : Matrix V V ℝ) (π : V → ℝ)
    (B : Finset V) (f : ParentAssignment B) {τ : List V}
    (hτ : τ ∈ orderings B) :
    orderEdgeWeight P π (extendParents B f) τ =
      forestWeight P π B f := by
  obtain ⟨hnodup, hfin⟩ := (mem_orderings B τ).mp hτ
  rw [orderEdgeWeight, ← List.prod_toFinset _ hnodup, hfin,
    forestWeight,
    ← Finset.prod_coe_sort (univ \ B)
      (fun v => π (extendParents B f v) * P (extendParents B f v) v)]
  apply Finset.prod_congr rfl
  intro v _
  rw [extendParents_nonroot B f (nonroot_not_mem B v)]

/-- The minors required by the order-mass identity are positive for
the matrix of a chain, Lemma `lem:green`. -/
theorem minorCondition_reversedMatrix (hP : IsStochastic P)
    (hirr : IsIrreducible P) (hπ : IsStationary P π)
    (B : Finset V) (hBne : B.Nonempty) (f : ParentAssignment B) :
    MinorCondition (reversedMatrix P π) B f := by
  intro τ hτ l hl
  have hGO := (mem_growthOrders_iff B f τ).mp hτ
  apply (det_principal_reversedMatrix_pos hP hirr hπ _ _ _).ne'
  · exact hBne.mono Finset.subset_union_left
  · intro huniv
    have hcard : (orderBase B τ l).card < Fintype.card V := by
      have h1 : (orderBase B τ l).card ≤
          B.card + (τ.take l).toFinset.card :=
        Finset.card_union_le _ _
      have h2 : (τ.take l).toFinset.card ≤ l := by
        refine (List.toFinset_card_le _).trans ?_
        rw [List.length_take]
        exact Nat.min_le_left _ _
      have h3 : τ.length = (univ \ B).card := hGO.length_eq
      have h4 : (univ \ B).card + B.card = Fintype.card V := by
        rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ B),
          Finset.card_univ]
      omega
    rw [huniv, Finset.card_univ] at hcard
    exact lt_irrefl _ hcard

/-- The real number on the right of `eq:stopped`. -/
noncomputable def forestLawValue (P : Matrix V V ℝ) (π : V → ℝ)
    (B : Finset V) (f : ParentAssignment B) (r : B) : ℝ :=
  (Foundation.principal (reversedMatrix P π) B).det /
      (π r * (∏ v ∈ univ \ B, π v) * cofactorSum P) *
    forestWeight P π B f *
    completionFactor (reversedMatrix P π) B f r

/-- Summing Lemma `lem:joint-order` over the growth orders, grouped
by the root `i` that is the parent of their first vertex, produces
`∑_i 𝒢_i (L[B]⁻¹)_{ir} = φ_r(f)`. -/
theorem sum_excursionWeight_growthOrders (hP : IsStochastic P)
    (hirr : IsIrreducible P) (hπ : IsStationary P π)
    (hcard : 2 ≤ Fintype.card V) (B : Finset V) (hB : B ≠ univ)
    (r : B) (f : ParentAssignment B) :
    ∑ τ ∈ growthOrders B f,
        excursionWeight P (extendParents B f) B r τ =
      forestLawValue P π B f r := by
  classical
  let L := reversedMatrix P π
  let g := extendParents B f
  let K : ℝ := (Foundation.principal L B).det /
    (π r * (∏ v ∈ univ \ B, π v) * cofactorSum P) *
      forestWeight P π B f
  -- The entry of `L[B]⁻¹` selected by the first vertex of an order.
  let entry : List V → ℝ := fun τ =>
    match τ with
    | [] => 0
    | z :: _ => invEntry L B (g z) r
  have hweight : ∀ τ ∈ growthOrders B f,
      excursionWeight P g B r τ =
        K * (entry τ * orderWeight L g B τ) := by
    intro τ hτ
    have hord : τ ∈ orderings B :=
      ((mem_growthOrders_iff_parentsBefore B f τ).mp hτ).1
    obtain ⟨hnodup, hfin⟩ := (mem_orderings B τ).mp hord
    cases τ with
    | nil =>
        exact absurd rfl
          (((mem_growthOrders_iff B f _).mp hτ).ne_nil hB)
    | cons z rest =>
        rw [excursionWeight_eq hP hirr hπ hcard g rest z B r r.2
          hnodup hfin, orderPi_eq π B hord,
          orderEdgeWeight_eq P π B f hord]
        simp only [K, entry]
        ring
  have hgroup : ∑ τ ∈ growthOrders B f,
      entry τ * orderWeight L g B τ =
        completionFactor L B f r := by
    rw [sum_growthOrders_by_firstParent B f hB, completionFactor]
    apply Finset.sum_congr rfl
    intro i _
    rw [orderMass, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro τ hτ
    obtain ⟨-, hfirst⟩ := Finset.mem_filter.mp hτ
    cases τ with
    | nil => simp [firstParent] at hfirst
    | cons z rest =>
        have hgz : g z = (i : V) := by
          simpa [firstParent] using hfirst
        simp only [entry]
        rw [hgz, invEntry, dif_pos ⟨i.2, r.2⟩, mul_comm]
  rw [Finset.sum_congr rfl hweight, ← Finset.mul_sum, hgroup]
  rfl

theorem excursionWeight_nonneg_of_mem_growthOrders
    (hP : IsStochastic P) (hirr : IsIrreducible P) (B : Finset V)
    (r : V) (f : ParentAssignment B) {τ : List V}
    (hτ : τ ∈ growthOrders B f) :
    0 ≤ excursionWeight P (extendParents B f) B r τ := by
  have hord : τ ∈ orderings B :=
    ((mem_growthOrders_iff_parentsBefore B f τ).mp hτ).1
  obtain ⟨hnodup, hfin⟩ := (mem_orderings B τ).mp hord
  apply excursionWeight_nonneg hP hirr _ τ B r _ hnodup
  intro z hz
  have hmem : z ∈ τ.toFinset := List.mem_toFinset.mpr hz
  rw [hfin] at hmem
  exact (Finset.mem_sdiff.mp hmem).2

theorem forestLawValue_nonneg (hP : IsStochastic P)
    (hirr : IsIrreducible P) (hπ : IsStationary P π)
    (hcard : 2 ≤ Fintype.card V) (B : Finset V) (hB : B ≠ univ)
    (r : B) (f : ParentAssignment B) :
    0 ≤ forestLawValue P π B f r := by
  rw [← sum_excursionWeight_growthOrders hP hirr hπ hcard B hB r f]
  exact Finset.sum_nonneg fun τ hτ =>
    excursionWeight_nonneg_of_mem_growthOrders hP hirr B r f hτ

variable [MeasurableSpace V] [MeasurableSingletonClass V]

/-- **Lemma `lem:joint-order`.** The joint law of the first-entrance
forest and its discovery order, for a growth order `(z, rest)`. The
real number on the right is nonnegative, so the probability equals it. -/
theorem chainLaw_orderEvent_eq (hP : IsStochastic P)
    (hirr : IsIrreducible P) (hπ : IsStationary P π)
    (hcard : 2 ≤ Fintype.card V) (B : Finset V) (r : B)
    (f : ParentAssignment B) (z : V) (rest : List V)
    (hτ : z :: rest ∈ growthOrders B f) :
    chainLaw P hP r
        (orderEvent (extendParents B f) B r (z :: rest)) =
      ENNReal.ofReal
        ((Foundation.principal (reversedMatrix P π) B).det /
            (π r * (∏ v ∈ univ \ B, π v) * cofactorSum P) *
          forestWeight P π B f *
          invEntry (reversedMatrix P π) B (extendParents B f z) r *
          orderWeight (reversedMatrix P π) (extendParents B f) B
            (z :: rest)) ∧
      0 ≤ (Foundation.principal (reversedMatrix P π) B).det /
            (π r * (∏ v ∈ univ \ B, π v) * cofactorSum P) *
          forestWeight P π B f *
          invEntry (reversedMatrix P π) B (extendParents B f z) r *
          orderWeight (reversedMatrix P π) (extendParents B f) B
            (z :: rest) := by
  have hord : z :: rest ∈ orderings B :=
    ((mem_growthOrders_iff_parentsBefore B f _).mp hτ).1
  obtain ⟨hnodup, hfin⟩ := (mem_orderings B _).mp hord
  have hnn := excursionWeight_nonneg_of_mem_growthOrders hP hirr B r f hτ
  rw [excursionWeight_eq hP hirr hπ hcard _ rest z B r r.2 hnodup hfin,
    orderPi_eq π B hord, orderEdgeWeight_eq P π B f hord] at hnn
  refine ⟨?_, hnn⟩
  rw [chainLaw_orderEvent P hP hirr _ (z :: rest) B r r.2 hnodup
      hfin,
    excursionWeight_eq hP hirr hπ hcard _ rest z B r r.2 hnodup hfin,
    orderPi_eq π B hord, orderEdgeWeight_eq P π B f hord]

/-- **Equation `eq:stopped`.** The law of the first-entrance forest
rooted at `B` of the walk started at the seed `r ∈ B`. -/
theorem chainLaw_forestEvent_eq (hP : IsStochastic P)
    (hirr : IsIrreducible P) (hπ : IsStationary P π)
    (hcard : 2 ≤ Fintype.card V) (B : Finset V) (hB : B ≠ univ)
    (r : B) (f : ParentAssignment B) :
    chainLaw P hP r (forestEvent B f) =
      ENNReal.ofReal
        ((Foundation.principal (reversedMatrix P π) B).det /
            (π r * (∏ v ∈ univ \ B, π v) * cofactorSum P) *
          forestWeight P π B f *
          completionFactor (reversedMatrix P π) B f r) := by
  rw [chainLaw_forestEvent_growthOrders P hP hirr B r r.2 f,
    ← ENNReal.ofReal_sum_of_nonneg (fun τ hτ =>
      excursionWeight_nonneg_of_mem_growthOrders hP hirr B r f hτ),
    sum_excursionWeight_growthOrders hP hirr hπ hcard B hB r f]
  rfl

end EAB.Paper.Chain
