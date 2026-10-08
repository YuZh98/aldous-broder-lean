import EAB.Paper.AldousBroder

/-!
# The stopped forest as a marginal of the covering tree

Lemma `lem:forest-marginal` of the blueprint and the completion
weights of Theorem `thm:stopped` for a forest of positive weight.
The first-entrance forest rooted at `B` is the restriction of the
first-entrance tree to the edges entering the non-roots. Comparing
the law of the forest with the sum of the laws of the trees that
complete it, and cancelling the forest weight, evaluates the total
weight of the completions.
-/

open MeasureTheory ProbabilityTheory Finset

namespace EAB.Paper.Chain

open Foundation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Completions of a forest -/

/-- The restriction of a parent assignment on `V \ {r}` to the
non-roots of `B ∋ r`. -/
def restrictParents (B : Finset V) (r : V) (hr : r ∈ B)
    (h : ParentAssignment ({r} : Finset V)) : ParentAssignment B :=
  fun v => h ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hv =>
    nonroot_not_mem B v (by
      rw [Finset.mem_singleton.mp hv]
      exact hr)⟩⟩

open scoped Classical in
/-- The arborescences rooted at `r` that complete the forest `f`. -/
noncomputable def completions (B : Finset V) (r : V) (hr : r ∈ B)
    (f : ParentAssignment B) :
    Finset (ParentAssignment ({r} : Finset V)) :=
  (parentMaps {r}).filter fun h => restrictParents B r hr h = f

/-- The weight `∏_{j ∈ B \ {r}} π_{h(j)} P_{h(j) j}` of the edges of
a completion that enter the roots other than `r`. -/
noncomputable def completionWeight (P : Matrix V V ℝ) (π : V → ℝ)
    (B : Finset V) (r : V) (h : ParentAssignment ({r} : Finset V)) :
    ℝ :=
  ∏ j ∈ B \ {r},
    π (extendParents {r} h j) * P (extendParents {r} h j) j

/-- The weight of a completion separates its edges entering the
non-roots from those entering the roots other than `r`. -/
theorem forestWeight_completion (P : Matrix V V ℝ) (π : V → ℝ)
    (B : Finset V) (r : V) (hr : r ∈ B)
    (h : ParentAssignment ({r} : Finset V)) :
    forestWeight P π {r} h =
      forestWeight P π B (restrictParents B r hr h) *
        completionWeight P π B r h := by
  have hsplit : univ \ {r} = (univ \ B) ∪ (B \ {r}) := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_singleton, Finset.mem_union]
    constructor
    · intro hv
      by_cases hvB : v ∈ B
      · exact Or.inr ⟨hvB, hv⟩
      · exact Or.inl hvB
    · rintro (hvB | ⟨-, hv⟩)
      · exact fun hvr => hvB (hvr ▸ hr)
      · exact hv
  have hdisj : Disjoint (univ \ B) (B \ {r}) := by
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_sdiff.mp hv').1
  have hleft : forestWeight P π {r} h =
      ∏ v ∈ univ \ {r},
        π (extendParents {r} h v) * P (extendParents {r} h v) v := by
    rw [forestWeight, ← Finset.prod_coe_sort (univ \ {r})
      (fun v => π (extendParents {r} h v) *
        P (extendParents {r} h v) v)]
    apply Finset.prod_congr rfl
    intro v _
    rw [extendParents_nonroot {r} h (nonroot_not_mem {r} v)]
  have hright : forestWeight P π B (restrictParents B r hr h) =
      ∏ v ∈ univ \ B,
        π (extendParents {r} h v) * P (extendParents {r} h v) v := by
    rw [forestWeight, ← Finset.prod_coe_sort (univ \ B)
      (fun v => π (extendParents {r} h v) *
        P (extendParents {r} h v) v)]
    apply Finset.prod_congr rfl
    intro v _
    have hv : (v : V) ∉ ({r} : Finset V) := fun hvr =>
      nonroot_not_mem B v (by
        rw [Finset.mem_singleton.mp hvr]
        exact hr)
    rw [extendParents_nonroot {r} h hv]
    rfl
  rw [hleft, hright, completionWeight, hsplit,
    Finset.prod_union hdisj]

variable {P : Matrix V V ℝ} {π : V → ℝ}

variable [MeasurableSpace V] [MeasurableSingletonClass V]

/-- **Lemma `lem:forest-marginal`.** The law of the stopped forest
is the sum of the laws of the covering trees that complete it. -/
theorem chainLaw_forestEvent_marginal (hP : IsStochastic P)
    (hirr : IsIrreducible P) (B : Finset V) (r : V) (hr : r ∈ B)
    (f : ParentAssignment B) :
    chainLaw P hP r (forestEvent B f) =
      ∑ h ∈ completions B r hr f,
        chainLaw P hP r (forestEvent {r} h) := by
  classical
  have hcover : chainLaw P hP r {ω | ∀ v, Hits ω v}ᶜ = 0 :=
    ae_iff.mp (ae_hits_all P hP hirr r)
  let S : Finset (ParentAssignment ({r} : Finset V)) :=
    Finset.univ.filter fun h => restrictParents B r hr h = f
  have hset : forestEvent B f ∩ {ω | ω 0 = r} =
      (⋃ h ∈ S, orderUnion {r} r h) ∩ {ω | ∀ v, Hits ω v} := by
    apply Set.ext
    intro ω
    constructor
    · rintro ⟨⟨hcov, hforest⟩, h0⟩
      refine ⟨?_, hcov⟩
      have hmem : ω ∈ forestEvent {r} (entranceForest {r} ω) ∩
          {ω | ω 0 = r} := ⟨⟨hcov, rfl⟩, h0⟩
      rw [forestEvent_inter_start] at hmem
      refine Set.mem_biUnion (x := entranceForest {r} ω) ?_ hmem.1
      simp only [S, Finset.coe_filter, Finset.mem_univ, true_and,
        Set.mem_setOf_eq]
      exact hforest
    · rintro ⟨hunion, hcov⟩
      obtain ⟨h, hhS, hω⟩ := Set.mem_iUnion₂.mp hunion
      have hrestrict : restrictParents B r hr h = f := by
        have := Finset.mem_coe.mp hhS
        exact (Finset.mem_filter.mp this).2
      have hmem : ω ∈ orderUnion {r} r h ∩ {ω | ∀ v, Hits ω v} :=
        ⟨hω, hcov⟩
      rw [← forestEvent_inter_start] at hmem
      obtain ⟨⟨-, hforest⟩, h0⟩ := hmem
      refine ⟨⟨hcov, ?_⟩, h0⟩
      rw [← hrestrict, ← hforest]
      rfl
  have hsum : chainLaw P hP r (forestEvent B f) =
      ∑ h ∈ S, chainLaw P hP r (forestEvent {r} h) := by
    rw [← chainLaw_inter_start P hP r (forestEvent B f), hset,
      measure_inter_conull hcover, measure_biUnion_finset]
    · apply Finset.sum_congr rfl
      intro h _
      rw [chainLaw_forestEvent_eq_orderUnion P hP hirr {r} r h]
    · intro h _ h' _ hne
      exact disjoint_orderUnion {r} r hne
    · intro h _
      exact measurableSet_orderUnion {r} r
        (Finset.mem_singleton_self r) h
  rw [hsum, completions, parentMaps, Finset.filter_filter]
  symm
  apply Finset.sum_subset
  · intro h hh
    obtain ⟨-, -, hrestrict⟩ := Finset.mem_filter.mp hh
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ h, hrestrict⟩
  · intro h hhS hnot
    have hrestrict := (Finset.mem_filter.mp hhS).2
    have hpm : ¬ IsPaperParentMap {r} h := fun hpm =>
      hnot (Finset.mem_filter.mpr
        ⟨Finset.mem_univ h, hpm, hrestrict⟩)
    exact chainLaw_forestEvent_of_not_parentMap hP {r} r
      (Finset.mem_singleton_self r) h hpm

/-- Equation `eq:completion-weight` for a forest of positive
weight, by comparing `eq:stopped` with the marginal and cancelling
the forest weight. -/
theorem sum_completionWeight_of_pos (hP : IsStochastic P)
    (hirr : IsIrreducible P) (hπ : IsStationary P π)
    (hcard : 2 ≤ Fintype.card V) (B : Finset V) (hB : B ≠ univ)
    (r : B) (f : ParentAssignment B)
    (hpos : 0 < forestWeight P π B f) :
    ∑ h ∈ completions B r r.2 f, completionWeight P π B r h =
      (Foundation.principal (reversedMatrix P π) B).det *
        (∏ j ∈ B \ {(r : V)}, π j) *
        completionFactor (reversedMatrix P π) B f r := by
  classical
  have hΛ : 0 < cofactorSum P := cofactorSum_pos hP hirr hcard
  have hden : 0 < cofactorSum P * ∏ v, π v :=
    mul_pos hΛ (Finset.prod_pos fun v _ => hπ.pos v)
  have hterm : ∀ h ∈ completions B r r.2 f,
      chainLaw P hP r (forestEvent {(r : V)} h) =
        ENNReal.ofReal
          (forestWeight P π B f * completionWeight P π B r h /
            (cofactorSum P * ∏ v, π v)) := by
    intro h hh
    obtain ⟨hpmem, hrestrict⟩ := Finset.mem_filter.mp hh
    rw [aldous_broder hP hirr hπ hcard r h
        (Finset.mem_filter.mp hpmem).2,
      forestWeight_completion P π B r r.2 h, hrestrict]
  have hcw : ∀ h : ParentAssignment ({(r : V)} : Finset V),
      0 ≤ completionWeight P π B r h := fun h =>
    Finset.prod_nonneg fun j _ =>
      mul_nonneg (hπ.pos _).le (hP.nonneg _ _)
  have hlaw := chainLaw_forestEvent_eq hP hirr hπ hcard B hB r f
  rw [chainLaw_forestEvent_marginal hP hirr B r r.2 f,
    Finset.sum_congr rfl hterm,
    ← ENNReal.ofReal_sum_of_nonneg (fun h _ =>
      div_nonneg (mul_nonneg hpos.le (hcw h)) hden.le)] at hlaw
  have hreal : ∑ h ∈ completions B r r.2 f,
      forestWeight P π B f * completionWeight P π B r h /
        (cofactorSum P * ∏ v, π v) =
      forestLawValue P π B f r :=
    (ENNReal.ofReal_eq_ofReal_iff
      (Finset.sum_nonneg fun h _ =>
        div_nonneg (mul_nonneg hpos.le (hcw h)) hden.le)
      (forestLawValue_nonneg hP hirr hπ hcard B hB r f)).mp hlaw
  have hprod : ∏ v, π v =
      π r * (∏ v ∈ univ \ B, π v) * ∏ j ∈ B \ {(r : V)}, π j := by
    have h1 : ∏ v, π v = (∏ v ∈ univ \ B, π v) * ∏ v ∈ B, π v := by
      rw [← Finset.prod_union Finset.sdiff_disjoint,
        Finset.sdiff_union_of_subset (Finset.subset_univ B)]
    have h2 : ∏ v ∈ B, π v = π r * ∏ j ∈ B \ {(r : V)}, π j := by
      rw [Finset.sdiff_singleton_eq_erase,
        Finset.mul_prod_erase B π r.2]
    rw [h1, h2]
    ring
  have hπr : π r ≠ 0 := (hπ.pos r).ne'
  have hπZ : ∏ v ∈ univ \ B, π v ≠ 0 :=
    (Finset.prod_pos fun v _ => hπ.pos v).ne'
  have hπB : ∏ j ∈ B \ {(r : V)}, π j ≠ 0 :=
    (Finset.prod_pos fun v _ => hπ.pos v).ne'
  have hw : forestWeight P π B f ≠ 0 := hpos.ne'
  have hΛ' : cofactorSum P ≠ 0 := hΛ.ne'
  rw [← Finset.sum_div, ← Finset.mul_sum, forestLawValue, hprod]
    at hreal
  field_simp at hreal
  rw [hreal]
  ring

end EAB.Paper.Chain
