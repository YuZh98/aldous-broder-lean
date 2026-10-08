import EAB.Paper.ForestLaw

/-!
# The Aldous--Broder theorem for an irreducible chain

Theorem `thm:ab` of the blueprint. With one root the completion
factor is the single-root normalization divided by `det L[{r}]`, so
the law of the first-entrance tree is its weight divided by
`Λ ∏_v π_v`. Summing over the parent maps, which almost surely
contain the first-entrance tree by Lemma `lem:cover`, identifies
this constant with the sum of the tree weights.
-/

open MeasureTheory ProbabilityTheory Finset

namespace EAB.Paper.Chain

open Foundation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## A one-by-one inverse -/

/-- The inverse of a one-by-one matrix has the entry `1 / det`. -/
theorem inv_apply_of_card_eq_one {ι : Type*} [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι ℝ) (hcard : Fintype.card ι = 1)
    (hdet : A.det ≠ 0) (k : ι) : A⁻¹ k k = 1 / A.det := by
  haveI : Subsingleton ι :=
    Fintype.card_le_one_iff_subsingleton.mp hcard.le
  have hmul := congrFun (congrFun
    (Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hdet)) k) k
  rw [Matrix.mul_apply, Fintype.sum_subsingleton _ k,
    Matrix.one_apply_eq] at hmul
  have hentry : A.det = A k k :=
    Matrix.det_eq_elem_of_card_eq_one hcard k
  rw [hentry]
  have hk : A k k ≠ 0 := hentry ▸ hdet
  field_simp
  linarith [hmul]

variable {P : Matrix V V ℝ} {π : V → ℝ}

omit [DecidableEq V] in
theorem singleton_ne_univ (hcard : 2 ≤ Fintype.card V) (r : V) :
    ({r} : Finset V) ≠ univ := by
  intro h
  have hc : ({r} : Finset V).card = Fintype.card V := by
    rw [h, Finset.card_univ]
  rw [Finset.card_singleton] at hc
  omega

/-- With one root, the completion factor is `1 / det L[{r}]`. -/
theorem completionFactor_singleton (hP : IsStochastic P)
    (hirr : IsIrreducible P) (hπ : IsStationary P π)
    (hcard : 2 ≤ Fintype.card V) (r : V)
    (f : ParentAssignment ({r} : Finset V))
    (hpm : IsPaperParentMap {r} f) :
    completionFactor (reversedMatrix P π) {r} f
        ⟨r, Finset.mem_singleton_self r⟩ =
      1 / (Foundation.principal (reversedMatrix P π) {r}).det := by
  have hB : ({r} : Finset V) ≠ univ := singleton_ne_univ hcard r
  have hBne : ({r} : Finset V).Nonempty := Finset.singleton_nonempty r
  have hcardB : ({r} : Finset V).card = 1 := Finset.card_singleton r
  have hcard' : Fintype.card ({r} : Finset V) = 1 := by
    rw [Fintype.card_coe]
    exact hcardB
  haveI : Subsingleton ({r} : Finset V) :=
    Fintype.card_le_one_iff_subsingleton.mp hcard'.le
  have hdet :
      (Foundation.principal (reversedMatrix P π) {r}).det ≠ 0 :=
    (det_principal_reversedMatrix_pos hP hirr hπ {r} hBne hB).ne'
  have hmass : orderMass (reversedMatrix P π) {r} f
      ⟨r, Finset.mem_singleton_self r⟩ = 1 := by
    rw [← sum_orderWeight_eq_orderMass_of_card_one _ {r} hcardB hB f]
    exact single_root_normalization _
      (reversedMatrix_mulVec_one hP hπ) {r} hcardB hB f hpm
      (minorCondition_reversedMatrix hP hirr hπ {r} hBne f)
  rw [completionFactor,
    Fintype.sum_subsingleton _ ⟨r, Finset.mem_singleton_self r⟩,
    hmass, one_mul, inv_apply_of_card_eq_one _ hcard' hdet]

variable [MeasurableSpace V] [MeasurableSingletonClass V]

/-- **Theorem `thm:ab`, first expression.** The law of the
first-entrance tree of the covering walk started at `r`. -/
theorem aldous_broder (hP : IsStochastic P) (hirr : IsIrreducible P)
    (hπ : IsStationary P π) (hcard : 2 ≤ Fintype.card V) (r : V)
    (f : ParentAssignment ({r} : Finset V))
    (hpm : IsPaperParentMap {r} f) :
    chainLaw P hP r (forestEvent {r} f) =
      ENNReal.ofReal
        (forestWeight P π {r} f / (cofactorSum P * ∏ v, π v)) := by
  have hB : ({r} : Finset V) ≠ univ := singleton_ne_univ hcard r
  have hdet :
      (Foundation.principal (reversedMatrix P π) {r}).det ≠ 0 :=
    (det_principal_reversedMatrix_pos hP hirr hπ {r}
      (Finset.singleton_nonempty r) hB).ne'
  have hprod : ∏ v, π v = π r * ∏ v ∈ univ \ {r}, π v := by
    rw [Finset.sdiff_singleton_eq_erase,
      Finset.mul_prod_erase univ π (Finset.mem_univ r)]
  have hΛ : cofactorSum P ≠ 0 := (cofactorSum_pos hP hirr hcard).ne'
  have hπr : π r ≠ 0 := (hπ.pos r).ne'
  have hπZ : ∏ v ∈ univ \ {r}, π v ≠ 0 :=
    (Finset.prod_pos fun v _ => hπ.pos v).ne'
  rw [chainLaw_forestEvent_eq hP hirr hπ hcard {r} hB
      ⟨r, Finset.mem_singleton_self r⟩ f,
    completionFactor_singleton hP hirr hπ hcard r f hpm, hprod]
  congr 1
  field_simp

/-! ## Total probability -/

/-- The events of distinct parent assignments are disjoint, and
almost surely one of them occurs. -/
theorem sum_chainLaw_forestEvent (hP : IsStochastic P)
    (hirr : IsIrreducible P) (B : Finset V) (r : V) (hr : r ∈ B) :
    ∑ f : ParentAssignment B,
      chainLaw P hP r (forestEvent B f) = 1 := by
  classical
  have hcover : chainLaw P hP r {ω | ∀ v, Hits ω v}ᶜ = 0 :=
    ae_iff.mp (ae_hits_all P hP hirr r)
  simp only [chainLaw_forestEvent_eq_orderUnion P hP hirr B r]
  rw [← measure_biUnion_finset]
  · apply le_antisymm prob_le_one
    have hfull : chainLaw P hP r
        ({ω | ω 0 = r} ∩ {ω | ∀ v, Hits ω v}) = 1 := by
      rw [measure_inter_conull hcover, chainLaw_start]
    rw [← hfull]
    apply measure_mono
    rintro ω ⟨h0, hcov⟩
    have hmem : ω ∈ forestEvent B (entranceForest B ω) ∩
        {ω | ω 0 = r} := ⟨⟨hcov, rfl⟩, h0⟩
    rw [forestEvent_inter_start] at hmem
    exact Set.mem_biUnion (Finset.mem_univ _) hmem.1
  · intro f _ f' _ hne
    exact disjoint_orderUnion B r hne
  · intro f _
    exact measurableSet_orderUnion B r hr f

/-- By Lemma `lem:cover`, a parent assignment that is not a parent
map is almost surely not the first-entrance forest. -/
theorem chainLaw_forestEvent_of_not_parentMap (hP : IsStochastic P)
    (B : Finset V) (r : V) (hr : r ∈ B) (f : ParentAssignment B)
    (hf : ¬ IsPaperParentMap B f) :
    chainLaw P hP r (forestEvent B f) = 0 := by
  rw [← chainLaw_inter_start P hP r (forestEvent B f)]
  have hempty : forestEvent B f ∩ {ω | ω 0 = r} = ∅ := by
    apply Set.eq_empty_of_forall_notMem
    rintro ω ⟨⟨hcov, hforest⟩, h0⟩
    apply hf
    rw [← hforest]
    exact isPaperParentMap_entranceForest B ω
      (by rw [show ω 0 = r from h0]; exact hr)
      (fun v _ => hcov v)
  rw [hempty, measure_empty]

open scoped Classical in
/-- The parent maps rooted at `B`. -/
noncomputable def parentMaps (B : Finset V) :
    Finset (ParentAssignment B) :=
  Finset.univ.filter fun f => IsPaperParentMap B f

theorem sum_chainLaw_forestEvent_parentMaps (hP : IsStochastic P)
    (hirr : IsIrreducible P) (B : Finset V) (r : V) (hr : r ∈ B) :
    ∑ f ∈ parentMaps B, chainLaw P hP r (forestEvent B f) = 1 := by
  classical
  rw [← sum_chainLaw_forestEvent hP hirr B r hr, parentMaps,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro f _
  by_cases hf : IsPaperParentMap B f
  · rw [if_pos hf]
  · rw [if_neg hf,
      chainLaw_forestEvent_of_not_parentMap hP B r hr f hf]

/-- The normalizing constant is the sum of the tree weights. -/
theorem sum_forestWeight_singleton (hP : IsStochastic P)
    (hirr : IsIrreducible P) (hπ : IsStationary P π)
    (hcard : 2 ≤ Fintype.card V) (r : V) :
    ∑ f ∈ parentMaps ({r} : Finset V), forestWeight P π {r} f =
      cofactorSum P * ∏ v, π v := by
  classical
  have hden : 0 < cofactorSum P * ∏ v, π v :=
    mul_pos (cofactorSum_pos hP hirr hcard)
      (Finset.prod_pos fun v _ => hπ.pos v)
  have htotal := sum_chainLaw_forestEvent_parentMaps hP hirr
    ({r} : Finset V) r (Finset.mem_singleton_self r)
  have hterm : ∀ f ∈ parentMaps ({r} : Finset V),
      chainLaw P hP r (forestEvent {r} f) =
        ENNReal.ofReal
          (forestWeight P π {r} f /
            (cofactorSum P * ∏ v, π v)) := by
    intro f hf
    exact aldous_broder hP hirr hπ hcard r f
      (Finset.mem_filter.mp hf).2
  rw [Finset.sum_congr rfl hterm,
    ← ENNReal.ofReal_sum_of_nonneg (fun f _ =>
      div_nonneg (forestWeight_nonneg hP hπ {r} f) hden.le),
    ← Finset.sum_div, ENNReal.ofReal_eq_one] at htotal
  exact (div_eq_one_iff_eq hden.ne').mp htotal

/-- **Theorem `thm:ab`, second expression.** The law of the
first-entrance tree is proportional to the tree weight. -/
theorem aldous_broder_normalized (hP : IsStochastic P)
    (hirr : IsIrreducible P) (hπ : IsStationary P π)
    (hcard : 2 ≤ Fintype.card V) (r : V)
    (f : ParentAssignment ({r} : Finset V))
    (hpm : IsPaperParentMap {r} f) :
    chainLaw P hP r (forestEvent {r} f) =
      ENNReal.ofReal
        (forestWeight P π {r} f /
          ∑ f' ∈ parentMaps ({r} : Finset V),
            forestWeight P π {r} f') := by
  rw [aldous_broder hP hirr hπ hcard r f hpm,
    sum_forestWeight_singleton hP hirr hπ hcard r]

end EAB.Paper.Chain
