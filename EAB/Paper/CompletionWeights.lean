import EAB.Paper.StoppedForest

/-!
# The completion weights of a forest of arbitrary weight

Equation `eq:completion-weight` of Theorem `thm:stopped` holds also
when the forest weight vanishes, where it cannot be obtained by
cancelling that weight. The matrix `P` is replaced by
`P_ε = (1 - ε) P + ε 𝟏𝟏ᵀ / n`, all of whose forest weights are
positive. The stationary distribution of `P_ε` is its normalized
cofactor vector, a continuous function of `ε`. The minors used by
the harmonic extensions and by `L[B]⁻¹` are positive at `ε = 0`, so
the order masses and the completion factor are continuous there.
Both sides of the identity are therefore continuous at `ε = 0`, and
they agree for `0 < ε < 1`.
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology

namespace EAB.Paper.Chain

open Foundation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Continuity in the matrix `L` -/

omit [Fintype V] [DecidableEq V] in
theorem continuous_entry (u v : V) :
    Continuous fun L : Matrix V V ℝ => L u v :=
  (continuous_apply v).comp (continuous_apply u)

omit [DecidableEq V] in
theorem continuous_principal (U : Finset V) :
    Continuous fun L : Matrix V V ℝ => Foundation.principal L U :=
  continuous_id.matrix_submatrix _ _

theorem continuousAt_det_principal (U : Finset V)
    (L₀ : Matrix V V ℝ) :
    ContinuousAt
      (fun L : Matrix V V ℝ => (Foundation.principal L U).det) L₀ :=
  (continuous_principal U).matrix_det.continuousAt

theorem continuousAt_inv_principal (U : Finset V)
    (L₀ : Matrix V V ℝ)
    (h : (Foundation.principal L₀ U).det ≠ 0) (i j : U) :
    ContinuousAt
      (fun L : Matrix V V ℝ => (Foundation.principal L U)⁻¹ i j)
      L₀ := by
  have hinv : ContinuousAt (fun A : Matrix U U ℝ => A⁻¹)
      (Foundation.principal L₀ U) := by
    apply continuousAt_matrix_inv
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ h
  have hcomp : ContinuousAt
      (fun L : Matrix V V ℝ => (Foundation.principal L U)⁻¹) L₀ :=
    ContinuousAt.comp (g := fun A : Matrix U U ℝ => A⁻¹)
      (f := fun L : Matrix V V ℝ => Foundation.principal L U)
      (x := L₀) hinv (continuous_principal U).continuousAt
  have hentry : Continuous fun A : Matrix U U ℝ => A i j :=
    (continuous_apply j).comp (continuous_apply i)
  exact ContinuousAt.comp (g := fun A : Matrix U U ℝ => A i j)
    (f := fun L : Matrix V V ℝ => (Foundation.principal L U)⁻¹)
    (x := L₀) hentry.continuousAt hcomp

theorem continuousAt_harmonic (U : Finset V)
    (m : (univ \ U : Finset V) → ℝ) (L₀ : Matrix V V ℝ)
    (h : (Foundation.principal L₀ U).det ≠ 0) (x : V) :
    ContinuousAt (fun L : Matrix V V ℝ => harmonic L U m x) L₀ := by
  by_cases hx : x ∈ U
  · have hform : (fun L : Matrix V V ℝ => harmonic L U m x) =
        fun L => ∑ j : U,
          -(Foundation.principal L U)⁻¹ ⟨x, hx⟩ j *
            ∑ v : (univ \ U : Finset V), L j v * m v := by
      funext L
      have hint := harmonic_interior_formula L U m ⟨x, hx⟩
      simp only [Matrix.mulVec, dotProduct, boundaryBlock,
        Matrix.submatrix_apply, Matrix.neg_apply] at hint
      exact hint
    rw [hform]
    apply tendsto_finsetSum
    intro j _
    apply Tendsto.mul
    · exact (continuousAt_inv_principal U L₀ h ⟨x, hx⟩ j).neg
    · apply tendsto_finsetSum
      intro v _
      exact ((continuous_entry (j : V) (v : V)).continuousAt).mul
        continuousAt_const
  · have hconst : (fun L : Matrix V V ℝ => harmonic L U m x) =
        fun _ => m ⟨x, Finset.mem_sdiff.mpr
          ⟨Finset.mem_univ x, hx⟩⟩ := by
      funext L
      exact harmonic_boundary L U m
        ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩⟩
    rw [hconst]
    exact continuousAt_const

/-- The order weights are continuous at a matrix whose minors on
nonempty proper sets do not vanish. -/
theorem continuousAt_orderWeight (g : V → V) (L₀ : Matrix V V ℝ)
    (hdet : ∀ U : Finset V, U.Nonempty → U ≠ univ →
      (Foundation.principal L₀ U).det ≠ 0) :
    ∀ (τ : List V) (U : Finset V), U.Nonempty →
      (∀ z ∈ τ, z ∉ U) → τ.Nodup →
      ContinuousAt
        (fun L : Matrix V V ℝ => orderWeight L g U τ) L₀
  | [], _, _, _, _ => continuousAt_const
  | [_], _, _, _, _ => continuousAt_const
  | z :: y :: rest, U, hU, hdisj, hnodup => by
      have hz : z ∉ U := hdisj z (by simp)
      have hUne : U ≠ univ := fun h => hz (h ▸ Finset.mem_univ z)
      obtain ⟨hzrest, hrestNodup⟩ := List.nodup_cons.mp hnodup
      have hrest : ∀ v ∈ y :: rest, v ∉ insert z U := by
        intro v hv hmem
        rcases Finset.mem_insert.mp hmem with hvz | hvU
        · exact hzrest (hvz ▸ hv)
        · exact hdisj v (List.mem_cons_of_mem z hv) hvU
      have hrec := continuousAt_orderWeight g L₀ hdet (y :: rest)
        (insert z U) ⟨z, Finset.mem_insert_self z U⟩ hrest
        hrestNodup
      have hgamma : ContinuousAt
          (fun L : Matrix V V ℝ => gamma L U z (g y)) L₀ :=
        continuousAt_harmonic U (coordBoundary U z) L₀
          (hdet U hU hUne) (g y)
      exact hgamma.mul hrec

theorem continuousAt_orderMass (L₀ : Matrix V V ℝ)
    (hdet : ∀ U : Finset V, U.Nonempty → U ≠ univ →
      (Foundation.principal L₀ U).det ≠ 0)
    (B : Finset V) (hBne : B.Nonempty) (f : ParentAssignment B)
    (i : B) :
    ContinuousAt (fun L : Matrix V V ℝ => orderMass L B f i) L₀ := by
  apply tendsto_finsetSum
  intro τ hτ
  have hGO := (mem_growthOrders_iff B f τ).mp
    (Finset.mem_filter.mp hτ).1
  exact continuousAt_orderWeight _ L₀ hdet τ B hBne
    (fun z hz => hGO.not_mem_roots hz) hGO.1

theorem continuousAt_completionFactor (L₀ : Matrix V V ℝ)
    (hdet : ∀ U : Finset V, U.Nonempty → U ≠ univ →
      (Foundation.principal L₀ U).det ≠ 0)
    (B : Finset V) (hB : B ≠ univ) (f : ParentAssignment B)
    (r : B) :
    ContinuousAt
      (fun L : Matrix V V ℝ => completionFactor L B f r) L₀ := by
  apply tendsto_finsetSum
  intro i _
  exact (continuousAt_orderMass L₀ hdet B ⟨r, r.2⟩ f i).mul
    (continuousAt_inv_principal B L₀ (hdet B ⟨r, r.2⟩ hB) i r)

/-! ## The perturbed chain -/

/-- The matrix `P_ε = (1 - ε) P + ε 𝟏𝟏ᵀ / n`. -/
noncomputable def perturb (P : Matrix V V ℝ) (ε : ℝ) :
    Matrix V V ℝ :=
  fun u v => (1 - ε) * P u v + ε / Fintype.card V

omit [DecidableEq V] in
theorem perturb_zero (P : Matrix V V ℝ) : perturb P 0 = P := by
  funext u v
  simp [perturb]

omit [DecidableEq V] in
theorem perturb_pos {P : Matrix V V ℝ} (hP : IsStochastic P)
    [Nonempty V] {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (u v : V) :
    0 < perturb P ε u v := by
  have hn : (0 : ℝ) < Fintype.card V :=
    Nat.cast_pos.mpr Fintype.card_pos
  have h2 : 0 ≤ (1 - ε) * P u v :=
    mul_nonneg (by linarith) (hP.nonneg u v)
  have h3 : 0 < ε / Fintype.card V := div_pos h0 hn
  simp only [perturb]
  linarith

omit [DecidableEq V] in
theorem perturb_isStochastic {P : Matrix V V ℝ} (hP : IsStochastic P)
    [Nonempty V] {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    IsStochastic (perturb P ε) where
  nonneg u v := (perturb_pos hP h0 h1 u v).le
  row_sum u := by
    have hn : (Fintype.card V : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp only [perturb, Finset.sum_add_distrib, ← Finset.mul_sum,
      hP.row_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    ring

theorem perturb_isIrreducible {P : Matrix V V ℝ} (hP : IsStochastic P)
    [Nonempty V] {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    IsIrreducible (perturb P ε) := by
  intro u v
  refine ⟨1, ?_⟩
  rw [pow_one]
  exact perturb_pos hP h0 h1 u v

omit [DecidableEq V] in
theorem continuous_perturb (P : Matrix V V ℝ) :
    Continuous fun ε : ℝ => perturb P ε := by
  apply continuous_matrix
  intro u v
  simp only [perturb]
  fun_prop

theorem continuous_cofactorVec_perturb (P : Matrix V V ℝ) (v : V) :
    Continuous fun ε : ℝ => cofactorVec (perturb P ε) v := by
  unfold cofactorVec
  apply Continuous.matrix_det
  exact (continuous_principal (univ.erase v)).comp
    (continuous_const.sub (continuous_perturb P))

/-- The stationary distribution of `P_ε`, as its normalized cofactor
vector. -/
noncomputable def perturbPi (P : Matrix V V ℝ) (ε : ℝ) (v : V) : ℝ :=
  cofactorVec (perturb P ε) v / cofactorSum (perturb P ε)

theorem continuousAt_perturbPi (P : Matrix V V ℝ)
    (hΛ : cofactorSum P ≠ 0) (v : V) :
    ContinuousAt (fun ε : ℝ => perturbPi P ε v) 0 := by
  unfold perturbPi
  apply ContinuousAt.div
  · exact (continuous_cofactorVec_perturb P v).continuousAt
  · unfold cofactorSum
    exact (continuous_finsetSum _ fun u _ =>
      continuous_cofactorVec_perturb P u).continuousAt
  · rw [perturb_zero]
    exact hΛ

variable {P : Matrix V V ℝ} {π : V → ℝ}

theorem perturbPi_zero (hP : IsStochastic P) (hirr : IsIrreducible P)
    (hπ : IsStationary P π) (hcard : 2 ≤ Fintype.card V) :
    perturbPi P 0 = π := by
  funext v
  have hΛ : cofactorSum P ≠ 0 := (cofactorSum_pos hP hirr hcard).ne'
  rw [perturbPi, perturb_zero, hπ.cofactorVec_eq hP hirr hcard v]
  field_simp

/-- The matrix `L_ε = I - P_ε*`. -/
noncomputable def perturbL (P : Matrix V V ℝ) (ε : ℝ) :
    Matrix V V ℝ :=
  reversedMatrix (perturb P ε) (perturbPi P ε)

theorem continuousAt_perturbL (hP : IsStochastic P)
    (hirr : IsIrreducible P) (hπ : IsStationary P π)
    (hcard : 2 ≤ Fintype.card V) :
    ContinuousAt (fun ε : ℝ => perturbL P ε) 0 := by
  have hΛ : cofactorSum P ≠ 0 := (cofactorSum_pos hP hirr hcard).ne'
  apply continuousAt_pi.mpr
  intro u
  apply continuousAt_pi.mpr
  intro v
  have hform : (fun ε : ℝ => perturbL P ε u v) = fun ε =>
      (1 : Matrix V V ℝ) u v -
        perturbPi P ε v * perturb P ε v u / perturbPi P ε u := by
    funext ε
    simp only [perturbL, reversedMatrix, Matrix.sub_apply,
      reversal_apply]
  rw [hform]
  apply ContinuousAt.sub continuousAt_const
  apply ContinuousAt.div
  · exact (continuousAt_perturbPi P hΛ v).mul
      ((continuous_entry v u).comp
        (continuous_perturb P)).continuousAt
  · exact continuousAt_perturbPi P hΛ u
  · rw [perturbPi_zero hP hirr hπ hcard]
    exact (hπ.pos u).ne'

variable [MeasurableSpace V] [MeasurableSingletonClass V]

/-- **Equation `eq:completion-weight`.** The total weight of the
arborescences rooted at the seed `r` that complete the forest `f`.
The forest weight may vanish. -/
theorem sum_completionWeight (hP : IsStochastic P)
    (hirr : IsIrreducible P) (hπ : IsStationary P π)
    (hcard : 2 ≤ Fintype.card V) (B : Finset V) (hB : B ≠ univ)
    (r : B) (f : ParentAssignment B) :
    ∑ h ∈ completions B r r.2 f, completionWeight P π B r h =
      (Foundation.principal (reversedMatrix P π) B).det *
        (∏ j ∈ B \ {(r : V)}, π j) *
        completionFactor (reversedMatrix P π) B f r := by
  classical
  haveI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hΛ : cofactorSum P ≠ 0 := (cofactorSum_pos hP hirr hcard).ne'
  let G : ℝ → ℝ := fun ε =>
    ∑ h ∈ completions B r r.2 f,
      completionWeight (perturb P ε) (perturbPi P ε) B r h
  let H : ℝ → ℝ := fun ε =>
    (Foundation.principal (perturbL P ε) B).det *
      (∏ j ∈ B \ {(r : V)}, perturbPi P ε j) *
      completionFactor (perturbL P ε) B f r
  -- The identity for the perturbed chain.
  have hpositive : ∀ ε ∈ Set.Ioo (0 : ℝ) 1, G ε = H ε := by
    intro ε hε
    have hPε := perturb_isStochastic hP hε.1 hε.2
    have hirrε := perturb_isIrreducible hP hε.1 hε.2
    have hπε : IsStationary (perturb P ε) (perturbPi P ε) :=
      isStationary_cofactor hPε hirrε hcard
    apply sum_completionWeight_of_pos hPε hirrε hπε hcard B hB r f
    exact Finset.prod_pos fun v _ =>
      mul_pos (hπε.pos _) (perturb_pos hP hε.1 hε.2 _ _)
  -- Continuity of both sides at `ε = 0`.
  have hG : ContinuousAt G 0 := by
    apply tendsto_finsetSum
    intro h _
    apply tendsto_finsetProd
    intro j _
    exact (continuousAt_perturbPi P hΛ _).mul
      ((continuous_entry _ _).comp
        (continuous_perturb P)).continuousAt
  have hL0 : perturbL P 0 = reversedMatrix P π := by
    rw [perturbL, perturb_zero, perturbPi_zero hP hirr hπ hcard]
  have hdet0 : ∀ U : Finset V, U.Nonempty → U ≠ univ →
      (Foundation.principal (perturbL P 0) U).det ≠ 0 := by
    intro U hUne hU
    rw [hL0]
    exact (det_principal_reversedMatrix_pos hP hirr hπ U hUne hU).ne'
  have hLcont := continuousAt_perturbL hP hirr hπ hcard
  have hH : ContinuousAt H 0 := by
    apply ContinuousAt.mul
    · apply ContinuousAt.mul
      · exact (continuousAt_det_principal B (perturbL P 0)).comp
          hLcont
      · apply tendsto_finsetProd
        intro j _
        exact continuousAt_perturbPi P hΛ j
    · exact (continuousAt_completionFactor (perturbL P 0) hdet0 B hB
        f r).comp hLcont
  -- The two limits from the right agree.
  have heq : G 0 = H 0 := by
    have hGlim : Tendsto G (𝓝[>] 0) (𝓝 (G 0)) :=
      hG.tendsto.mono_left nhdsWithin_le_nhds
    have hHlim : Tendsto H (𝓝[>] 0) (𝓝 (H 0)) :=
      hH.tendsto.mono_left nhdsWithin_le_nhds
    apply tendsto_nhds_unique_of_eventuallyEq hGlim hHlim
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)]
      with ε hε
    exact hpositive ε hε
  have hG0 : G 0 =
      ∑ h ∈ completions B r r.2 f, completionWeight P π B r h := by
    simp only [G]
    rw [perturb_zero, perturbPi_zero hP hirr hπ hcard]
  have hH0 : H 0 =
      (Foundation.principal (reversedMatrix P π) B).det *
        (∏ j ∈ B \ {(r : V)}, π j) *
        completionFactor (reversedMatrix P π) B f r := by
    simp only [H]
    rw [hL0, perturbPi_zero hP hirr hπ hcard]
  rw [← hG0, heq, hH0]

/-- **Theorem `thm:stopped`.** The law of the first-entrance forest
of the stopped covering walk from the seed `r ∈ B`, and the total
weight of the arborescences that complete a forest. -/
theorem stopped_forest_law (hP : IsStochastic P)
    (hirr : IsIrreducible P) (hπ : IsStationary P π)
    (hcard : 2 ≤ Fintype.card V) (B : Finset V) (hB : B ≠ univ)
    (r : B) (f : ParentAssignment B) :
    chainLaw P hP r (forestEvent B f) =
        ENNReal.ofReal
          ((Foundation.principal (reversedMatrix P π) B).det /
              (π r * (∏ v ∈ univ \ B, π v) * cofactorSum P) *
            forestWeight P π B f *
            completionFactor (reversedMatrix P π) B f r) ∧
      ∑ h ∈ completions B r r.2 f, completionWeight P π B r h =
        (Foundation.principal (reversedMatrix P π) B).det *
          (∏ j ∈ B \ {(r : V)}, π j) *
          completionFactor (reversedMatrix P π) B f r :=
  ⟨chainLaw_forestEvent_eq hP hirr hπ hcard B hB r f,
    sum_completionWeight hP hirr hπ hcard B hB r f⟩

end EAB.Paper.Chain
