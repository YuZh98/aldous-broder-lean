import EAB.Paper.AggregationFoundation

/-!
# One-vertex transfer

This module proves the general algebraic transfer before specializing to forests.
-/

open Finset Matrix

namespace EAB.Paper.Foundation

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {K : Type*} [Field K]

/-- Fold the new-root column and row into the old base using a vector
whose coordinates sum to one. -/
noncomputable def fold (U : Finset W) (w : W) (_hw : w ∉ U)
    (M' : Matrix (univ \ insert w U : Finset W) (insert w U : Finset W) K)
    (θ : U → K) : Matrix (univ \ U : Finset W) U K :=
  fun v j =>
    if h : (v : W) = w then θ j
    else
      let v' : (univ \ insert w U : Finset W) :=
        ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ (v : W), by
          have hvU : (v : W) ∉ U := (Finset.mem_sdiff.mp v.2).2
          simp [Finset.mem_insert, h, hvU]⟩⟩
      M' v' ⟨j, Finset.mem_insert_of_mem j.2⟩ +
        M' v' ⟨w, Finset.mem_insert_self w U⟩ * θ j

theorem fold_at_new_vertex (U : Finset W) (w : W) (hw : w ∉ U)
    (M' : Matrix (univ \ insert w U : Finset W) (insert w U : Finset W) K)
    (θ : U → K) (j : U) :
    fold U w hw M' θ
      ⟨w, Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hw⟩⟩ j = θ j := by
  simp [fold]

theorem fold_at_old_boundary (U : Finset W) (w : W) (hw : w ∉ U)
    (M' : Matrix (univ \ insert w U : Finset W) (insert w U : Finset W) K)
    (θ : U → K) (v : W) (hv : v ∉ insert w U) (j : U) :
    fold U w hw M' θ
      ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ v,
        fun h => hv (Finset.mem_insert_of_mem h)⟩⟩ j =
      M' ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hv⟩⟩
        ⟨j, Finset.mem_insert_of_mem j.2⟩ +
      M' ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hv⟩⟩
        ⟨w, Finset.mem_insert_self w U⟩ * θ j := by
  have hvw : v ≠ w := fun h => hv (h ▸ Finset.mem_insert_self w U)
  simp [fold, hvw]

/- Decompose a sum over a base enlarged by one vertex. -/
omit [Fintype W] in
private theorem sum_insert_subtype (U : Finset W) (w : W) (hw : w ∉ U)
    (φ : ↥(insert w U) → K) :
    (∑ j : ↥(insert w U), φ j) =
      φ ⟨w, Finset.mem_insert_self w U⟩ +
        ∑ j : U, φ ⟨j, Finset.mem_insert_of_mem j.2⟩ := by
  classical
  let F : W → K := fun j =>
    if h : j ∈ insert w U then φ ⟨j, h⟩ else 0
  have hleft : (∑ j : ↥(insert w U), φ j) =
      ∑ j ∈ insert w U, F j := by
    calc
      (∑ j : ↥(insert w U), φ j)
          = ∑ j : ↥(insert w U), F j := by
              apply Finset.sum_congr rfl
              intro j _
              change φ j =
                (if h : (j : W) ∈ insert w U then φ ⟨j, h⟩ else 0)
              rw [dif_pos j.2]
      _ = ∑ j ∈ insert w U, F j :=
            Finset.sum_coe_sort (insert w U) F
  have hright : (∑ j : U, φ ⟨j, Finset.mem_insert_of_mem j.2⟩) =
      ∑ j ∈ U, F j := by
    calc
      (∑ j : U, φ ⟨j, Finset.mem_insert_of_mem j.2⟩)
          = ∑ j : U, F j := by
              apply Finset.sum_congr rfl
              intro j _
              change φ ⟨j, Finset.mem_insert_of_mem j.2⟩ =
                (if h : (j : W) ∈ insert w U then φ ⟨j, h⟩ else 0)
              rw [dif_pos (Finset.mem_insert_of_mem j.2)]
      _ = ∑ j ∈ U, F j := Finset.sum_coe_sort U F
  calc
    (∑ j : ↥(insert w U), φ j)
        = ∑ j ∈ insert w U, F j := hleft
    _ = F w + ∑ j ∈ U, F j := Finset.sum_insert hw
    _ = φ ⟨w, Finset.mem_insert_self w U⟩ +
          ∑ j : U, φ ⟨j, Finset.mem_insert_of_mem j.2⟩ := by
            rw [hright]
            simp [F]

/-- Folding preserves unit row sums. -/
theorem fold_unitRowSums (U : Finset W) (w : W) (hw : w ∉ U)
    (M' : Matrix (univ \ insert w U : Finset W) (insert w U : Finset W) K)
    (θ : U → K) (hθ : ∑ j : U, θ j = 1)
    (hM' : UnitRowSums (insert w U) M') :
    UnitRowSums U (fold U w hw M' θ) := by
  classical
  intro v
  by_cases hvw : (v : W) = w
  · have heq : v = (⟨w, Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ w, hw⟩⟩ : (univ \ U : Finset W)) :=
      Subtype.ext hvw
    subst v
    simpa only [fold_at_new_vertex] using hθ
  · have hvU : (v : W) ∉ U := (Finset.mem_sdiff.mp v.2).2
    have hvU' : (v : W) ∉ insert w U := by
      simp [Finset.mem_insert, hvw, hvU]
    let v' : (univ \ insert w U : Finset W) :=
      ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ (v : W), hvU'⟩⟩
    let w' : (insert w U : Finset W) :=
      ⟨w, Finset.mem_insert_self w U⟩
    calc
      (∑ j : U, fold U w hw M' θ v j)
          = ∑ j : U,
              (M' v' ⟨j, Finset.mem_insert_of_mem j.2⟩ +
                M' v' w' * θ j) := by
              apply Finset.sum_congr rfl
              intro j _
              exact fold_at_old_boundary U w hw M' θ v hvU' j
      _ = (∑ j : U, M' v' ⟨j, Finset.mem_insert_of_mem j.2⟩) +
            M' v' w' * ∑ j : U, θ j := by
              rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = ∑ j : (insert w U : Finset W), M' v' j := by
            rw [sum_insert_subtype U w hw (M' v')]
            rw [hθ]
            ring
      _ = 1 := hM' v'

/-- The paper's one-vertex harmonic update for each column of `M'`. -/
theorem harmonic_extended_column (L : Matrix W W K)
    (U : Finset W) (w : W) (hw : w ∉ U)
    (hdetU : (principal L U).det ≠ 0)
    (hdetU' : (principal L (insert w U)).det ≠ 0)
    (M' : Matrix (univ \ insert w U : Finset W) (insert w U : Finset W) K)
    (j : ↥(insert w U)) :
    harmonic L (insert w U) (fun v => M' v j) =
      harmonic L U (extendZero U w (fun v => M' v j)) +
        harmonic L (insert w U) (fun v => M' v j) w •
          gamma L U w :=
  harmonic_one_step L U w hw hdetU hdetU' (fun v => M' v j)

/-- The matrix `Ĝ` in the two-determinant proof of one-vertex transfer. -/
noncomputable def transferG (L : Matrix W W K) (U : Finset W) (w : W)
    (M' : Matrix (univ \ insert w U : Finset W) (insert w U : Finset W) K) :
    Matrix (insert w U : Finset W) (insert w U : Finset W) K :=
  fun x j => harmonic L U (extendZero U w (fun v => M' v j)) x

noncomputable def transferRho (L : Matrix W W K) (U : Finset W) (w : W)
    (M' : Matrix (univ \ insert w U : Finset W) (insert w U : Finset W) K) :
    ↥(insert w U) → K :=
  fun j => harmonic L (insert w U) (fun v => M' v j) w

/-- `N' = (I - Ĝ) - a ρᵀ`, with `a = γ^{U,w}|_{U'}`. -/
theorem aggregation_rank_one_decomposition (L : Matrix W W K)
    (U : Finset W) (w : W) (hw : w ∉ U)
    (hdetU : (principal L U).det ≠ 0)
    (hdetU' : (principal L (insert w U)).det ≠ 0)
    (M' : Matrix (univ \ insert w U : Finset W) (insert w U : Finset W) K) :
    aggregation L (insert w U) M' =
      1 - transferG L U w M' -
        Matrix.of (fun (x j : ↥(insert w U)) =>
          gamma L U w x * transferRho L U w M' j) := by
  classical
  funext x j
  have hstep := congrFun
    (harmonic_extended_column L U w hw hdetU hdetU' M' j) (x : W)
  simp only [aggregation_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.of_apply, transferG, transferRho]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hstep
  rw [hstep]
  ring

/-- The coefficients in the rank-one decomposition sum to one. -/
theorem transferRho_sum_one (L : Matrix W W K)
    (U : Finset W) (w : W)
    (hL : L *ᵥ (fun _ => 1) = 0)
    (hdetU' : (principal L (insert w U)).det ≠ 0)
    (M' : Matrix (univ \ insert w U : Finset W) (insert w U : Finset W) K)
    (hM' : UnitRowSums (insert w U) M') :
    (∑ j : ↥(insert w U), transferRho L U w M' j) = 1 := by
  have hsum := congrFun
    (harmonic_sum L (insert w U) hdetU' Finset.univ
      (fun j : ↥(insert w U) => fun v => M' v j)) w
  have hb : (∑ j : ↥(insert w U),
      (fun v : (univ \ insert w U : Finset W) => M' v j)) =
      (fun _ => (1 : K)) := by
    funext v
    simpa only [Finset.sum_apply] using hM' v
  rw [hb, harmonic_one L (insert w U) hL hdetU'] at hsum
  simpa only [transferRho, Finset.sum_apply] using hsum.symm

/-- The new row of `Ĝ` is zero. -/
theorem transferG_new_row_zero (L : Matrix W W K)
    (U : Finset W) (w : W) (hw : w ∉ U)
    (M' : Matrix (univ \ insert w U : Finset W) (insert w U : Finset W) K)
    (j : ↥(insert w U)) :
    transferG L U w M' ⟨w, Finset.mem_insert_self w U⟩ j = 0 := by
  unfold transferG
  let wU : (univ \ U : Finset W) :=
    ⟨w, Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hw⟩⟩
  have h := harmonic_boundary L U
    (extendZero U w (fun v => M' v j)) wU
  simpa [wU, extendZero] using h

/-- First evaluation of the determinant `D = det(I - Ĝ)` in the
general transfer proof. -/
theorem transfer_left_determinant (L : Matrix W W K)
    (U : Finset W) (w : W) (hw : w ∉ U)
    (hL : L *ᵥ (fun _ => 1) = 0)
    (hdetU : (principal L U).det ≠ 0)
    (hdetU' : (principal L (insert w U)).det ≠ 0)
    (M' : Matrix (univ \ insert w U : Finset W) (insert w U : Finset W) K)
    (hM' : UnitRowSums (insert w U) M') :
    ((1 : Matrix (insert w U : Finset W) (insert w U : Finset W) K) -
      transferG L U w M').det =
      ∑ x : ↥(insert w U), gamma L U w x *
        principalCofactor (insert w U) (aggregation L (insert w U) M') x := by
  classical
  let N' := aggregation L (insert w U) M'
  let a : ↥(insert w U) → K := fun x => gamma L U w x
  let ρ : ↥(insert w U) → K := transferRho L U w M'
  have hrow : N' *ᵥ (fun _ => 1) = 0 :=
    aggregation_zero_row_sum L (insert w U) M' hL hdetU' hM'
  have hnonempty : (insert w U).Nonempty :=
    ⟨w, Finset.mem_insert_self w U⟩
  have hrel :
      (1 : Matrix (insert w U : Finset W) (insert w U : Finset W) K) -
        transferG L U w M' =
          N' + Matrix.of (fun (x j : ↥(insert w U)) => a x * ρ j) := by
    dsimp only [N', a, ρ]
    rw [aggregation_rank_one_decomposition L U w hw hdetU hdetU' M']
    funext x j
    simp [Matrix.sub_apply, Matrix.add_apply,
      Matrix.one_apply, Matrix.of_apply]
  calc
    ((1 : Matrix (insert w U : Finset W) (insert w U : Finset W) K) -
        transferG L U w M').det
        = (N' + Matrix.of (fun (x j : ↥(insert w U)) => a x * ρ j)).det :=
            congrArg Matrix.det hrel
    _ = (∑ j : ↥(insert w U), ρ j) *
          (∑ x : ↥(insert w U), a x * principalCofactor (insert w U) N' x) :=
            det_add_rank_one_zero_row_sum (insert w U) N' hnonempty hrow a ρ
    _ = ∑ x : ↥(insert w U), gamma L U w x *
          principalCofactor (insert w U) (aggregation L (insert w U) M') x := by
            rw [show (∑ j : ↥(insert w U), ρ j) = 1 from
              transferRho_sum_one L U w hL hdetU' M' hM']
            simp [N', a]

/-- The other evaluation starts by expanding the determinant along
the row of the newly added vertex. -/
theorem transfer_determinant_drop (L : Matrix W W K)
    (U : Finset W) (w : W) (hw : w ∉ U)
    (M' : Matrix (univ \ insert w U : Finset W) (insert w U : Finset W) K) :
    ((1 : Matrix (insert w U : Finset W) (insert w U : Finset W) K) -
      transferG L U w M').det =
      (eraseMinor (insert w U)
        ((1 : Matrix (insert w U : Finset W) (insert w U : Finset W) K) -
          transferG L U w M')
        ⟨w, Finset.mem_insert_self w U⟩).det := by
  classical
  apply det_drop_coordinate_row
  intro j
  rw [Matrix.sub_apply, Matrix.one_apply,
    transferG_new_row_zero L U w hw M' j]
  by_cases hj : j = ⟨w, Finset.mem_insert_self w U⟩ <;> simp [hj, eq_comm]

/-- The boundary vector `s̃ + e_w` from the fold identity. -/
noncomputable def transferBoundary (U : Finset W) (w : W) (hw : w ∉ U)
    (M' : Matrix (univ \ insert w U : Finset W) (insert w U : Finset W) K) :
    (univ \ U : Finset W) → K :=
  extendZero U w (fun v => M' v ⟨w, Finset.mem_insert_self w U⟩) +
    Pi.single ⟨w, Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hw⟩⟩ 1

/-- Column identity for the general fold. -/
theorem fold_column (U : Finset W) (w : W) (hw : w ∉ U)
    (M' : Matrix (univ \ insert w U : Finset W) (insert w U : Finset W) K)
    (θ : U → K) (j : U) :
    extendZero U w (fun v => M' v ⟨j, Finset.mem_insert_of_mem j.2⟩) =
      (fun v => fold U w hw M' θ v j) -
        θ j • transferBoundary U w hw M' := by
  classical
  funext v
  change extendZero U w
      (fun x => M' x ⟨j, Finset.mem_insert_of_mem j.2⟩) v =
    fold U w hw M' θ v j - θ j * transferBoundary U w hw M' v
  by_cases hvw : (v : W) = w
  · have heq : v = (⟨w, Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ w, hw⟩⟩ : (univ \ U : Finset W)) :=
      Subtype.ext hvw
    subst v
    simp [extendZero, fold, transferBoundary, Pi.add_apply]
  · have hvU : (v : W) ∉ U := (Finset.mem_sdiff.mp v.2).2
    have hvU' : (v : W) ∉ insert w U := by
      simp [Finset.mem_insert, hvw, hvU]
    rw [extendZero_at_old_boundary U w _ v hvU',
      fold_at_old_boundary U w hw M' θ v hvU' j]
    simp [transferBoundary, Pi.add_apply,
      extendZero_at_old_boundary U w _ v hvU']
    have hvv : v ≠ (⟨w, Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ w, hw⟩⟩ : (univ \ U : Finset W)) :=
      fun h => hvw (congrArg Subtype.val h)
    simp [hvv]
    ring

/-- After deleting the coordinate row, the remaining determinant is
indexed by the old base `U`. -/
theorem transfer_determinant_on_old_base (L : Matrix W W K)
    (U : Finset W) (w : W) (hw : w ∉ U)
    (M' : Matrix (univ \ insert w U : Finset W) (insert w U : Finset W) K) :
    ((1 : Matrix (insert w U : Finset W) (insert w U : Finset W) K) -
      transferG L U w M').det =
      (Matrix.of (fun (i j : U) =>
        ((1 : Matrix (insert w U : Finset W) (insert w U : Finset W) K) -
          transferG L U w M')
          ⟨i, Finset.mem_insert_of_mem i.2⟩
          ⟨j, Finset.mem_insert_of_mem j.2⟩)).det := by
  let e : ↥U ≃ ↥((insert w U).erase w) :=
    { toFun := fun i => ⟨i, by simp [Finset.erase_insert hw, i.2]⟩
      invFun := fun i => ⟨i, by simpa [Finset.erase_insert hw] using i.2⟩
      left_inv := by intro i; cases i; rfl
      right_inv := by intro i; cases i; rfl }
  let A : Matrix (insert w U : Finset W) (insert w U : Finset W) K :=
    1 - transferG L U w M'
  calc
    A.det = (eraseMinor (insert w U) A
      ⟨w, Finset.mem_insert_self w U⟩).det :=
      transfer_determinant_drop L U w hw M'
    _ = ((eraseMinor (insert w U) A
      ⟨w, Finset.mem_insert_self w U⟩).submatrix e e).det :=
      (Matrix.det_submatrix_equiv_self e _).symm
    _ = (Matrix.of (fun (i j : U) => A
          ⟨i, Finset.mem_insert_of_mem i.2⟩
          ⟨j, Finset.mem_insert_of_mem j.2⟩)).det := by
      congr 1

/-- The old-base minor is the folded aggregation matrix plus the
rank-one correction in the paper proof. -/
theorem transfer_old_block (L : Matrix W W K)
    (U : Finset W) (w : W) (hw : w ∉ U)
    (hdetU : (principal L U).det ≠ 0)
    (M' : Matrix (univ \ insert w U : Finset W) (insert w U : Finset W) K)
    (θ : U → K) :
    Matrix.of (fun (i j : U) =>
      ((1 : Matrix (insert w U : Finset W) (insert w U : Finset W) K) -
        transferG L U w M')
        ⟨i, Finset.mem_insert_of_mem i.2⟩
        ⟨j, Finset.mem_insert_of_mem j.2⟩) =
      aggregation L U (fold U w hw M' θ) +
        Matrix.of (fun (i j : U) =>
          harmonic L U (transferBoundary U w hw M') i * θ j) := by
  classical
  funext i j
  have hcolumn : (fun v => fold U w hw M' θ v j) =
      extendZero U w (fun v => M' v
        ⟨j, Finset.mem_insert_of_mem j.2⟩) +
        θ j • transferBoundary U w hw M' := by
    exact (eq_sub_iff_add_eq.mp (fold_column U w hw M' θ j)).symm
  have hharm := congrArg (harmonic L U) hcolumn
  rw [harmonic_add L U _ _ hdetU,
    harmonic_smul L U _ _ hdetU] at hharm
  have hentry := congrFun hharm (i : W)
  simp only [Matrix.of_apply, Matrix.add_apply, Matrix.sub_apply,
    Matrix.one_apply, transferG, aggregation_apply]
  rw [hentry]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [Subtype.ext_iff]
  ring

/-- Second evaluation of `D = det(I - Ĝ)`, now on the old base. -/
theorem transfer_right_determinant (L : Matrix W W K)
    (U : Finset W) (hU : U.Nonempty) (w : W) (hw : w ∉ U)
    (hL : L *ᵥ (fun _ => 1) = 0)
    (hdetU : (principal L U).det ≠ 0)
    (M' : Matrix (univ \ insert w U : Finset W) (insert w U : Finset W) K)
    (hM' : UnitRowSums (insert w U) M')
    (θ : U → K) (hθ : ∑ j : U, θ j = 1) :
    ((1 : Matrix (insert w U : Finset W) (insert w U : Finset W) K) -
      transferG L U w M').det =
      ∑ x : U, harmonic L U (transferBoundary U w hw M') x *
        principalCofactor U (aggregation L U (fold U w hw M' θ)) x := by
  classical
  let N := aggregation L U (fold U w hw M' θ)
  let a : U → K := fun x => harmonic L U (transferBoundary U w hw M') x
  have hrow : N *ᵥ (fun _ => 1) = 0 :=
    aggregation_zero_row_sum L U (fold U w hw M' θ) hL hdetU
      (fold_unitRowSums U w hw M' θ hθ hM')
  calc
    ((1 : Matrix (insert w U : Finset W) (insert w U : Finset W) K) -
      transferG L U w M').det
        = (Matrix.of (fun (i j : U) =>
            ((1 : Matrix (insert w U : Finset W)
              (insert w U : Finset W) K) - transferG L U w M')
              ⟨i, Finset.mem_insert_of_mem i.2⟩
              ⟨j, Finset.mem_insert_of_mem j.2⟩)).det :=
            transfer_determinant_on_old_base L U w hw M'
    _ = (N + Matrix.of (fun (i j : U) => a i * θ j)).det := by
          exact congrArg Matrix.det
            (transfer_old_block L U w hw hdetU M' θ)
    _ = (∑ j : U, θ j) * (∑ x : U, a x * principalCofactor U N x) :=
          det_add_rank_one_zero_row_sum U N hU hrow a θ
    _ = ∑ x : U, harmonic L U (transferBoundary U w hw M') x *
          principalCofactor U (aggregation L U (fold U w hw M' θ)) x := by
            rw [hθ]
            simp [N, a]

/-- The paper's general one-vertex transfer lemma. No forest data or
positivity assumption appears in this statement. The hypothesis
`insert w U ≠ univ` is the paper's `|U| ≤ n - 2`. -/
theorem one_vertex_transfer (L : Matrix W W K)
    (U : Finset W) (hU : U.Nonempty) (w : W) (hw : w ∉ U)
    (_hproper : insert w U ≠ univ)
    (hL : L *ᵥ (fun _ => 1) = 0)
    (hdetU : (principal L U).det ≠ 0)
    (hdetU' : (principal L (insert w U)).det ≠ 0)
    (M' : Matrix (univ \ insert w U : Finset W) (insert w U : Finset W) K)
    (hM' : UnitRowSums (insert w U) M')
    (θ : U → K) (hθ : ∑ j : U, θ j = 1) :
    (∑ x : ↥(insert w U), gamma L U w x *
      principalCofactor (insert w U) (aggregation L (insert w U) M') x) =
    (∑ x : U, harmonic L U (transferBoundary U w hw M') x *
      principalCofactor U (aggregation L U (fold U w hw M' θ)) x) := by
  calc
    (∑ x : ↥(insert w U), gamma L U w x *
      principalCofactor (insert w U) (aggregation L (insert w U) M') x)
        = ((1 : Matrix (insert w U : Finset W)
            (insert w U : Finset W) K) - transferG L U w M').det :=
            (transfer_left_determinant L U w hw hL hdetU hdetU' M' hM').symm
    _ = ∑ x : U, harmonic L U (transferBoundary U w hw M') x *
          principalCofactor U (aggregation L U (fold U w hw M' θ)) x :=
            transfer_right_determinant L U hU w hw hL hdetU M' hM' θ hθ

/-- Transfer onto a one-vertex base. The right side is one harmonic
entry: the old-base determinant is one-by-one and is read as its entry,
so no principal cofactor of a one-by-one matrix is taken. -/
theorem one_vertex_transfer_singleton (L : Matrix W W K)
    (U : Finset W) (hcard : U.card = 1) (r : U) (w : W) (hw : w ∉ U)
    (_hproper : insert w U ≠ univ)
    (hL : L *ᵥ (fun _ => 1) = 0)
    (hdetU : (principal L U).det ≠ 0)
    (hdetU' : (principal L (insert w U)).det ≠ 0)
    (M' : Matrix (univ \ insert w U : Finset W) (insert w U : Finset W) K)
    (hM' : UnitRowSums (insert w U) M') :
    (∑ x : ↥(insert w U), gamma L U w x *
      principalCofactor (insert w U) (aggregation L (insert w U) M') x) =
    harmonic L U (transferBoundary U w hw M') r := by
  classical
  have hcard' : Fintype.card U = 1 := by
    rw [Fintype.card_coe]
    exact hcard
  haveI : Subsingleton U :=
    Fintype.card_le_one_iff_subsingleton.mp hcard'.le
  let θ : U → K := fun _ => 1
  have hθ : ∑ j : U, θ j = 1 := Fintype.sum_subsingleton θ r
  let N := aggregation L U (fold U w hw M' θ)
  have hrow : N *ᵥ (fun _ => 1) = 0 :=
    aggregation_zero_row_sum L U (fold U w hw M' θ) hL hdetU
      (fold_unitRowSums U w hw M' θ hθ hM')
  have hN : N r r = 0 := by
    have h := congrFun hrow r
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, mul_one] at h
    rw [Fintype.sum_subsingleton _ r] at h
    exact h
  calc
    (∑ x : ↥(insert w U), gamma L U w x *
      principalCofactor (insert w U) (aggregation L (insert w U) M') x)
        = ((1 : Matrix (insert w U : Finset W)
            (insert w U : Finset W) K) - transferG L U w M').det :=
            (transfer_left_determinant L U w hw hL hdetU hdetU' M' hM').symm
    _ = (Matrix.of (fun (i j : U) =>
          ((1 : Matrix (insert w U : Finset W)
            (insert w U : Finset W) K) - transferG L U w M')
            ⟨i, Finset.mem_insert_of_mem i.2⟩
            ⟨j, Finset.mem_insert_of_mem j.2⟩)).det :=
          transfer_determinant_on_old_base L U w hw M'
    _ = (N + Matrix.of (fun (i j : U) =>
          harmonic L U (transferBoundary U w hw M') i * θ j)).det :=
          congrArg Matrix.det (transfer_old_block L U w hw hdetU M' θ)
    _ = (N + Matrix.of (fun (i j : U) =>
          harmonic L U (transferBoundary U w hw M') i * θ j)) r r :=
          Matrix.det_eq_elem_of_card_eq_one hcard' r
    _ = harmonic L U (transferBoundary U w hw M') r := by
          simp [hN, θ]

end EAB.Paper.Foundation
