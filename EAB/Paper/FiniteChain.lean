import Mathlib.Algebra.BigOperators.Field
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import EAB.Paper.ConfinedChain
import EAB.Paper.HarmonicFoundation

/-!
# Finite chains: stationary cofactors, reversal, Green identities

Lemmas `lem:stationary` and `lem:green` of the blueprint, with the
objects of Definition `def:chain`: the cofactor vector `λ`, its sum
`Λ`, the reversed kernel `P* = D⁻¹ Pᵀ D`, and the matrix
`L = I - P*`. All statements are about real matrices. No path
probability appears in this file.
-/

open Finset Matrix

namespace EAB.Paper.Chain

open Foundation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Normalized inverse columns -/

section InverseColumn

variable {K : Type*} [Field K]

/-- Cramer's rule on the diagonal: the first identity of
`eq:inverse-ratio`. -/
theorem inv_diag_eq_det_ratio (L : Matrix V V K) (U : Finset V)
    (j : U) :
    (principal L U)⁻¹ j j =
      (principal L (U.erase (j : V))).det / (principal L U).det := by
  rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv',
    ← principalCofactor_eq_adjugate, smul_eq_mul, div_eq_inv_mul]
  rfl

/-- The second identity of `eq:inverse-ratio`: a column of the
inverse of `L[U]`, divided by its diagonal entry, is the harmonic
extension of the coordinate vector at `j` into `U \ {j}`. -/
theorem inv_column_eq_gamma (L : Matrix V V K) (U : Finset V)
    (j : U) (hdetU : (principal L U).det ≠ 0)
    (hdetErase : (principal L (U.erase (j : V))).det ≠ 0) (x : U) :
    (principal L U)⁻¹ x j / (principal L U)⁻¹ j j =
      gamma L (U.erase (j : V)) (j : V) (x : V) := by
  classical
  let d : K := (principal L U)⁻¹ j j
  have hd : d ≠ 0 := by
    change (principal L U)⁻¹ j j ≠ 0
    rw [inv_diag_eq_det_ratio]
    exact div_ne_zero hdetErase hdetU
  let g : V → K := fun v =>
    if hv : v ∈ U then (principal L U)⁻¹ ⟨v, hv⟩ j / d else 0
  have hgU : ∀ u : U, g u = (principal L U)⁻¹ u j / d := by
    intro u
    simp [g, u.2]
  have hboundary : ∀ v : (univ \ U.erase (j : V) : Finset V),
      g v = coordBoundary (K := K) (U.erase (j : V)) (j : V) v := by
    intro v
    have hv : (v : V) ∉ U.erase (j : V) := (Finset.mem_sdiff.mp v.2).2
    by_cases hvj : (v : V) = (j : V)
    · have hvU : (v : V) ∈ U := by
        rw [hvj]
        exact j.2
      have hveq : (⟨(v : V), hvU⟩ : U) = j := Subtype.ext hvj
      simp only [g, dif_pos hvU, coordBoundary, if_pos hvj, hveq]
      exact div_self hd
    · have hvU : (v : V) ∉ U :=
        fun h => hv (Finset.mem_erase.mpr ⟨hvj, h⟩)
      simp [g, hvU, coordBoundary, hvj]
  have hinterior : ∀ i : (U.erase (j : V) : Finset V),
      (L *ᵥ g) i = 0 := by
    intro i
    have hiU : (i : V) ∈ U := Finset.mem_of_mem_erase i.2
    have hij : (⟨(i : V), hiU⟩ : U) ≠ j := fun h =>
      (Finset.mem_erase.mp i.2).1 (congrArg Subtype.val h)
    have hsum : (L *ᵥ g) i =
        ∑ u : U, L i u * ((principal L U)⁻¹ u j / d) := by
      simp only [Matrix.mulVec, dotProduct]
      rw [← Finset.sum_subset (Finset.subset_univ U)]
      · rw [← Finset.sum_coe_sort U (fun v => L i v * g v)]
        exact Finset.sum_congr rfl fun u _ => by rw [hgU u]
      · intro v _ hv
        simp [g, hv]
    have hmul := congrFun (congrFun
      (Matrix.mul_nonsing_inv (principal L U)
        (isUnit_iff_ne_zero.mpr hdetU)) ⟨(i : V), hiU⟩) j
    rw [Matrix.mul_apply, Matrix.one_apply, if_neg hij] at hmul
    have hmul' : ∑ u : U, L i u * (principal L U)⁻¹ u j = 0 := hmul
    rw [hsum]
    simp only [mul_div_assoc', ← Finset.sum_div]
    rw [hmul', zero_div]
  have huniq := harmonic_unique L (U.erase (j : V))
    (coordBoundary (U.erase (j : V)) (j : V)) hdetErase g
    hboundary hinterior
  rw [gamma, ← huniq, hgU x]

end InverseColumn

/-! ## The cofactor vector and the stationary distribution -/

variable {P : Matrix V V ℝ}

theorem principal_one_sub (P : Matrix V V ℝ) (U : Finset V) :
    principal (1 - P) U = 1 - principal P U := by
  funext i j
  simp only [principal, Matrix.submatrix_apply, Matrix.sub_apply,
    Matrix.one_apply]
  by_cases hij : i = j
  · simp [hij]
  · have hne : (i : V) ≠ (j : V) := fun h => hij (Subtype.ext h)
    simp [hij, hne]

/-- The principal cofactor `λ_v = det ((I - P)[V \ {v}])`. -/
noncomputable def cofactorVec (P : Matrix V V ℝ) (v : V) : ℝ :=
  (principal (1 - P) (univ.erase v)).det

/-- The sum `Λ` of the principal cofactors. -/
noncomputable def cofactorSum (P : Matrix V V ℝ) : ℝ :=
  ∑ v, cofactorVec P v

theorem erase_nonempty_and_proper
    (hcard : 2 ≤ Fintype.card V) (v : V) :
    (univ.erase v : Finset V).Nonempty ∧ univ.erase v ≠ univ := by
  constructor
  · rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ v),
      Finset.card_univ]
    omega
  · intro h
    have hv : v ∈ (univ.erase v : Finset V) := by
      rw [h]
      exact Finset.mem_univ v
    exact Finset.notMem_erase v univ hv

theorem cofactorVec_pos (hP : IsStochastic P) (hirr : IsIrreducible P)
    (hcard : 2 ≤ Fintype.card V) (v : V) : 0 < cofactorVec P v := by
  rw [cofactorVec, principal_one_sub]
  exact confined_det_pos hP hirr _
    (erase_nonempty_and_proper hcard v).1
    (erase_nonempty_and_proper hcard v).2

theorem cofactorSum_pos (hP : IsStochastic P) (hirr : IsIrreducible P)
    (hcard : 2 ≤ Fintype.card V) : 0 < cofactorSum P := by
  have hne : (univ : Finset V).Nonempty :=
    Finset.card_pos.mp (by rw [Finset.card_univ]; omega)
  exact Finset.sum_pos (fun v _ => cofactorVec_pos hP hirr hcard v) hne

/-- `λᵀ (I - P) = 0`, by Lemma `lem:cofactor` for the zero-row-sum
matrix `I - P`. -/
theorem cofactorVec_vecMul (hP : IsStochastic P) :
    cofactorVec P ᵥ* (1 - P) = 0 := by
  classical
  funext j
  let A : Matrix (univ : Finset V) (univ : Finset V) ℝ :=
    principal (1 - P) univ
  have hrow : A *ᵥ (fun _ => 1) = 0 := by
    funext i
    have hsum : ∑ v, (1 - P) (i : V) v = 0 := by
      simp [Matrix.sub_apply, Finset.sum_sub_distrib, Matrix.one_apply,
        hP.row_sum]
    rw [← Finset.sum_coe_sort univ (fun v => (1 - P) (i : V) v)] at hsum
    simpa [A, principal, Matrix.mulVec, dotProduct] using hsum
  have hker := principalCofactor_left_kernel univ A ⟨j, Finset.mem_univ j⟩
    hrow
  have hj := congrFun hker ⟨j, Finset.mem_univ j⟩
  have hd : ∀ i : (univ : Finset V),
      principalCofactor univ A i = cofactorVec P i := fun _ => rfl
  simp only [Matrix.vecMul, dotProduct, hd, Pi.zero_apply] at hj ⊢
  rw [← Finset.sum_coe_sort univ
    (fun v => cofactorVec P v * (1 - P) v j)]
  exact hj

/-- A stationary distribution: positive, normalized, invariant. -/
structure IsStationary (P : Matrix V V ℝ) (π : V → ℝ) : Prop where
  pos : ∀ v, 0 < π v
  sum_one : ∑ v, π v = 1
  invariant : π ᵥ* P = π

theorem vecMul_one_sub_eq_zero_iff (P : Matrix V V ℝ)
    (μ : V → ℝ) : μ ᵥ* (1 - P) = 0 ↔ μ ᵥ* P = μ := by
  rw [Matrix.vecMul_sub, Matrix.vecMul_one, sub_eq_zero, eq_comm]

/-- Lemma `lem:stationary`, existence: `λ / Λ` is a stationary
distribution. -/
theorem isStationary_cofactor (hP : IsStochastic P)
    (hirr : IsIrreducible P) (hcard : 2 ≤ Fintype.card V) :
    IsStationary P (fun v => cofactorVec P v / cofactorSum P) where
  pos v := div_pos (cofactorVec_pos hP hirr hcard v)
    (cofactorSum_pos hP hirr hcard)
  sum_one := by
    rw [← Finset.sum_div]
    exact div_self (cofactorSum_pos hP hirr hcard).ne'
  invariant := by
    have hlam : cofactorVec P ᵥ* P = cofactorVec P :=
      (vecMul_one_sub_eq_zero_iff P _).mp (cofactorVec_vecMul hP)
    funext j
    have hj := congrFun hlam j
    simp only [Matrix.vecMul, dotProduct] at hj ⊢
    rw [← hj, Finset.sum_div]
    exact Finset.sum_congr rfl fun v _ => by ring

/-- Lemma `lem:stationary`, uniqueness. The minor of `I - P` on
`V \ {v₀}` is nonzero, so a vector of the left kernel of `I - P` that
vanishes at `v₀` is zero. Hence the left kernel is one-dimensional
and the normalization determines the stationary distribution. -/
theorem IsStationary.cofactorVec_eq {π : V → ℝ}
    (hπ : IsStationary P π) (hP : IsStochastic P)
    (hirr : IsIrreducible P) (hcard : 2 ≤ Fintype.card V) (v : V) :
    cofactorVec P v = π v * cofactorSum P := by
  classical
  obtain ⟨v₀⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hlam0 : cofactorVec P v₀ ≠ 0 :=
    (cofactorVec_pos hP hirr hcard v₀).ne'
  let c : ℝ := π v₀ / cofactorVec P v₀
  let μ : V → ℝ := fun u => π u - c * cofactorVec P u
  have hμ0 : μ v₀ = 0 := by
    simp only [μ, c]
    field_simp
    ring
  have hμker : μ ᵥ* (1 - P) = 0 := by
    have h1 : π ᵥ* (1 - P) = 0 :=
      (vecMul_one_sub_eq_zero_iff P π).mpr hπ.invariant
    have h2 := cofactorVec_vecMul hP
    funext j
    have h1j := congrFun h1 j
    have h2j := congrFun h2 j
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at h1j h2j ⊢
    calc
      ∑ u, μ u * (1 - P) u j
          = ∑ u, π u * (1 - P) u j -
              c * ∑ u, cofactorVec P u * (1 - P) u j := by
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun u _ => by
              simp only [μ]
              ring
      _ = 0 := by rw [h1j, h2j]; ring
  let U : Finset V := univ.erase v₀
  have hdet : (principal (1 - P) U).det ≠ 0 := hlam0
  have hrestrict :
      (fun u : U => μ u) ᵥ* principal (1 - P) U = 0 := by
    funext j
    have hj := congrFun hμker (j : V)
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at hj ⊢
    have hsplit : ∑ u ∈ U, μ u * (1 - P) u j =
        ∑ u, μ u * (1 - P) u j :=
      Finset.sum_erase _ (by rw [hμ0, zero_mul])
    rw [← hj, ← hsplit,
      ← Finset.sum_coe_sort U (fun u => μ u * (1 - P) u j)]
    rfl
  have hzeroU := Matrix.eq_zero_of_vecMul_eq_zero hdet hrestrict
  have hzero : ∀ u, μ u = 0 := by
    intro u
    by_cases hu : u = v₀
    · rw [hu, hμ0]
    · exact congrFun hzeroU
        ⟨u, Finset.mem_erase.mpr ⟨hu, Finset.mem_univ u⟩⟩
  have hπ_eq : ∀ u, π u = c * cofactorVec P u := fun u =>
    sub_eq_zero.mp (hzero u)
  have hc : c * cofactorSum P = 1 := by
    rw [cofactorSum, Finset.mul_sum, ← hπ.sum_one]
    exact Finset.sum_congr rfl fun u _ => (hπ_eq u).symm
  rw [hπ_eq v]
  calc
    cofactorVec P v = cofactorVec P v * (c * cofactorSum P) := by
      rw [hc, mul_one]
    _ = c * cofactorVec P v * cofactorSum P := by ring

/-! ## Reversal -/

/-- The reversed kernel `P* = D⁻¹ Pᵀ D`, `D = diag π`. -/
noncomputable def reversal (P : Matrix V V ℝ) (π : V → ℝ) :
    Matrix V V ℝ :=
  Matrix.diagonal (fun v => (π v)⁻¹) * Pᵀ * Matrix.diagonal π

/-- The matrix `L = I - P*` of `eq:reverse`. -/
noncomputable def reversedMatrix (P : Matrix V V ℝ) (π : V → ℝ) :
    Matrix V V ℝ :=
  1 - reversal P π

theorem reversal_apply (P : Matrix V V ℝ) (π : V → ℝ) (u v : V) :
    reversal P π u v = π v * P v u / π u := by
  simp only [reversal, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.transpose_apply]
  ring

theorem reversal_isStochastic {π : V → ℝ} (hP : IsStochastic P)
    (hπ : IsStationary P π) : IsStochastic (reversal P π) where
  nonneg u v := by
    rw [reversal_apply]
    exact div_nonneg (mul_nonneg (hπ.pos v).le (hP.nonneg v u))
      (hπ.pos u).le
  row_sum u := by
    have hu := congrFun hπ.invariant u
    simp only [Matrix.vecMul, dotProduct] at hu
    simp only [reversal_apply]
    rw [← Finset.sum_div, hu]
    exact div_self (hπ.pos u).ne'

theorem reversedMatrix_mulVec_one {π : V → ℝ} (hP : IsStochastic P)
    (hπ : IsStationary P π) :
    reversedMatrix P π *ᵥ (fun _ => 1) = 0 := by
  rw [reversedMatrix, Matrix.sub_mulVec, Matrix.one_mulVec,
    (reversal_isStochastic hP hπ).mulVec_one, sub_self]

/-- `L[U] = D[U]⁻¹ ((I - P)[U])ᵀ D[U]`. -/
theorem principal_reversedMatrix {π : V → ℝ} (hπ : IsStationary P π)
    (U : Finset V) :
    principal (reversedMatrix P π) U =
      Matrix.diagonal (fun i : U => (π i)⁻¹) *
        (1 - principal P U)ᵀ * Matrix.diagonal (fun i : U => π i) := by
  funext i j
  simp only [principal, reversedMatrix, Matrix.submatrix_apply,
    Matrix.sub_apply, reversal_apply, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Matrix.transpose_apply, Matrix.one_apply]
  have hi : π i ≠ 0 := (hπ.pos i).ne'
  by_cases hij : i = j
  · subst hij
    simp only [if_true]
    field_simp
  · have hne : (i : V) ≠ (j : V) := fun h => hij (Subtype.ext h)
    have hji : ¬ j = i := fun h => hij h.symm
    simp only [if_neg hne, if_neg hji]
    field_simp
    ring

theorem det_diagonal_inv_mul {π : V → ℝ} (hπ : IsStationary P π)
    (U : Finset V) :
    (Matrix.diagonal (fun i : U => (π i)⁻¹)).det *
      (Matrix.diagonal (fun i : U => π i)).det = 1 := by
  rw [Matrix.det_diagonal, Matrix.det_diagonal, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun i _ =>
    inv_mul_cancel₀ (hπ.pos i).ne'

/-- Equation `eq:green`, the determinant. -/
theorem det_principal_reversedMatrix {π : V → ℝ}
    (hπ : IsStationary P π) (U : Finset V) :
    (principal (reversedMatrix P π) U).det =
      (1 - principal P U).det := by
  rw [principal_reversedMatrix hπ, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose]
  calc
    (Matrix.diagonal (fun i : U => (π i)⁻¹)).det *
        (1 - principal P U).det *
        (Matrix.diagonal (fun i : U => π i)).det
        = (1 - principal P U).det *
            ((Matrix.diagonal (fun i : U => (π i)⁻¹)).det *
              (Matrix.diagonal (fun i : U => π i)).det) := by ring
    _ = (1 - principal P U).det := by
      rw [det_diagonal_inv_mul hπ, mul_one]

theorem det_principal_reversedMatrix_pos {π : V → ℝ}
    (hP : IsStochastic P) (hirr : IsIrreducible P)
    (hπ : IsStationary P π) (U : Finset V) (hUne : U.Nonempty)
    (hU : U ≠ univ) :
    0 < (principal (reversedMatrix P π) U).det := by
  rw [det_principal_reversedMatrix hπ]
  exact confined_det_pos hP hirr U hUne hU

/-- Equation `eq:green-reversal`: the Green function of the chain
confined to `U` is the transposed inverse of `L[U]`, conjugated by
the stationary distribution. -/
theorem green_reversal {π : V → ℝ} (hP : IsStochastic P)
    (hirr : IsIrreducible P) (hπ : IsStationary P π)
    (U : Finset V) (hUne : U.Nonempty) (hU : U ≠ univ) (i j : U) :
    (1 - principal P U)⁻¹ i j =
      π j / π i * (principal (reversedMatrix P π) U)⁻¹ j i := by
  have hunit : IsUnit (1 - principal P U).det :=
    isUnit_iff_ne_zero.mpr (confined_det_pos hP hirr U hUne hU).ne'
  let Dinv : Matrix U U ℝ := Matrix.diagonal (fun i : U => (π i)⁻¹)
  let D : Matrix U U ℝ := Matrix.diagonal (fun i : U => π i)
  have hDD : D * Dinv = 1 := by
    simp only [D, Dinv, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    funext k
    exact mul_inv_cancel₀ (hπ.pos k).ne'
  have hDinvD : Dinv * D = 1 := by
    simp only [D, Dinv, Matrix.diagonal_mul_diagonal]
    rw [← Matrix.diagonal_one]
    congr 1
    funext k
    exact inv_mul_cancel₀ (hπ.pos k).ne'
  have hinv : (principal (reversedMatrix P π) U)⁻¹ =
      Dinv * ((1 - principal P U)⁻¹)ᵀ * D := by
    apply Matrix.inv_eq_right_inv
    rw [principal_reversedMatrix hπ]
    calc
      Dinv * (1 - principal P U)ᵀ * D *
          (Dinv * ((1 - principal P U)⁻¹)ᵀ * D)
          = Dinv * (1 - principal P U)ᵀ * (D * Dinv) *
              ((1 - principal P U)⁻¹)ᵀ * D := by
            simp only [Matrix.mul_assoc]
      _ = Dinv * ((1 - principal P U)ᵀ *
            ((1 - principal P U)⁻¹)ᵀ) * D := by
            rw [hDD, Matrix.mul_one]
            simp only [Matrix.mul_assoc]
      _ = Dinv * D := by
            rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hunit,
              Matrix.transpose_one, Matrix.mul_one]
      _ = 1 := hDinvD
  rw [hinv]
  simp only [Dinv, D, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.transpose_apply]
  have hi : π i ≠ 0 := (hπ.pos i).ne'
  have hj : π j ≠ 0 := (hπ.pos j).ne'
  field_simp

/-- Equation `eq:green` with `eq:green-reversal`: the Green series
in terms of the inverse of `L[U]`. -/
theorem green_hasSum {π : V → ℝ} (hP : IsStochastic P)
    (hirr : IsIrreducible P) (hπ : IsStationary P π)
    (U : Finset V) (hUne : U.Nonempty) (hU : U ≠ univ) (i j : U) :
    HasSum (fun t => (principal P U ^ t) i j)
      (π j / π i * (principal (reversedMatrix P π) U)⁻¹ j i) := by
  rw [← green_reversal hP hirr hπ U hUne hU i j]
  exact confined_hasSum hP hirr U hUne hU i j

end EAB.Paper.Chain
