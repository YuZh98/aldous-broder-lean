import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Subtype-indexed minors and the elementary rank-one determinant

This file develops the first matrix objects from the paper without
importing the earlier project proof.
-/

open Finset Matrix

namespace EAB.Paper.Foundation

variable {V : Type*} [DecidableEq V]
variable {K : Type*} [Field K]

/-- The principal submatrix on a finite subset. -/
def principal [Fintype V] (L : Matrix V V K) (U : Finset V) :
    Matrix U U K :=
  L.submatrix (fun u => (u : V)) (fun u => (u : V))

/-- Delete the same index from the rows and columns of a square matrix. -/
def eraseMinor (S : Finset V) (A : Matrix S S K) (i : S) :
    Matrix (S.erase (i : V)) (S.erase (i : V)) K :=
  A.submatrix
    (fun u => (⟨u.1, Finset.mem_of_mem_erase u.2⟩ : S))
    (fun u => (⟨u.1, Finset.mem_of_mem_erase u.2⟩ : S))

/-- The principal cofactor at i, including its one-by-one case. -/
def principalCofactor (S : Finset V) (A : Matrix S S K) (i : S) : K :=
  (eraseMinor S A i).det

/-- The unique zero-by-zero matrix has determinant one by the
empty Leibniz sum and product. -/
theorem det_empty (A : Matrix (∅ : Finset V) (∅ : Finset V) K) :
    A.det = 1 := by
  exact Matrix.det_isEmpty

/-- A one-by-one matrix has principal cofactor one. -/
theorem principalCofactor_singleton (i : V)
    (A : Matrix ({i} : Finset V) ({i} : Finset V) K) :
    principalCofactor {i} A ⟨i, Finset.mem_singleton_self i⟩ = 1 := by
  unfold principalCofactor
  haveI : IsEmpty (({i} : Finset V).erase i) := by
    rw [Finset.erase_singleton]
    infer_instance
  exact Matrix.det_isEmpty

/-- The first rank-one identity of the paper. -/
theorem det_one_add_rank_one (S : Finset V) (a y : S → K) :
    ((1 : Matrix S S K) + Matrix.vecMulVec a y).det =
      1 + ∑ j : S, y j * a j := by
  rw [Matrix.vecMulVec_eq PUnit.{1} a y]
  rw [Matrix.det_one_add_replicateCol_mul_replicateRow]
  rfl

/-- Column multilinearity for a rank-one perturbation. The terms
using the perturbing column twice vanish. -/
theorem det_add_rank_one_expansion (S : Finset V)
    (A : Matrix S S K) (a y : S → K) :
    (A + Matrix.of (fun i j => a i * y j)).det =
      A.det + ∑ j : S, y j * (A.updateCol j a).det := by
  let M : Finset S → Matrix S S K :=
    fun T => Matrix.of fun i j =>
      A i j + if j ∈ T then a i * y j else 0
  have update_invariant : ∀ T : Finset S, ∀ j : S,
      ((M T).updateCol j a).det = (A.updateCol j a).det := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
        intro j
        have hM : M ∅ = A := by
          funext i k
          simp [M]
        rw [hM]
    | @insert k T hk ih =>
        intro j
        by_cases hkj : k = j
        · subst hkj
          have heq : (M (insert k T)).updateCol k a =
              (M T).updateCol k a := by
            funext i j'
            by_cases hj' : j' = k
            · simp [hj']
            · simp [M, hj', Finset.mem_insert]
          rw [heq, ih k]
        · have step : (M (insert k T)).updateCol j a =
              ((M T).updateCol j a).updateCol k
                ((fun i => A i k) + y k • a) := by
            funext i j'
            by_cases hj' : j' = k
            · subst hj'
              simp [M, hkj, mul_comm]
            · simp [M, Matrix.updateCol_apply, hj', Finset.mem_insert]
          rw [step, Matrix.det_updateCol_add, Matrix.det_updateCol_smul]
          have hrestore : ((M T).updateCol j a).updateCol k
              (fun i => A i k) = (M T).updateCol j a := by
            funext i j'
            by_cases hj' : j' = k
            · subst hj'
              simp [M, hkj, hk]
            · simp [Matrix.updateCol_apply, hj']
          have hzero : (((M T).updateCol j a).updateCol k a).det = 0 := by
            refine Matrix.det_zero_of_column_eq hkj fun i => ?_
            simp [Ne.symm hkj]
          rw [hrestore, hzero, mul_zero, add_zero, ih j]
  have expansion : ∀ T : Finset S,
      (M T).det = A.det +
        ∑ j ∈ T, y j * (A.updateCol j a).det := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
        have hM : M ∅ = A := by
          funext i j
          simp [M]
        rw [hM, Finset.sum_empty, add_zero]
    | @insert k T hk ih =>
        have hins : M (insert k T) =
            (M T).updateCol k ((fun i => A i k) + y k • a) := by
          funext i j
          by_cases hj : j = k
          · subst hj
            simp [M, mul_comm]
          · simp [M, hj, Finset.mem_insert]
        have hrestore : (M T).updateCol k (fun i => A i k) = M T := by
          funext i j
          by_cases hj : j = k
          · subst hj
            simp [M, hk]
          · simp [hj]
        rw [hins, Matrix.det_updateCol_add, Matrix.det_updateCol_smul,
          hrestore, update_invariant T k, ih, Finset.sum_insert hk]
        ring
  have hfinal : A + Matrix.of (fun i j => a i * y j) = M univ := by
    funext i j
    simp [M]
  rw [hfinal, expansion univ]

/-- Reindex the complement of an index as the erased finite set. -/
private def eraseSubtypeEquiv (S : Finset V) (i : S) :
    (S.erase (i : V)) ≃ {j : S // j ≠ i} where
  toFun j :=
    ⟨⟨j.1, Finset.mem_of_mem_erase j.2⟩, by
      intro h
      exact (Finset.mem_erase.mp j.2).1 (congrArg Subtype.val h)⟩
  invFun j :=
    ⟨j.1.1, Finset.mem_erase.mpr ⟨by
      intro h
      exact j.2 (Subtype.ext h), j.1.2⟩⟩
  left_inv := by
    intro j
    exact Subtype.ext rfl
  right_inv := by
    intro j
    exact Subtype.ext (Subtype.ext rfl)

/-- A coordinate row with a single one drops from a determinant,
leaving the principal submatrix on the remaining indices. -/
theorem det_drop_coordinate_row (S : Finset V)
    (A : Matrix S S K) (i : S)
    (hrow : ∀ j : S, A i j = if j = i then 1 else 0) :
    A.det = (eraseMinor S A i).det := by
  classical
  letI : Fintype {j : S // j = i} := Subtype.fintype _
  letI : Fintype {j : S // j ≠ i} := Subtype.fintype _
  have htri := Matrix.twoBlockTriangular_det' A
    (fun j : S => j = i) (by
      intro j hj k hk
      subst j
      simpa [hk] using hrow k)
  have hsingle :
      (A.toSquareBlockProp (fun j : S => j = i)).det = 1 := by
    have h := Matrix.det_toSquareBlock_id A i
    change (A.toSquareBlockProp (fun j : S => j = i)).det = A i i at h
    exact h.trans (by simpa using hrow i)
  let e := eraseSubtypeEquiv S i
  have hminor :
      (eraseMinor S A i).det =
        (A.toSquareBlockProp (fun j : S => j ≠ i)).det := by
    calc
      (eraseMinor S A i).det =
          ((A.toSquareBlockProp (fun j : S => j ≠ i)).submatrix e e).det := by
            rfl
      _ = _ := Matrix.det_submatrix_equiv_self e _
  have htri' : A.det =
      (A.toSquareBlockProp (fun j : S => j = i)).det *
        (A.toSquareBlockProp (fun j : S => j ≠ i)).det := by
    exact htri
  calc
    A.det = (A.toSquareBlockProp (fun j : S => j = i)).det *
        (A.toSquareBlockProp (fun j : S => j ≠ i)).det := htri'
    _ = 1 * (A.toSquareBlockProp (fun j : S => j ≠ i)).det := by rw [hsingle]
    _ = (A.toSquareBlockProp (fun j : S => j ≠ i)).det := one_mul _
    _ = (eraseMinor S A i).det := hminor.symm

/-- The diagonal adjugate entry is the principal cofactor. -/
theorem principalCofactor_eq_adjugate (S : Finset V)
    (A : Matrix S S K) (i : S) :
    principalCofactor S A i = A.adjugate i i := by
  let C := A.updateRow i (Pi.single i 1)
  have hrow : ∀ j : S, C i j = if j = i then 1 else 0 := by
    intro j
    simp [C, Pi.single_apply]
  have hdrop := det_drop_coordinate_row S C i hrow
  have hminor : eraseMinor S C i = eraseMinor S A i := by
    funext j k
    have hji : (⟨j.1, Finset.mem_of_mem_erase j.2⟩ : S) ≠ i := by
      intro h
      exact (Finset.mem_erase.mp j.2).1 (congrArg Subtype.val h)
    simp [eraseMinor, C, Matrix.submatrix_apply, hji]
  rw [hminor] at hdrop
  rw [principalCofactor, ← hdrop]
  exact (Matrix.adjugate_apply A i i).symm

/-- Multilinearity in one column, for a finite linear combination. -/
private theorem detcol_linear (S : Finset V) (A : Matrix S S K)
    (b : S) {ι : Type*} (s : Finset ι) (c : ι → K)
    (y : ι → S → K) :
    (A.updateCol b (∑ i ∈ s, c i • y i)).det =
      ∑ i ∈ s, c i * (A.updateCol b (y i)).det := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      exact Matrix.det_eq_zero_of_column_eq_zero b fun i => by simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        Matrix.det_updateCol_add, Matrix.det_updateCol_smul, ih]

/-- In a zero-row-sum matrix, the determinant of a replaced column
does not depend on which column was replaced. -/
private theorem det_updateCol_constant (S : Finset V)
    (A : Matrix S S K) (h : A *ᵥ (fun _ => 1) = 0)
    (c : S → K) (b : S) :
    (A.updateCol b c).det =
      ∑ a : S, c a * (A.updateCol a (Pi.single a 1)).det := by
  have hrow : ∀ u : S, ∑ v : S, A u v = 0 := by
    intro u
    have hu := congrFun h u
    simpa [Matrix.mulVec, dotProduct] using hu
  have hb : ∀ a b b' : S,
      (A.updateCol b (Pi.single a (1 : K))).det =
        (A.updateCol b' (Pi.single a (1 : K))).det := by
    intro a b b'
    rcases eq_or_ne b b' with rfl | hbb'
    · rfl
    set M := A.updateCol b (Pi.single a (1 : K)) with hMdef
    set X := A.updateCol b' (Pi.single a (1 : K)) with hXdef
    have hg : (fun u => A u b') =
        ∑ v ∈ Finset.univ.erase b', (-1 : K) • (fun u => A u v) := by
      funext u
      have hsum : A u b' + ∑ v ∈ Finset.univ.erase b', A u v = 0 := by
        rw [Finset.add_sum_erase Finset.univ (fun v => A u v)
          (Finset.mem_univ b')]
        exact hrow u
      have h1 : A u b' = -∑ v ∈ Finset.univ.erase b', A u v :=
        eq_neg_of_add_eq_zero_left hsum
      rw [h1]
      simp [Finset.sum_apply]
    have hcolM : (fun u => M u b') = fun u => A u b' := by
      funext u
      simp [hMdef, Ne.symm hbb']
    have hMcol : M = M.updateCol b'
        (∑ v ∈ Finset.univ.erase b', (-1 : K) • (fun u => A u v)) := by
      conv_lhs => rw [← Matrix.updateCol_eq_self M b']
      rw [hcolM, hg]
    have hdet : M.det = ∑ v ∈ Finset.univ.erase b',
        (-1 : K) * (M.updateCol b' (fun u => A u v)).det := by
      conv_lhs => rw [hMcol]
      exact detcol_linear S M b' (Finset.univ.erase b')
        (fun _ => (-1 : K)) (fun v u => A u v)
    have hzero : ∀ v ∈ Finset.univ.erase b', v ≠ b →
        (M.updateCol b' (fun u => A u v)).det = 0 := by
      intro v hv hvb
      have hvb' : v ≠ b' := (Finset.mem_erase.mp hv).1
      refine Matrix.det_zero_of_column_eq hvb' fun k => ?_
      simp [hvb', hMdef, hvb]
    have hsum1 : ∑ v ∈ Finset.univ.erase b',
        (-1 : K) * (M.updateCol b' (fun u => A u v)).det =
          (-1 : K) * (M.updateCol b' (fun u => A u b)).det := by
      refine Finset.sum_eq_single_of_mem b
        (Finset.mem_erase.mpr ⟨hbb', Finset.mem_univ b⟩) ?_
      intro v hv hvb
      rw [hzero v hv hvb, mul_zero]
    have hswap : M.updateCol b' (fun u => A u b) =
        X.submatrix id ⇑(Equiv.swap b b') := by
      funext u w
      rcases eq_or_ne w b with rfl | hwb
      · simp [Matrix.submatrix_apply, Equiv.swap_apply_left,
          hMdef, hXdef, hbb']
      rcases eq_or_ne w b' with rfl | hwb'
      · simp [Matrix.submatrix_apply, Equiv.swap_apply_right,
          hXdef, hbb']
      have hw : Equiv.swap b b' w = w :=
        Equiv.swap_apply_of_ne_of_ne hwb hwb'
      simp [Matrix.submatrix_apply, hw, hMdef, hXdef, hwb, hwb']
    have hdetswap :
        (X.submatrix id ⇑(Equiv.swap b b')).det = -X.det := by
      rw [Matrix.det_permute', Equiv.Perm.sign_swap hbb']
      simp
    calc
      M.det = ∑ v ∈ Finset.univ.erase b',
          (-1 : K) * (M.updateCol b' (fun u => A u v)).det := hdet
      _ = (-1 : K) * (M.updateCol b' (fun u => A u b)).det := hsum1
      _ = (-1 : K) * (X.submatrix id ⇑(Equiv.swap b b')).det := by rw [hswap]
      _ = (-1 : K) * (-X.det) := by rw [hdetswap]
      _ = X.det := by ring
  have hc : c = ∑ a ∈ Finset.univ, c a • Pi.single a (1 : K) := by
    funext x
    simp [Finset.sum_apply, Pi.single_apply]
  have h1 : (A.updateCol b c).det =
      ∑ a ∈ Finset.univ, c a *
        (A.updateCol b (Pi.single a (1 : K))).det := by
    conv_lhs => rw [hc]
    exact detcol_linear S A b Finset.univ c (fun a => Pi.single a 1)
  rw [h1]
  exact Finset.sum_congr rfl fun a _ => by rw [hb a b a]

private theorem adjugate_eq_det_updateCol (S : Finset V)
    (A : Matrix S S K) (i j : S) :
    A.adjugate i j = (A.updateCol i (Pi.single j 1)).det := by
  have h := congrArg (fun M : Matrix S S K => M j i)
    (Matrix.adjugate_transpose A)
  simpa only [Matrix.transpose_apply, Matrix.adjugate_apply,
    Matrix.updateRow_transpose, Matrix.det_transpose] using h

/-- Every adjugate column of a zero-row-sum matrix is its
corresponding principal cofactor times the constant vector. -/
theorem adjugate_apply_eq_principalCofactor (S : Finset V)
    (A : Matrix S S K) (hrow : A *ᵥ (fun _ => 1) = 0)
    (i j : S) :
    A.adjugate i j = principalCofactor S A j := by
  have hstar := det_updateCol_constant S A hrow (Pi.single j 1) i
  have hdiag := det_updateCol_constant S A hrow (Pi.single j 1) j
  have hsame : (A.updateCol i (Pi.single j 1)).det =
      (A.updateCol j (Pi.single j 1)).det := by
    rw [hstar, hdiag]
  rw [principalCofactor_eq_adjugate]
  rw [adjugate_eq_det_updateCol S A i j,
    adjugate_eq_det_updateCol S A j j]
  exact hsame

/-- A zero-row-sum matrix on a nonempty set has determinant zero. -/
theorem det_zero_of_zero_row_sum (S : Finset V) (A : Matrix S S K)
    (hS : S.Nonempty) (hrow : A *ᵥ (fun _ => 1) = 0) :
    A.det = 0 := by
  let i : S := ⟨hS.choose, hS.choose_spec⟩
  exact Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors
    hrow (i := i) (by simp)

/-- The principal cofactor vector is in the left kernel. -/
theorem principalCofactor_left_kernel (S : Finset V)
    (A : Matrix S S K) (hS : S.Nonempty)
    (hrow : A *ᵥ (fun _ => 1) = 0) :
    (fun i : S => principalCofactor S A i) ᵥ* A = 0 := by
  have hadj : A.adjugate =
      Matrix.of fun _ j => principalCofactor S A j := by
    funext i j
    exact adjugate_apply_eq_principalCofactor S A hrow i j
  have hmul := Matrix.adjugate_mul A
  rw [hadj, det_zero_of_zero_row_sum S A hS hrow, zero_smul] at hmul
  funext j
  have hj := congrFun (congrFun hmul
    (⟨hS.choose, hS.choose_spec⟩ : S)) j
  simpa [Matrix.mul_apply, Matrix.vecMul, dotProduct] using hj

/-- The zero-row-sum cofactor rank-one determinant identity. -/
theorem det_add_rank_one_zero_row_sum (S : Finset V)
    (A : Matrix S S K) (hS : S.Nonempty)
    (hrow : A *ᵥ (fun _ => 1) = 0) (a y : S → K) :
    (A + Matrix.of (fun i j => a i * y j)).det =
      (∑ j : S, y j) *
        (∑ i : S, a i * principalCofactor S A i) := by
  rw [det_add_rank_one_expansion S A a y,
    det_zero_of_zero_row_sum S A hS hrow, zero_add]
  calc
    (∑ j : S, y j * (A.updateCol j a).det) =
        ∑ j : S, y j *
          (∑ i : S, a i * principalCofactor S A i) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [det_updateCol_constant S A hrow a j]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [principalCofactor_eq_adjugate,
        adjugate_eq_det_updateCol]
    _ = (∑ j : S, y j) *
          (∑ i : S, a i * principalCofactor S A i) := by
      rw [Finset.sum_mul]

end EAB.Paper.Foundation
