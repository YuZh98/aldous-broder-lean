import EAB.Paper.HarmonicFoundation

/-!
# Aggregated matrices and boundary folds

The aggregation matrix is the inverse-principal-matrix expression
in the paper. A fold eliminates one newly encountered vertex from
the remaining boundary matrix.
-/

open Finset Matrix

namespace EAB.Paper.Foundation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {K : Type*} [Field K]

/-- The paper's aggregation matrix. -/
noncomputable def aggregation (L : Matrix V V K) (U : Finset V)
    (M : Matrix (univ \ U : Finset V) U K) : Matrix U U K :=
  1 + (principal L U)⁻¹ * boundaryBlock L U * M

/-- Every row of the boundary matrix has sum one. -/
def UnitRowSums (U : Finset V)
    (M : Matrix (univ \ U : Finset V) U K) : Prop :=
  ∀ v, ∑ j : U, M v j = 1

/-- The column of an aggregation matrix is a coordinate column
minus the corresponding harmonic extension. -/
theorem aggregation_apply (L : Matrix V V K) (U : Finset V)
    (M : Matrix (univ \ U : Finset V) U K) (i j : U) :
    aggregation L U M i j =
      (1 : Matrix U U K) i j -
        harmonic L U (fun v => M v j) i := by
  simp only [aggregation, Matrix.add_apply, Matrix.mul_apply,
    Matrix.one_apply, harmonic_interior_formula]
  simp only [Matrix.mulVec, dotProduct, boundaryBlock,
    Matrix.submatrix_apply]
  simp only [Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib,
    sub_neg_eq_add]
  congr 1
  simp_rw [Finset.sum_mul, mul_sum, mul_assoc]
  rw [Finset.sum_comm]

/-- Unit row sums and a zero-row-sum ambient matrix give zero row
sums for the aggregation matrix. -/
theorem aggregation_zero_row_sum (L : Matrix V V K) (U : Finset V)
    (M : Matrix (univ \ U : Finset V) U K)
    (hL : L *ᵥ (fun _ => 1) = 0)
    (hdet : (principal L U).det ≠ 0)
    (hM : UnitRowSums U M) :
    aggregation L U M *ᵥ (fun _ => 1) = 0 := by
  classical
  have hb : (∑ j : U, (fun v : (univ \ U : Finset V) => M v j)) =
      (fun _ => (1 : K)) := by
    funext v
    simpa only [Finset.sum_apply] using hM v
  have hsum := congrFun
    (harmonic_sum L U hdet Finset.univ
      (fun j : U => fun v => M v j))
  funext i
  have hi := hsum i
  rw [hb, harmonic_one L U hL hdet] at hi
  have hcoord : (∑ j : U, (1 : Matrix U U K) i j) = 1 := by
    have h := congrFun (Matrix.one_mulVec (fun _ : U => (1 : K))) i
    simpa [Matrix.mulVec, dotProduct] using h
  have hi' : (∑ j : U, harmonic L U (fun v => M v j) i) = 1 := by
    simpa only [Finset.sum_apply] using hi.symm
  change (aggregation L U M *ᵥ (fun _ => 1)) i = 0
  calc
    (aggregation L U M *ᵥ (fun _ => 1)) i =
        ∑ j : U, ((1 : Matrix U U K) i j -
          harmonic L U (fun v => M v j) i) := by
      simp [Matrix.mulVec, dotProduct, aggregation_apply]
    _ = (∑ j : U, (1 : Matrix U U K) i j) -
          ∑ j : U, harmonic L U (fun v => M v j) i := by
      rw [Finset.sum_sub_distrib]
    _ = 1 - 1 := by rw [hcoord, hi']
    _ = 0 := sub_self 1

end EAB.Paper.Foundation
