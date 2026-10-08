import EAB.Paper.MatrixFoundation

/-!
# Harmonic extension from a boundary vector

The interior coordinates are defined by the inverse principal
submatrix, exactly as in the paper. No identity padding is used.
-/

open Finset Matrix

namespace EAB.Paper.Foundation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {K : Type*} [Field K]

/-- Rows in U and columns outside U. -/
def boundaryBlock (L : Matrix V V K) (U : Finset V) :
    Matrix U (univ \ U : Finset V) K :=
  L.submatrix (fun i => (i : V)) (fun v => (v : V))

/-- Assemble a full vector from its values on U and its complement. -/
def assemble (U : Finset V)
    (a : U → K) (m : (univ \ U : Finset V) → K) : V → K :=
  fun v => if hv : v ∈ U then a ⟨v, hv⟩
    else m ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hv⟩⟩

omit [Field K] in
theorem assemble_interior (U : Finset V)
    (a : U → K) (m : (univ \ U : Finset V) → K) (i : U) :
    assemble U a m i = a i := by
  simp [assemble, i.2]

omit [Field K] in
theorem assemble_boundary (U : Finset V)
    (a : U → K) (m : (univ \ U : Finset V) → K)
    (v : (univ \ U : Finset V)) :
    assemble U a m v = m v := by
  have hv : (v : V) ∉ U := (Finset.mem_sdiff.mp v.2).2
  simp [assemble, hv]

/-- The inverse-principal-matrix formula for harmonic extension. -/
noncomputable def harmonic (L : Matrix V V K) (U : Finset V)
    (m : (univ \ U : Finset V) → K) : V → K :=
  assemble U
    (-(principal L U)⁻¹ *ᵥ (boundaryBlock L U *ᵥ m)) m

theorem harmonic_boundary (L : Matrix V V K) (U : Finset V)
    (m : (univ \ U : Finset V) → K)
    (v : (univ \ U : Finset V)) :
    harmonic L U m v = m v := by
  exact assemble_boundary U _ m v

theorem harmonic_interior_formula (L : Matrix V V K) (U : Finset V)
    (m : (univ \ U : Finset V) → K) (i : U) :
    harmonic L U m i =
      (-(principal L U)⁻¹ *ᵥ (boundaryBlock L U *ᵥ m)) i := by
  exact assemble_interior U _ m i

/-- Split a full row sum over a subset and its complement. -/
theorem mulVec_split (L : Matrix V V K) (U : Finset V)
    (x : V → K) (i : U) :
    (L *ᵥ x) i =
      (principal L U *ᵥ fun u : U => x u) i +
        (boundaryBlock L U *ᵥ fun v : (univ \ U : Finset V) => x v) i := by
  classical
  have hdisj : Disjoint U (univ \ U : Finset V) := disjoint_sdiff_self_right
  have hcover : U ∪ (univ \ U : Finset V) = univ := by
    ext v
    simp
  simp only [Matrix.mulVec, dotProduct, principal, boundaryBlock,
    Matrix.submatrix_apply]
  rw [Finset.sum_coe_sort U (fun v => L i v * x v),
    Finset.sum_coe_sort (univ \ U : Finset V)
      (fun v => L i v * x v)]
  rw [← Finset.sum_union hdisj, hcover]

/-- The inverse formula solves the interior linear system. -/
theorem harmonic_principal_equation (L : Matrix V V K) (U : Finset V)
    (m : (univ \ U : Finset V) → K)
    (hdet : (principal L U).det ≠ 0) :
    principal L U *ᵥ (fun i : U => harmonic L U m i) =
      -(boundaryBlock L U *ᵥ m) := by
  have hvec : (fun i : U => harmonic L U m i) =
      (-(principal L U)⁻¹ *ᵥ (boundaryBlock L U *ᵥ m)) := by
    funext i
    exact harmonic_interior_formula L U m i
  have hunit : IsUnit (principal L U).det :=
    isUnit_iff_ne_zero.mpr hdet
  rw [hvec, Matrix.neg_mulVec, Matrix.mulVec_neg,
    Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv (principal L U) hunit,
    Matrix.one_mulVec]

/-- Harmonic extension is annihilated by every interior row. -/
theorem harmonic_interior_row (L : Matrix V V K) (U : Finset V)
    (m : (univ \ U : Finset V) → K)
    (hdet : (principal L U).det ≠ 0) (i : U) :
    (L *ᵥ harmonic L U m) i = 0 := by
  have hboundary :
      (fun v : (univ \ U : Finset V) => harmonic L U m v) = m := by
    funext v
    exact harmonic_boundary L U m v
  calc
    (L *ᵥ harmonic L U m) i =
        (principal L U *ᵥ fun u : U => harmonic L U m u) i +
          (boundaryBlock L U *ᵥ
            fun v : (univ \ U : Finset V) => harmonic L U m v) i :=
      mulVec_split L U _ i
    _ = (-(boundaryBlock L U *ᵥ m)) i +
          (boundaryBlock L U *ᵥ m) i := by
      rw [harmonic_principal_equation L U m hdet, hboundary]
    _ = 0 := by simp

/-- The boundary values and zero interior rows characterize the
harmonic extension uniquely. -/
theorem harmonic_unique (L : Matrix V V K) (U : Finset V)
    (m : (univ \ U : Finset V) → K)
    (hdet : (principal L U).det ≠ 0)
    (g : V → K)
    (hboundary : ∀ v : (univ \ U : Finset V), g v = m v)
    (hinterior : ∀ i : U, (L *ᵥ g) i = 0) :
    g = harmonic L U m := by
  have hboundaryVec :
      (fun v : (univ \ U : Finset V) => g v) = m := by
    funext v
    exact hboundary v
  have hsystem :
      principal L U *ᵥ (fun i : U => g i) =
        -(boundaryBlock L U *ᵥ m) := by
    funext i
    have hs := mulVec_split L U g i
    rw [hboundaryVec, hinterior i] at hs
    exact eq_neg_of_add_eq_zero_left hs.symm
  have hunit : IsUnit (principal L U).det :=
    isUnit_iff_ne_zero.mpr hdet
  have hinj : Function.Injective (principal L U).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr
      (((principal L U).isUnit_iff_isUnit_det).mpr hunit)
  have heq : (fun i : U => g i) =
      (fun i : U => harmonic L U m i) :=
    hinj (hsystem.trans
      (harmonic_principal_equation L U m hdet).symm)
  funext v
  by_cases hv : v ∈ U
  · exact congrFun heq ⟨v, hv⟩
  · let z : (univ \ U : Finset V) :=
      ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hv⟩⟩
    exact (hboundary z).trans (harmonic_boundary L U m z).symm

/-- Harmonic extension is additive in its boundary data. -/
theorem harmonic_add (L : Matrix V V K) (U : Finset V)
    (m n : (univ \ U : Finset V) → K)
    (hdet : (principal L U).det ≠ 0) :
    harmonic L U (m + n) = harmonic L U m + harmonic L U n := by
  symm
  apply harmonic_unique L U (m + n) hdet
  · intro v
    simp [Pi.add_apply, harmonic_boundary]
  · intro i
    rw [Matrix.mulVec_add]
    simp [harmonic_interior_row L U m hdet i,
      harmonic_interior_row L U n hdet i]

/-- Harmonic extension commutes with scalar multiplication. -/
theorem harmonic_smul (L : Matrix V V K) (U : Finset V)
    (c : K) (m : (univ \ U : Finset V) → K)
    (hdet : (principal L U).det ≠ 0) :
    harmonic L U (c • m) = c • harmonic L U m := by
  symm
  apply harmonic_unique L U (c • m) hdet
  · intro v
    simp [Pi.smul_apply, harmonic_boundary]
  · intro i
    rw [Matrix.mulVec_smul]
    simp [harmonic_interior_row L U m hdet i]

/-- A zero-row-sum matrix extends unit boundary data to the unit vector. -/
theorem harmonic_one (L : Matrix V V K) (U : Finset V)
    (hL : L *ᵥ (fun _ : V => 1) = 0)
    (hdet : (principal L U).det ≠ 0) :
    harmonic L U (fun _ => 1) = fun _ => 1 := by
  symm
  apply harmonic_unique L U (fun _ => 1) hdet
  · intro v
    rfl
  · intro i
    simpa using congrFun hL i

theorem harmonic_zero (L : Matrix V V K) (U : Finset V)
    (hdet : (principal L U).det ≠ 0) :
    harmonic L U (0 : (univ \ U : Finset V) → K) = 0 := by
  symm
  apply harmonic_unique L U 0 hdet
  · intro v
    rfl
  · intro i
    simp

theorem harmonic_sum (L : Matrix V V K) (U : Finset V)
    (hdet : (principal L U).det ≠ 0)
    {ι : Type*} (s : Finset ι)
    (m : ι → (univ \ U : Finset V) → K) :
    harmonic L U (∑ j ∈ s, m j) =
      ∑ j ∈ s, harmonic L U (m j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [harmonic_zero L U hdet]
  | @insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj,
        harmonic_add L U _ _ hdet, ih]

/-- The coordinate vector at `w` on the boundary `V \ U`. -/
def coordBoundary (U : Finset V) (w : V) :
    (univ \ U : Finset V) → K :=
  fun v => if (v : V) = w then 1 else 0

/-- The paper's `γ^{U,w}`: the harmonic extension of the coordinate
boundary vector at `w`. The paper uses it for `w ∉ U`. -/
noncomputable def gamma (L : Matrix V V K) (U : Finset V)
    (w : V) : V → K :=
  harmonic L U (coordBoundary U w)

/-- Extend boundary data from `V \ (U ∪ {w})` to `V \ U` by zero at `w`. -/
noncomputable def extendZero (U : Finset V) (w : V)
    (m : (univ \ insert w U : Finset V) → K) :
    (univ \ U : Finset V) → K :=
  fun v =>
    if h : (v : V) = w then 0
    else
      m ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ (v : V), by
        have hvU : (v : V) ∉ U := (Finset.mem_sdiff.mp v.2).2
        simp [Finset.mem_insert, h, hvU]⟩⟩

theorem extendZero_at_new_vertex (U : Finset V) (w : V) (hw : w ∉ U)
    (m : (univ \ insert w U : Finset V) → K) :
    extendZero U w m
      ⟨w, Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hw⟩⟩ = 0 := by
  simp [extendZero]

theorem extendZero_at_old_boundary (U : Finset V) (w : V)
    (m : (univ \ insert w U : Finset V) → K)
    (v : V) (hv : v ∉ insert w U) :
    extendZero U w m
      ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ v,
        (fun h => hv (Finset.mem_insert_of_mem h))⟩⟩ =
      m ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hv⟩⟩ := by
  have hvw : v ≠ w := fun h => hv (h ▸ Finset.mem_insert_self w U)
  simp [extendZero, hvw]

/-- The paper's one-vertex harmonic update. -/
theorem harmonic_one_step (L : Matrix V V K)
    (U : Finset V) (w : V) (hw : w ∉ U)
    (hdetU : (principal L U).det ≠ 0)
    (hdetU' : (principal L (insert w U)).det ≠ 0)
    (m : (univ \ insert w U : Finset V) → K) :
    harmonic L (insert w U) m =
      harmonic L U (extendZero U w m) +
        harmonic L (insert w U) m w • gamma L U w := by
  let wU : (univ \ U : Finset V) :=
    ⟨w, Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hw⟩⟩
  let m0 := extendZero U w m
  let e : (univ \ U : Finset V) → K := coordBoundary U w
  let f := harmonic L (insert w U) m
  let c : K := f w
  have hboundary : ∀ v : (univ \ U : Finset V),
      f v = (m0 + c • e) v := by
    intro v
    by_cases hvw : (v : V) = w
    · have hveq : v = wU := Subtype.ext hvw
      subst v
      simp [m0, e, c, f, wU, extendZero, coordBoundary, Pi.add_apply,
        Pi.smul_apply]
    · have hvU' : (v : V) ∉ insert w U := by
        have hvU : (v : V) ∉ U := (Finset.mem_sdiff.mp v.2).2
        simp [Finset.mem_insert, hvw, hvU]
      have hf := harmonic_boundary L (insert w U) m
        ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ (v : V), hvU'⟩⟩
      simpa [m0, e, c, f, extendZero, coordBoundary, hvw,
        Pi.add_apply, Pi.smul_apply] using hf
  have hinterior : ∀ i : U, (L *ᵥ f) i = 0 := by
    intro i
    exact harmonic_interior_row L (insert w U) m hdetU'
      ⟨i, Finset.mem_insert_of_mem i.2⟩
  have huniq := harmonic_unique L U (m0 + c • e) hdetU
    f hboundary hinterior
  calc
    f = harmonic L U (m0 + c • e) := huniq
    _ = harmonic L U m0 + c • harmonic L U e := by
      rw [harmonic_add L U m0 (c • e) hdetU,
        harmonic_smul L U c e hdetU]

end EAB.Paper.Foundation
