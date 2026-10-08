import EAB.Paper.WalkOrders
import EAB.Paper.OrderWeights

/-!
# Reversal and determinant telescoping

Lemma `lem:joint-order` of the blueprint. Each Green entry of the
excursion formula is reversed by `eq:green-reversal`. Every inverse
entry after the first is a harmonic reading times a ratio of
determinants, by `eq:inverse-ratio`. The ratios telescope, and the
last determinant is `π_{τ_k} Λ` by Lemma `lem:stationary`. The
telescoping is carried out by induction on the order, from its last
vertex backwards.
-/

open MeasureTheory ProbabilityTheory Finset

namespace EAB.Paper.Chain

open Foundation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The entry `(L[U]⁻¹)_{xy}`, and `0` unless `x, y ∈ U`. -/
noncomputable def invEntry (L : Matrix V V ℝ) (U : Finset V)
    (x y : V) : ℝ :=
  if h : x ∈ U ∧ y ∈ U then
    (Foundation.principal L U)⁻¹ ⟨x, h.1⟩ ⟨y, h.2⟩
  else 0

variable {P : Matrix V V ℝ} {π : V → ℝ}

/-- Equation `eq:green-reversal` for arbitrary states. -/
theorem green_eq_invEntry (hP : IsStochastic P)
    (hirr : IsIrreducible P) (hπ : IsStationary P π)
    (U : Finset V) (hU : U ≠ univ) (a b : V) :
    green P U a b =
      π b / π a * invEntry (reversedMatrix P π) U b a := by
  unfold green invEntry
  by_cases h : a ∈ U ∧ b ∈ U
  · rw [dif_pos h, dif_pos ⟨h.2, h.1⟩]
    exact green_reversal hP hirr hπ U ⟨a, h.1⟩ hU _ _
  · rw [dif_neg h, dif_neg (fun h' => h ⟨h'.2, h'.1⟩), mul_zero]

/-- Equation `eq:inverse-ratio` in the form used by the telescope:
the column `z` of the inverse of `L[U ∪ {z}]` is the harmonic
extension `γ^{U,z}` times `det L[U] / det L[U ∪ {z}]`. -/
theorem invEntry_insert (L : Matrix V V ℝ) (U : Finset V) (z : V)
    (hz : z ∉ U) (hdetU : (Foundation.principal L U).det ≠ 0)
    (hdetU' : (Foundation.principal L (insert z U)).det ≠ 0)
    (x : V) :
    invEntry L (insert z U) x z =
      gamma L U z x *
        ((Foundation.principal L U).det /
          (Foundation.principal L (insert z U)).det) := by
  have hzU' : z ∈ insert z U := Finset.mem_insert_self z U
  have herase : ∀ S : Finset V, S = U →
      (Foundation.principal L S).det ≠ 0 ∧
        gamma L S z x = gamma L U z x ∧
        (Foundation.principal L S).det =
          (Foundation.principal L U).det := by
    rintro S rfl
    exact ⟨hdetU, rfl, rfl⟩
  obtain ⟨hdetE, hgammaE, hdetEq⟩ :=
    herase ((insert z U).erase z) (Finset.erase_insert hz)
  unfold invEntry
  by_cases hx : x ∈ insert z U
  · rw [dif_pos ⟨hx, hzU'⟩]
    have hcol := inv_column_eq_gamma L (insert z U) ⟨z, hzU'⟩
      hdetU' hdetE ⟨x, hx⟩
    have hdiag := inv_diag_eq_det_ratio L (insert z U) ⟨z, hzU'⟩
    simp only at hcol hdiag
    rw [hgammaE] at hcol
    rw [hdetEq] at hdiag
    have hd : (Foundation.principal L (insert z U))⁻¹
        ⟨z, hzU'⟩ ⟨z, hzU'⟩ ≠ 0 := by
      rw [hdiag]
      exact div_ne_zero hdetU hdetU'
    rw [← hcol, ← hdiag, div_mul_cancel₀ _ hd]
  · rw [dif_neg (fun h => hx h.1)]
    have hxU : x ∉ U := fun h => hx (Finset.mem_insert_of_mem h)
    have hxz : x ≠ z := fun h => hx (h ▸ hzU')
    have hboundary := harmonic_boundary L U (coordBoundary U z)
      ⟨x, Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxU⟩⟩
    have hgamma : gamma L U z x = 0 := by
      rw [gamma]
      simpa [coordBoundary, hxz] using hboundary
    rw [hgamma, zero_mul]

/-- The last determinant of the telescope: `det L[V \ {z}] = π_z Λ`. -/
theorem det_reversedMatrix_erase (hP : IsStochastic P)
    (hirr : IsIrreducible P) (hπ : IsStationary P π)
    (hcard : 2 ≤ Fintype.card V) (z : V) :
    (Foundation.principal (reversedMatrix P π) (univ.erase z)).det =
      π z * cofactorSum P := by
  rw [det_principal_reversedMatrix hπ, ← principal_one_sub,
    ← hπ.cofactorVec_eq hP hirr hcard z]
  rfl

/-- The product of the stationary weights along an order. -/
noncomputable def orderPi (π : V → ℝ) (τ : List V) : ℝ :=
  (τ.map π).prod

/-- The product of the edge weights `π_{g(v)} P_{g(v) v}` along an
order. -/
noncomputable def orderEdgeWeight (P : Matrix V V ℝ) (π : V → ℝ)
    (g : V → V) (τ : List V) : ℝ :=
  (τ.map fun v => π (g v) * P (g v) v).prod

omit [Fintype V] [DecidableEq V] in
theorem orderPi_pos (hπ : ∀ v, 0 < π v) (τ : List V) :
    0 < orderPi π τ := by
  induction τ with
  | nil => simp [orderPi]
  | cons v rest ih =>
      simp only [orderPi, List.map_cons, List.prod_cons] at ih ⊢
      exact mul_pos (hπ v) ih

/-- **Lemma `lem:joint-order`**, as an identity between the
excursion weight and the order weight. -/
theorem excursionWeight_eq (hP : IsStochastic P)
    (hirr : IsIrreducible P) (hπ : IsStationary P π)
    (hcard : 2 ≤ Fintype.card V) (g : V → V) :
    ∀ (rest : List V) (z : V) (U : Finset V) (a : V), a ∈ U →
      (z :: rest).Nodup → (z :: rest).toFinset = univ \ U →
      excursionWeight P g U a (z :: rest) =
        (Foundation.principal (reversedMatrix P π) U).det /
            (π a * orderPi π (z :: rest) * cofactorSum P) *
          orderEdgeWeight P π g (z :: rest) *
          invEntry (reversedMatrix P π) U (g z) a *
          orderWeight (reversedMatrix P π) g U (z :: rest) := by
  intro rest
  have hΛ : cofactorSum P ≠ 0 := (cofactorSum_pos hP hirr hcard).ne'
  induction rest with
  | nil =>
      intro z U a ha _ hfin
      have hz : z ∉ U := by
        have hmem : z ∈ univ \ U := by
          rw [← hfin]
          simp
        exact (Finset.mem_sdiff.mp hmem).2
      have hU : U ≠ univ := fun h => hz (h ▸ Finset.mem_univ z)
      have hUeq : U = univ.erase z := by
        ext x
        have hx : x ∈ ([z] : List V).toFinset ↔ x ∈ univ \ U := by
          rw [hfin]
        simp only [List.toFinset_cons, List.toFinset_nil,
          insert_empty_eq, Finset.mem_singleton, Finset.mem_sdiff,
          Finset.mem_univ, true_and] at hx
        simp only [Finset.mem_erase, Finset.mem_univ, and_true]
        constructor
        · intro hxU hxz
          exact (hx.mp hxz) hxU
        · intro hxz
          by_contra hxU
          exact hxz (hx.mpr hxU)
      have hdet : (Foundation.principal (reversedMatrix P π) U).det =
          π z * cofactorSum P := by
        rw [hUeq]
        exact det_reversedMatrix_erase hP hirr hπ hcard z
      have hπa : π a ≠ 0 := (hπ.pos a).ne'
      have hπz : π z ≠ 0 := (hπ.pos z).ne'
      simp only [excursionWeight, orderWeight, orderPi,
        orderEdgeWeight, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, mul_one]
      rw [green_eq_invEntry hP hirr hπ U hU, hdet]
      field_simp
  | cons y rest ih =>
      intro z U a ha hnodup hfin
      have hz : z ∉ U := by
        have hmem : z ∈ univ \ U := by
          rw [← hfin]
          simp
        exact (Finset.mem_sdiff.mp hmem).2
      have hU : U ≠ univ := fun h => hz (h ▸ Finset.mem_univ z)
      obtain ⟨hzrest, hrestNodup⟩ := List.nodup_cons.mp hnodup
      have hfin' : (y :: rest).toFinset = univ \ insert z U := by
        have hcompl : univ \ insert z U = (univ \ U).erase z := by
          ext x
          simp
        rw [hcompl, ← hfin, List.toFinset_cons (a := z),
          Finset.erase_insert (by simpa using hzrest)]
      have hy : y ∉ insert z U := by
        have hmem : y ∈ univ \ insert z U := by
          rw [← hfin']
          simp
        exact (Finset.mem_sdiff.mp hmem).2
      have hU' : insert z U ≠ univ :=
        fun h => hy (h ▸ Finset.mem_univ y)
      have hdetU :
          (Foundation.principal (reversedMatrix P π) U).det ≠ 0 :=
        (det_principal_reversedMatrix_pos hP hirr hπ U ⟨a, ha⟩ hU).ne'
      have hdetU' :
          (Foundation.principal (reversedMatrix P π)
            (insert z U)).det ≠ 0 :=
        (det_principal_reversedMatrix_pos hP hirr hπ (insert z U)
          ⟨z, Finset.mem_insert_self z U⟩ hU').ne'
      have hIH := ih y (insert z U) z (Finset.mem_insert_self z U)
        hrestNodup hfin'
      have hπa : π a ≠ 0 := (hπ.pos a).ne'
      have hπz : π z ≠ 0 := (hπ.pos z).ne'
      have hπrest : orderPi π (y :: rest) ≠ 0 :=
        (orderPi_pos hπ.pos (y :: rest)).ne'
      have hpi : orderPi π (z :: y :: rest) =
          π z * orderPi π (y :: rest) := by
        simp [orderPi]
      have hedge : orderEdgeWeight P π g (z :: y :: rest) =
          π (g z) * P (g z) z *
            orderEdgeWeight P π g (y :: rest) := by
        simp [orderEdgeWeight]
      rw [show excursionWeight P g U a (z :: y :: rest) =
          green P U a (g z) * P (g z) z *
            excursionWeight P g (insert z U) z (y :: rest) from rfl,
        hIH, invEntry_insert _ U z hz hdetU hdetU',
        orderWeight_cons_cons, green_eq_invEntry hP hirr hπ U hU,
        hpi, hedge]
      field_simp

end EAB.Paper.Chain
