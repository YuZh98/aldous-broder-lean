import EAB.Paper.OrderWeights

/-!
# The order-mass identity and the single-root normalization

Theorems `thm:order-mass` and `thm:single-root` of the blueprint.
The identity is proved first for root sets with at least two
elements, by induction on the number of non-roots. The induction
step enlarges the root set, so it stays within this class. The
single-root normalization is then obtained from the case of two
roots through the transfer onto a one-vertex base; it reads a
one-by-one determinant as its entry and does not use the value of
the determinant on the empty index set.
-/

open Finset Matrix

namespace EAB.Paper

open Foundation

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {K : Type*} [Field K]

/-! ## One non-root -/

/-- The case `k = 1` of the order-mass identity. The aggregation
matrix is `I - 𝟏 e_{i₀}ᵀ`, where `i₀` is the parent of the only
non-root, and its principal cofactors are computed by the
identity-plus-rank-one formula. -/
theorem orderMass_eq_cofactor_of_single_nonroot (L : Matrix V V K)
    (hL : L *ᵥ (fun _ => 1) = 0) (B : Finset V)
    (f : ParentAssignment B) (hpm : IsPaperParentMap B f)
    (hcard : (univ \ B).card = 1)
    (hminor : MinorCondition L B f) (i : B) :
    orderMass L B f i =
      principalCofactor B
        (aggregation L B (rootIndicator B f hpm)) i := by
  classical
  have hB : B ≠ univ := by
    intro h
    rw [h, Finset.sdiff_self, Finset.card_empty] at hcard
    omega
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
  have haZ : a ∈ univ \ B := by
    rw [ha]
    exact Finset.mem_singleton_self a
  let w : (univ \ B : Finset V) := ⟨a, haZ⟩
  have hZ : univ \ B = {(w : V)} := ha
  have hw : (w : V) ∉ B := nonroot_not_mem B w
  have hdet : (principal L B).det ≠ 0 := hminor.det_base hpm hB
  let i₀ : B := ⟨f w, parent_mem_of_single_nonroot B f hpm w hZ⟩
  have hroot : ∀ v : (univ \ B : Finset V),
      firstRoot B f hpm v = i₀ := by
    intro v
    have hv : v = w := by
      apply Subtype.ext
      have hmem : (v : V) ∈ ({(w : V)} : Finset V) := by
        rw [← hZ]
        exact v.2
      exact Finset.mem_singleton.mp hmem
    rw [hv]
    exact firstRoot_child B f hpm (w : V) hw i₀ rfl
  -- The left side is the indicator of `i = i₀`.
  have hleft : orderMass L B f i = if i₀ = i then 1 else 0 := by
    unfold orderMass
    rw [growthOrders_of_single_nonroot B f hpm w hZ,
      Finset.filter_singleton]
    have hfirst : firstParent (extendParents B f) [(w : V)] =
        some (i₀ : V) := by
      simp only [firstParent, List.head?_cons, Option.map_some]
      rw [extendParents_nonroot B f hw]
    rw [hfirst]
    by_cases hi : i₀ = i
    · rw [if_pos (by rw [hi]), if_pos hi, Finset.sum_singleton]
      rfl
    · rw [if_neg (fun h => hi (Subtype.ext (Option.some.inj h))),
        if_neg hi, Finset.sum_empty]
  -- The aggregation matrix is the identity plus a rank-one matrix.
  let y : B → K := fun j => if i₀ = j then 1 else 0
  have hN : aggregation L B (rootIndicator (K := K) B f hpm) =
      1 + Matrix.vecMulVec (fun _ : B => (-1 : K)) y := by
    funext x j
    rw [aggregation_apply]
    have hcolumn : (fun v => rootIndicator (K := K) B f hpm v j) =
        if i₀ = j then (fun _ : (univ \ B : Finset V) => (1 : K))
          else 0 := by
      funext v
      simp only [rootIndicator, hroot v]
      by_cases hj : i₀ = j
      · simp [hj]
      · simp [hj]
    rw [hcolumn]
    by_cases hj : i₀ = j
    · rw [if_pos hj, harmonic_one L B hL hdet]
      simp [Matrix.vecMulVec_apply, y, hj, sub_eq_add_neg]
    · rw [if_neg hj, harmonic_zero L B hdet]
      simp [Matrix.vecMulVec_apply, y, hj]
  have hminorMatrix :
      eraseMinor B (aggregation L B (rootIndicator (K := K) B f hpm)) i =
        1 + Matrix.vecMulVec (fun _ : (B.erase (i : V)) => (-1 : K))
          (fun u => y ⟨u.1, Finset.mem_of_mem_erase u.2⟩) := by
    rw [hN]
    funext u v
    have huv : ((⟨u.1, Finset.mem_of_mem_erase u.2⟩ : B) =
        ⟨v.1, Finset.mem_of_mem_erase v.2⟩) ↔ u = v :=
      ⟨fun h => Subtype.ext (Subtype.mk.inj h),
        fun h => by rw [h]⟩
    simp only [eraseMinor, Matrix.submatrix_apply, Matrix.add_apply,
      Matrix.one_apply, Matrix.vecMulVec_apply, huv]
  rw [hleft, principalCofactor, hminorMatrix, det_one_add_rank_one]
  by_cases hi : i₀ = i
  · rw [if_pos hi]
    have hzero : ∀ u : (B.erase (i : V)),
        y ⟨u.1, Finset.mem_of_mem_erase u.2⟩ = 0 := by
      intro u
      simp only [y]
      rw [if_neg]
      intro hu
      exact (Finset.mem_erase.mp u.2).1
        ((congrArg Subtype.val hu).symm.trans (congrArg Subtype.val hi))
    simp [hzero]
  · rw [if_neg hi]
    have hmem : (i₀ : V) ∈ B.erase (i : V) :=
      Finset.mem_erase.mpr
        ⟨fun h => hi (Subtype.ext h), i₀.2⟩
    rw [Fintype.sum_eq_single (⟨(i₀ : V), hmem⟩ : (B.erase (i : V)))]
    · simp [y]
    · intro u hu
      simp only [y]
      rw [if_neg, zero_mul]
      intro h
      exact hu (Subtype.ext (congrArg Subtype.val h).symm)

/-! ## The induction step -/

/-- The induction step of the order-mass identity, for at least two
non-roots. The hypothesis `ih` is the identity for the root sets
`B ∪ {w}`, `w` a child of the root `i`. -/
theorem orderMass_eq_cofactor_step (L : Matrix V V K)
    (hL : L *ᵥ (fun _ => 1) = 0) (B : Finset V) (hBne : B.Nonempty)
    (f : ParentAssignment B) (hpm : IsPaperParentMap B f)
    (hk : 2 ≤ (univ \ B).card)
    (hminor : MinorCondition L B f) (i : B)
    (ih : ∀ w ∈ children B f i,
      ∀ x : (insert (w : V) B : Finset V),
        orderMass L (insert (w : V) B) (peelParents B f (w : V)) x =
          principalCofactor (insert (w : V) B)
            (aggregation L (insert (w : V) B)
              (rootIndicator (insert (w : V) B)
                (peelParents B f (w : V))
                (peelParents_isParentMap B f hpm (w : V)))) x) :
    orderMass L B f i =
      principalCofactor B
        (aggregation L B (rootIndicator B f hpm)) i := by
  classical
  have hB : B ≠ univ := by
    intro h
    rw [h, Finset.sdiff_self, Finset.card_empty] at hk
    omega
  have hdetB : (principal L B).det ≠ 0 := hminor.det_base hpm hB
  let M : Matrix (univ \ B : Finset V) B K := rootIndicator B f hpm
  let N : Matrix B B K := aggregation L B M
  let d : B → K := fun x => principalCofactor B N x
  have hrow : N *ᵥ (fun _ => 1) = 0 :=
    aggregation_zero_row_sum L B M hL hdetB
      (rootIndicator_unitRowSums B f hpm)
  -- Equation `eq:left-kernel`.
  have hker : d ᵥ* N = 0 :=
    principalCofactor_left_kernel B N hBne hrow
  -- One child of `i`: peel, apply the hypothesis, transfer, fold.
  have hchildSum : ∀ w ∈ children B f i,
      ∑ τ ∈ (growthOrders B f).filter
          (fun τ => τ.head? = some (w : V)),
          orderWeight L (extendParents B f) B τ =
        ∑ x : B, harmonic L B (descendantIndicator B f hpm w) x *
          d x := by
    intro w hwi
    have hw : (w : V) ∉ B := nonroot_not_mem B w
    have hchild : f w = (i : V) := (Finset.mem_filter.mp hwi).2
    have hchildB : f w ∈ B := hchild.symm ▸ i.2
    have hpm' := peelParents_isParentMap B f hpm (w : V)
    have hB' : insert (w : V) B ≠ univ :=
      insert_ne_univ_of_two_le B (w : V) hw hk
    have hdetB' : (principal L (insert (w : V) B)).det ≠ 0 :=
      (hminor.peel w hchildB).det_base hpm' hB'
    have hθ : ∑ j : B, (Pi.single i (1 : K) : B → K) j = 1 := by
      simp
    calc
      ∑ τ ∈ (growthOrders B f).filter
          (fun τ => τ.head? = some (w : V)),
          orderWeight L (extendParents B f) B τ
          = ∑ x : (insert (w : V) B : Finset V),
              gamma L B (w : V) (x : V) *
                orderMass L (insert (w : V) B)
                  (peelParents B f (w : V)) x :=
            sum_orders_with_head L B f w hchildB hk
      _ = ∑ x : (insert (w : V) B : Finset V),
            gamma L B (w : V) (x : V) *
              principalCofactor (insert (w : V) B)
                (aggregation L (insert (w : V) B)
                  (rootIndicator (insert (w : V) B)
                    (peelParents B f (w : V)) hpm')) x := by
            apply Finset.sum_congr rfl
            intro x _
            rw [ih w hwi x]
      _ = ∑ x : B,
            harmonic L B (transferBoundary B (w : V) hw
              (rootIndicator (insert (w : V) B)
                (peelParents B f (w : V)) hpm')) x *
            principalCofactor B (aggregation L B
              (fold B (w : V) hw
                (rootIndicator (insert (w : V) B)
                  (peelParents B f (w : V)) hpm')
                (Pi.single i 1))) x :=
            one_vertex_transfer L B hBne (w : V) hw hB' hL hdetB
              hdetB' _ (rootIndicator_unitRowSums _ _ hpm') _ hθ
      _ = ∑ x : B, harmonic L B (descendantIndicator B f hpm w) x *
            d x := by
            rw [← rootIndicator_eq_fold B f hpm (w : V) hw i hchild hpm',
              transferBoundary_rootIndicator B f hpm (w : V) hw
                hchildB hpm']
  -- The column `i` of the aggregation matrix, equation
  -- `eq:aggregation-column`.
  have hcolumn : ∀ x : B,
      harmonic L B (fun v => M v i) x =
        (1 : Matrix B B K) x i - N x i := by
    intro x
    have h := aggregation_apply L B M x i
    change N x i = _ at h
    rw [h]
    ring
  calc
    orderMass L B f i
        = ∑ w ∈ children B f i, ∑ x : B,
            harmonic L B (descendantIndicator B f hpm w) x * d x := by
          rw [orderMass_eq_sum_children]
          exact Finset.sum_congr rfl hchildSum
    _ = ∑ x : B, harmonic L B (fun v => M v i) x * d x := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro x _
          rw [← Finset.sum_mul]
          congr 1
          have hsum := congrFun
            (harmonic_sum L B hdetB (children B f i)
              (fun w => descendantIndicator (K := K) B f hpm w)) x
          rw [sum_descendantIndicator, Finset.sum_apply] at hsum
          exact hsum.symm
    _ = ∑ x : B, ((1 : Matrix B B K) x i - N x i) * d x := by
          apply Finset.sum_congr rfl
          intro x _
          rw [hcolumn x]
    _ = d i - (d ᵥ* N) i := by
          simp only [sub_mul, Finset.sum_sub_distrib]
          congr 1
          · simp [Matrix.one_apply]
          · simp only [Matrix.vecMul, dotProduct]
            apply Finset.sum_congr rfl
            intro x _
            ring
    _ = d i := by
          rw [hker]
          simp

/-! ## Root sets with at least two elements -/

/-- The order-mass identity for root sets with at least two
elements, by induction on the number of non-roots. -/
theorem orderMass_eq_cofactor_of_two_le (L : Matrix V V K)
    (hL : L *ᵥ (fun _ => 1) = 0) :
    ∀ (k : ℕ) (B : Finset V) (f : ParentAssignment B)
      (hpm : IsPaperParentMap B f),
      (univ \ B).card = k + 1 → 2 ≤ B.card →
      MinorCondition L B f → ∀ i : B,
      orderMass L B f i =
        principalCofactor B
          (aggregation L B (rootIndicator B f hpm)) i := by
  intro k
  induction k with
  | zero =>
      intro B f hpm hcard _ hminor i
      exact orderMass_eq_cofactor_of_single_nonroot L hL B f hpm
        hcard hminor i
  | succ k ih =>
      intro B f hpm hcard hB2 hminor i
      have hBne : B.Nonempty := Finset.card_pos.mp (by omega)
      apply orderMass_eq_cofactor_step L hL B hBne f hpm (by omega)
        hminor i
      intro w hwi x
      have hw : (w : V) ∉ B := nonroot_not_mem B w
      have hchildB : f w ∈ B :=
        (Finset.mem_filter.mp hwi).2.symm ▸ i.2
      have hcard' : (univ \ insert (w : V) B).card = k + 1 := by
        have := card_sdiff_insert B (w : V) hw
        omega
      have hB2' : 2 ≤ (insert (w : V) B).card := by
        rw [Finset.card_insert_of_notMem hw]
        omega
      exact ih (insert (w : V) B) (peelParents B f (w : V))
        (peelParents_isParentMap B f hpm (w : V)) hcard' hB2'
        (hminor.peel w hchildB) x

/-! ## One root -/

/-- With one root, every growth order enters at that root. -/
theorem sum_orderWeight_eq_orderMass_of_card_one (L : Matrix V V K)
    (B : Finset V) (hcard : B.card = 1) (hB : B ≠ univ)
    (f : ParentAssignment B) (r : B) :
    ∑ τ ∈ growthOrders B f, orderWeight L (extendParents B f) B τ =
      orderMass L B f r := by
  haveI : Subsingleton B :=
    Fintype.card_le_one_iff_subsingleton.mp (by
      rw [Fintype.card_coe]
      omega)
  rw [sum_growthOrders_by_firstParent B f hB,
    Fintype.sum_subsingleton _ r]
  rfl

/-- Theorem `thm:single-root`. With one root, the weights of the
growth orders sum to one. The proof uses the order-mass identity for
a two-element root set, the transfer onto a one-vertex base, and the
unit boundary identity. -/
theorem single_root_normalization (L : Matrix V V K)
    (hL : L *ᵥ (fun _ => 1) = 0) (B : Finset V)
    (hcard : B.card = 1) (hB : B ≠ univ)
    (f : ParentAssignment B) (hpm : IsPaperParentMap B f)
    (hminor : MinorCondition L B f) :
    ∑ τ ∈ growthOrders B f,
      orderWeight L (extendParents B f) B τ = 1 := by
  classical
  obtain ⟨r₀, hr₀⟩ := Finset.card_eq_one.mp hcard
  let r : B := ⟨r₀, by rw [hr₀]; exact Finset.mem_singleton_self r₀⟩
  haveI : Subsingleton B :=
    Fintype.card_le_one_iff_subsingleton.mp (by
      rw [Fintype.card_coe]
      omega)
  have hkpos : 0 < (univ \ B).card := by
    apply Finset.card_pos.mpr
    obtain ⟨τ, hτ⟩ := growthOrders_nonempty_of_proper B f hpm hB
    have hGO := (mem_growthOrders_iff B f τ).mp hτ
    cases τ with
    | nil => exact absurd rfl (hGO.ne_nil hB)
    | cons y rest =>
        exact ⟨y, Finset.mem_sdiff.mpr
          ⟨Finset.mem_univ y, hGO.not_mem_roots (by simp)⟩⟩
  rcases Nat.lt_or_ge (univ \ B).card 2 with hk1 | hk
  · -- One non-root: the only growth order has the empty product.
    have hcard1 : (univ \ B).card = 1 := by omega
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard1
    have haZ : a ∈ univ \ B := by
      rw [ha]
      exact Finset.mem_singleton_self a
    rw [growthOrders_of_single_nonroot B f hpm ⟨a, haZ⟩ ha,
      Finset.sum_singleton]
    rfl
  · -- At least two non-roots.
    have hdetB : (principal L B).det ≠ 0 := hminor.det_base hpm hB
    have hchildSum : ∀ w ∈ children B f r,
        ∑ τ ∈ (growthOrders B f).filter
            (fun τ => τ.head? = some (w : V)),
            orderWeight L (extendParents B f) B τ =
          harmonic L B (descendantIndicator B f hpm w) r := by
      intro w hwr
      have hw : (w : V) ∉ B := nonroot_not_mem B w
      have hchildB : f w ∈ B :=
        (Finset.mem_filter.mp hwr).2.symm ▸ r.2
      have hpm' := peelParents_isParentMap B f hpm (w : V)
      have hB' : insert (w : V) B ≠ univ :=
        insert_ne_univ_of_two_le B (w : V) hw hk
      have hminor' := hminor.peel w hchildB
      have hdetB' : (principal L (insert (w : V) B)).det ≠ 0 :=
        hminor'.det_base hpm' hB'
      obtain ⟨k', hk'⟩ : ∃ k', (univ \ insert (w : V) B).card = k' + 1 := by
        have := card_sdiff_insert B (w : V) hw
        exact ⟨(univ \ insert (w : V) B).card - 1, by omega⟩
      have hB2' : 2 ≤ (insert (w : V) B).card := by
        rw [Finset.card_insert_of_notMem hw]
        omega
      calc
        ∑ τ ∈ (growthOrders B f).filter
            (fun τ => τ.head? = some (w : V)),
            orderWeight L (extendParents B f) B τ
            = ∑ x : (insert (w : V) B : Finset V),
                gamma L B (w : V) (x : V) *
                  orderMass L (insert (w : V) B)
                    (peelParents B f (w : V)) x :=
              sum_orders_with_head L B f w hchildB hk
        _ = ∑ x : (insert (w : V) B : Finset V),
              gamma L B (w : V) (x : V) *
                principalCofactor (insert (w : V) B)
                  (aggregation L (insert (w : V) B)
                    (rootIndicator (insert (w : V) B)
                      (peelParents B f (w : V)) hpm')) x := by
              apply Finset.sum_congr rfl
              intro x _
              rw [orderMass_eq_cofactor_of_two_le L hL k'
                (insert (w : V) B) (peelParents B f (w : V)) hpm'
                hk' hB2' hminor' x]
        _ = harmonic L B (transferBoundary B (w : V) hw
              (rootIndicator (insert (w : V) B)
                (peelParents B f (w : V)) hpm')) r :=
              one_vertex_transfer_singleton L B hcard r (w : V) hw
                hB' hL hdetB hdetB' _
                (rootIndicator_unitRowSums _ _ hpm')
        _ = harmonic L B (descendantIndicator B f hpm w) r := by
              rw [transferBoundary_rootIndicator B f hpm (w : V) hw
                hchildB hpm']
    -- The root block of the only root is the set of all non-roots.
    have hcolumn : (fun v => rootIndicator (K := K) B f hpm v r) =
        fun _ => 1 := by
      funext v
      simp [rootIndicator, Subsingleton.elim (firstRoot B f hpm v) r]
    calc
      ∑ τ ∈ growthOrders B f, orderWeight L (extendParents B f) B τ
          = orderMass L B f r :=
            sum_orderWeight_eq_orderMass_of_card_one L B hcard hB f r
      _ = ∑ w ∈ children B f r,
            harmonic L B (descendantIndicator B f hpm w) r := by
            rw [orderMass_eq_sum_children]
            exact Finset.sum_congr rfl hchildSum
      _ = harmonic L B (fun v => rootIndicator (K := K) B f hpm v r) r := by
            have hsum := congrFun
              (harmonic_sum L B hdetB (children B f r)
                (fun w => descendantIndicator (K := K) B f hpm w)) r
            rw [sum_descendantIndicator, Finset.sum_apply] at hsum
            exact hsum.symm
      _ = 1 := by
            rw [hcolumn, harmonic_one L B hL hdetB]

/-! ## The order-mass identity -/

/-- **Theorem `thm:order-mass`.** For a nonempty proper root set
`B`, a parent map `f` on the non-roots, and a zero-row-sum matrix `L`
whose principal minors are nonzero on the proper bases of the growth
orders of `f`, the order mass at every root `i` is the principal
cofactor at `i` of `I + L[B]⁻¹ L[B, V \ B] M_f`.

For one root the right side is the determinant on the empty index
set, equal to `1`, and the identity is the single-root
normalization. -/
theorem order_mass_identity (L : Matrix V V K)
    (hL : L *ᵥ (fun _ => 1) = 0) (B : Finset V)
    (hBne : B.Nonempty) (hB : B ≠ univ)
    (f : ParentAssignment B) (hpm : IsPaperParentMap B f)
    (hminor : MinorCondition L B f) (i : B) :
    orderMass L B f i =
      principalCofactor B
        (aggregation L B (rootIndicator B f hpm)) i := by
  classical
  have hBpos : 0 < B.card := Finset.card_pos.mpr hBne
  rcases Nat.lt_or_ge B.card 2 with h1 | h2
  · have hcard : B.card = 1 := by omega
    rw [← sum_orderWeight_eq_orderMass_of_card_one L B hcard hB f i,
      single_root_normalization L hL B hcard hB f hpm hminor]
    obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hcard
    subst hr
    obtain ⟨i, hi⟩ := i
    have hir : i = r := Finset.mem_singleton.mp hi
    subst hir
    exact (principalCofactor_singleton i _).symm
  · obtain ⟨k, hk⟩ : ∃ k, (univ \ B).card = k + 1 := by
      have hpos : 0 < (univ \ B).card := by
        apply Finset.card_pos.mpr
        by_contra hempty
        rw [Finset.not_nonempty_iff_eq_empty] at hempty
        apply hB
        exact Finset.eq_univ_iff_forall.mpr fun x => by
          by_contra hx
          have hmem : x ∈ univ \ B :=
            Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩
          rw [hempty] at hmem
          exact Finset.notMem_empty x hmem
      exact ⟨(univ \ B).card - 1, by omega⟩
    exact orderMass_eq_cofactor_of_two_le L hL k B f hpm hk h2 hminor i

end EAB.Paper
