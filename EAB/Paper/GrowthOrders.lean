import EAB.Paper.ForestSpecialization

/-!
# Growth orders: bases, existence and peeling

This file proves the combinatorial part of Lemma `lem:orders` of the
blueprint. A growth order of a parent map on the non-roots of `B`
starts at a child `w` of a root, and its remaining vertices form a
growth order of the restricted parent map for the root set `B ∪ {w}`.
Peeling is used only when at least two non-roots are present.
-/

open Finset

namespace EAB.Paper

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Bases -/

/-- The base `U_l = B ∪ {τ_1, …, τ_l}` of an order after `l` steps. -/
def orderBase (B : Finset V) (τ : List V) (l : ℕ) : Finset V :=
  B ∪ (τ.take l).toFinset

omit [Fintype V] in
@[simp] theorem orderBase_zero (B : Finset V) (τ : List V) :
    orderBase B τ 0 = B := by
  simp [orderBase]

omit [Fintype V] in
/-- Every base of the shortened order is a base of the original
order, with its prefix length increased by one. -/
theorem orderBase_cons_succ (B : Finset V) (w : V) (τ : List V) (l : ℕ) :
    orderBase B (w :: τ) (l + 1) = orderBase (insert w B) τ l := by
  ext x
  simp [orderBase]

/-! ## Elementary facts about one growth order -/

theorem IsGrowthOrder.not_mem_roots {B : Finset V}
    {f : ParentAssignment B} {τ : List V} (h : IsGrowthOrder B f τ)
    {z : V} (hz : z ∈ τ) : z ∉ B := by
  have hmem : z ∈ τ.toFinset := List.mem_toFinset.mpr hz
  rw [h.2.1] at hmem
  exact (Finset.mem_sdiff.mp hmem).2

theorem IsGrowthOrder.ne_nil {B : Finset V}
    {f : ParentAssignment B} {τ : List V} (h : IsGrowthOrder B f τ)
    (hB : B ≠ univ) : τ ≠ [] := by
  rintro rfl
  apply hB
  have hempty : univ \ B = ∅ := by simpa using h.2.1.symm
  exact Finset.eq_univ_iff_forall.mpr fun x => by
    by_contra hx
    have hmem : x ∈ univ \ B :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hx⟩
    rw [hempty] at hmem
    exact Finset.notMem_empty x hmem

/-- The first vertex of a growth order is a child of a root. -/
theorem IsGrowthOrder.head_parent_mem {B : Finset V}
    {f : ParentAssignment B} {y : V} {rest : List V}
    (h : IsGrowthOrder B f (y :: rest)) :
    extendParents B f y ∈ B := by
  have h0 := h.2.2 ⟨0, by simp⟩
  simpa using h0

theorem IsGrowthOrder.length_eq {B : Finset V}
    {f : ParentAssignment B} {τ : List V} (h : IsGrowthOrder B f τ) :
    τ.length = (univ \ B).card := by
  rw [← h.2.1, List.toFinset_card_of_nodup h.1]

/-! ## The case of one non-root -/

/-- If `w` is the only non-root, its parent is a root. -/
theorem parent_mem_of_single_nonroot (B : Finset V)
    (f : ParentAssignment B) (hpm : IsPaperParentMap B f)
    (w : (univ \ B : Finset V)) (hZ : univ \ B = {(w : V)}) :
    f w ∈ B := by
  obtain ⟨u, _, hu⟩ := last_nonroot_before_hit B f hpm w
  have huw : u = w := by
    apply Subtype.ext
    have hmem : (u : V) ∈ ({(w : V)} : Finset V) := by
      rw [← hZ]
      exact u.2
    exact Finset.mem_singleton.mp hmem
  rw [← huw, hu]
  exact firstHitTime_mem B f hpm w

/-- If `w` is the only non-root, `(w)` is the only growth order. -/
theorem isGrowthOrder_iff_of_single_nonroot (B : Finset V)
    (f : ParentAssignment B) (hpm : IsPaperParentMap B f)
    (w : (univ \ B : Finset V)) (hZ : univ \ B = {(w : V)})
    (τ : List V) :
    IsGrowthOrder B f τ ↔ τ = [(w : V)] := by
  constructor
  · intro h
    have hlen : τ.length = 1 := by
      rw [h.length_eq, hZ, Finset.card_singleton]
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hlen
    have ha : a ∈ univ \ B := by
      rw [← h.2.1]
      simp
    rw [hZ] at ha
    rw [Finset.mem_singleton.mp ha]
  · rintro rfl
    refine ⟨List.nodup_singleton _, by simpa using hZ.symm, fun i => ?_⟩
    obtain ⟨n, hn⟩ := i
    have hn0 : n = 0 := by simpa using hn
    subst hn0
    have hparent : extendParents B f (w : V) ∈ B := by
      rw [extendParents_nonroot B f (nonroot_not_mem B w)]
      exact parent_mem_of_single_nonroot B f hpm w hZ
    simpa using hparent

theorem growthOrders_of_single_nonroot (B : Finset V)
    (f : ParentAssignment B) (hpm : IsPaperParentMap B f)
    (w : (univ \ B : Finset V)) (hZ : univ \ B = {(w : V)}) :
    growthOrders B f = {[(w : V)]} := by
  ext τ
  rw [mem_growthOrders_iff, Finset.mem_singleton]
  exact isGrowthOrder_iff_of_single_nonroot B f hpm w hZ τ

/-! ## Peeling the first vertex -/

theorem sdiff_insert_eq_erase (B : Finset V) (w : V) :
    univ \ insert w B = (univ \ B).erase w := by
  ext x
  simp

theorem card_sdiff_insert (B : Finset V) (w : V) (hw : w ∉ B) :
    (univ \ insert w B).card + 1 = (univ \ B).card := by
  have hmem : w ∈ univ \ B :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hw⟩
  rw [sdiff_insert_eq_erase, Finset.card_erase_of_mem hmem]
  have hpos : 0 < (univ \ B).card := Finset.card_pos.mpr ⟨w, hmem⟩
  omega

/-- If at least two non-roots are present, the enlarged root set is
still proper. -/
theorem insert_ne_univ_of_two_le (B : Finset V) (w : V) (hw : w ∉ B)
    (hk : 2 ≤ (univ \ B).card) : insert w B ≠ univ := by
  intro h
  have hcard := card_sdiff_insert B w hw
  rw [h, Finset.sdiff_self, Finset.card_empty] at hcard
  omega

/-- Lemma `lem:orders`, the bijection. After placing the child `w`
of a root first, the condition on the subsequent vertices is the
growth-order condition for the restricted map and the root set
`B ∪ {w}`. -/
theorem isGrowthOrder_cons_iff (B : Finset V)
    (f : ParentAssignment B) (w : V) (hw : w ∉ B)
    (hchild : extendParents B f w ∈ B) (τ : List V) :
    IsGrowthOrder B f (w :: τ) ↔
      IsGrowthOrder (insert w B) (peelParents B f w) τ := by
  have hbase : ∀ l : ℕ, B ∪ ((w :: τ).take (l + 1)).toFinset =
      insert w B ∪ (τ.take l).toFinset :=
    fun l => orderBase_cons_succ B w τ l
  constructor
  · rintro ⟨hnd, hfin, hpar⟩
    have hwτ : w ∉ τ := (List.nodup_cons.mp hnd).1
    have hfin' : τ.toFinset = univ \ insert w B := by
      rw [sdiff_insert_eq_erase, ← hfin, List.toFinset_cons,
        Finset.erase_insert (by simpa using hwτ)]
    refine ⟨(List.nodup_cons.mp hnd).2, hfin', fun i => ?_⟩
    have hz : τ.get i ∉ insert w B := by
      have hmem : τ.get i ∈ τ.toFinset :=
        List.mem_toFinset.mpr (List.get_mem τ i)
      rw [hfin'] at hmem
      exact (Finset.mem_sdiff.mp hmem).2
    have h := hpar ⟨i.1 + 1, by simp⟩
    rw [peelParents_agree_off_roots B f w _ hz, ← hbase]
    simpa using h
  · rintro ⟨hnd, hfin, hpar⟩
    have hwτ : w ∉ τ := by
      intro hmem
      have hmem' : w ∈ τ.toFinset := List.mem_toFinset.mpr hmem
      rw [hfin] at hmem'
      exact (Finset.mem_sdiff.mp hmem').2 (Finset.mem_insert_self w B)
    refine ⟨List.nodup_cons.mpr ⟨hwτ, hnd⟩, ?_, fun i => ?_⟩
    · rw [List.toFinset_cons, hfin, sdiff_insert_eq_erase,
        Finset.insert_erase
          (Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hw⟩)]
    · obtain ⟨n, hn⟩ := i
      cases n with
      | zero => simpa using hchild
      | succ n =>
          have hn' : n < τ.length := by simpa using hn
          have hz : τ.get ⟨n, hn'⟩ ∉ insert w B := by
            have hmem : τ.get ⟨n, hn'⟩ ∈ τ.toFinset :=
              List.mem_toFinset.mpr (List.get_mem τ ⟨n, hn'⟩)
            rw [hfin] at hmem
            exact (Finset.mem_sdiff.mp hmem).2
          have h := hpar ⟨n, hn'⟩
          rw [peelParents_agree_off_roots B f w _ hz, ← hbase] at h
          simpa using h

/-- The growth orders with first vertex `w` are the growth orders of
the restricted map with `w` prepended. -/
theorem growthOrders_filter_head (B : Finset V)
    (f : ParentAssignment B) (w : V) (hw : w ∉ B)
    (hchild : extendParents B f w ∈ B) :
    (growthOrders B f).filter (fun τ => τ.head? = some w) =
      (growthOrders (insert w B) (peelParents B f w)).image
        (List.cons w) := by
  ext τ
  simp only [Finset.mem_filter, Finset.mem_image, mem_growthOrders_iff]
  constructor
  · rintro ⟨hτ, hhead⟩
    cases τ with
    | nil => simp at hhead
    | cons y rest =>
        have hy : y = w := by simpa using hhead
        subst hy
        exact ⟨rest, (isGrowthOrder_cons_iff B f y hw hchild rest).mp hτ,
          rfl⟩
  · rintro ⟨τ', hτ', rfl⟩
    exact ⟨(isGrowthOrder_cons_iff B f w hw hchild τ').mpr hτ', rfl⟩

/-! ## Existence -/

/-- A proper root set has a child of a root among its non-roots. -/
theorem exists_child_of_root (B : Finset V)
    (f : ParentAssignment B) (hpm : IsPaperParentMap B f)
    (hB : B ≠ univ) :
    ∃ w : (univ \ B : Finset V), f w ∈ B := by
  have hex : ∃ v : V, v ∉ B := by
    by_contra h
    exact hB (Finset.eq_univ_iff_forall.mpr fun x => by
      by_contra hx
      exact h ⟨x, hx⟩)
  obtain ⟨v, hv⟩ := hex
  let v' : (univ \ B : Finset V) :=
    ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hv⟩⟩
  obtain ⟨w, _, hw⟩ := last_nonroot_before_hit B f hpm v'
  exact ⟨w, hw ▸ firstHitTime_mem B f hpm v'⟩

/-- Lemma `lem:orders`, existence. The case of one non-root is
direct. With at least two non-roots, a child of a root is placed
first and followed by a growth order of the restricted map. -/
theorem growthOrders_nonempty :
    ∀ (k : ℕ) (B : Finset V) (f : ParentAssignment B),
      IsPaperParentMap B f → (univ \ B).card = k + 1 →
      (growthOrders B f).Nonempty := by
  intro k
  induction k with
  | zero =>
      intro B f hpm hcard
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
      have haZ : a ∈ univ \ B := by
        rw [ha]
        exact Finset.mem_singleton_self a
      exact ⟨[a], by
        rw [growthOrders_of_single_nonroot B f hpm ⟨a, haZ⟩ ha]
        exact Finset.mem_singleton_self _⟩
  | succ k ih =>
      intro B f hpm hcard
      have hB : B ≠ univ := by
        intro h
        rw [h, Finset.sdiff_self, Finset.card_empty] at hcard
        omega
      obtain ⟨w, hwchild⟩ := exists_child_of_root B f hpm hB
      have hw : (w : V) ∉ B := nonroot_not_mem B w
      have hchild : extendParents B f (w : V) ∈ B := by
        rw [extendParents_nonroot B f hw]
        exact hwchild
      have hcard' : (univ \ insert (w : V) B).card = k + 1 := by
        have := card_sdiff_insert B (w : V) hw
        omega
      obtain ⟨τ', hτ'⟩ := ih (insert (w : V) B)
        (peelParents B f (w : V))
        (peelParents_isParentMap B f hpm (w : V)) hcard'
      refine ⟨(w : V) :: τ', ?_⟩
      rw [mem_growthOrders_iff] at hτ' ⊢
      exact (isGrowthOrder_cons_iff B f (w : V) hw hchild τ').mpr hτ'

theorem growthOrders_nonempty_of_proper (B : Finset V)
    (f : ParentAssignment B) (hpm : IsPaperParentMap B f)
    (hB : B ≠ univ) : (growthOrders B f).Nonempty := by
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
  obtain ⟨k, hk⟩ : ∃ k, (univ \ B).card = k + 1 :=
    ⟨(univ \ B).card - 1, by omega⟩
  exact growthOrders_nonempty k B f hpm hk

end EAB.Paper
