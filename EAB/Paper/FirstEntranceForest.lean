import EAB.Paper.JointOrder
import EAB.Paper.OrderMass

/-!
# The first-entrance forest

The first-entrance forest of the walk records, for every non-root
`v`, the state `X_{T_v - 1}` from which `v` is first entered. This
file proves the second part of Lemma `lem:cover`, that these edges
form a parent map, and writes the event that the forest equals a
given parent assignment as the disjoint union, over the orderings
of the non-roots, of the events of Lemma `lem:excursion`. Only
growth orders contribute.
-/

open MeasureTheory ProbabilityTheory Finset

namespace EAB.Paper.Chain

open Foundation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## The forest and its events -/

/-- The first-entrance parent assignment on the non-roots. -/
noncomputable def entranceForest (B : Finset V) (ω : ℕ → V) :
    ParentAssignment B :=
  fun v => entranceParent ω v

/-- The walk covers the state space and its first-entrance forest
rooted at `B` is `f`. -/
def forestEvent (B : Finset V) (f : ParentAssignment B) :
    Set (ℕ → V) :=
  {ω | (∀ v, Hits ω v) ∧ entranceForest B ω = f}

/-- Lemma `lem:cover`, second part. Following parents strictly
decreases first-entrance times, so every non-root reaches a root. -/
theorem isPaperParentMap_entranceForest (B : Finset V) (ω : ℕ → V)
    (h0 : ω 0 ∈ B) (hhits : ∀ v, v ∉ B → Hits ω v) :
    IsPaperParentMap B (entranceForest B ω) := by
  have hpos : ∀ v, v ∉ B → 1 ≤ hitTime ω v := by
    intro v hv
    by_contra hlt
    have hzero : hitTime ω v = 0 := by omega
    have hspec := hitTime_spec (hhits v hv)
    rw [hzero] at hspec
    exact hv (hspec ▸ h0)
  have hkey : ∀ N : ℕ, ∀ v, v ∉ B → hitTime ω v ≤ N →
      ∃ n : ℕ,
        (extendParents B (entranceForest B ω))^[n + 1] v ∈ B := by
    intro N
    induction N with
    | zero =>
        intro v hv hle
        have := hpos v hv
        omega
    | succ N ih =>
        intro v hv hle
        have hstep : extendParents B (entranceForest B ω) v =
            ω (hitTime ω v - 1) := by
          rw [extendParents_nonroot B _ hv]
          rfl
        by_cases hu : ω (hitTime ω v - 1) ∈ B
        · refine ⟨0, ?_⟩
          rw [Function.iterate_one, hstep]
          exact hu
        · have hule : hitTime ω (ω (hitTime ω v - 1)) ≤ N := by
            have h1 : hitTime ω (ω (hitTime ω v - 1)) ≤
                hitTime ω v - 1 := hitTime_le rfl
            have h2 := hpos v hv
            omega
          obtain ⟨n, hn⟩ := ih _ hu hule
          refine ⟨n + 1, ?_⟩
          rw [Function.iterate_succ_apply, hstep]
          exact hn
  intro v
  exact hkey (hitTime ω v) v (nonroot_not_mem B v) le_rfl

/-! ## Existence and uniqueness of the discovery order -/

omit [Fintype V] in
theorem exists_pairwise_hitTime (ω : ℕ → V) :
    ∀ S : Finset V, (∀ v ∈ S, Hits ω v) →
      ∃ τ : List V, τ.toFinset = S ∧
        τ.Pairwise fun u v => hitTime ω u < hitTime ω v := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
      intro hhits
      by_cases hS : S.Nonempty
      · obtain ⟨z, hzS, hmin⟩ := S.exists_min_image (hitTime ω) hS
        obtain ⟨rest, hrest, hpair⟩ := ih (S.erase z)
          (Finset.erase_ssubset hzS)
          (fun v hv => hhits v (Finset.mem_of_mem_erase hv))
        refine ⟨z :: rest, ?_, List.pairwise_cons.mpr ⟨?_, hpair⟩⟩
        · rw [List.toFinset_cons, hrest, Finset.insert_erase hzS]
        · intro v hv
          have hvmem : v ∈ S.erase z := by
            rw [← hrest]
            exact List.mem_toFinset.mpr hv
          obtain ⟨hvz, hvS⟩ := Finset.mem_erase.mp hvmem
          apply lt_of_le_of_ne (hmin v hvS)
          intro heq
          apply hvz
          have h1 := hitTime_spec (hhits v hvS)
          have h2 := hitTime_spec (hhits z hzS)
          rw [← heq] at h1
          exact h1.symm.trans h2
      · refine ⟨[], ?_, List.Pairwise.nil⟩
        rw [Finset.not_nonempty_iff_eq_empty.mp hS]
        rfl

theorem IsDiscoveryOrder.nodup {U : Finset V}
    {ω : ℕ → V} {τ : List V} (h : IsDiscoveryOrder U ω τ) :
    τ.Nodup :=
  h.2.2.imp fun hlt heq => by
    rw [heq] at hlt
    exact lt_irrefl _ hlt

/-- A trajectory has at most one discovery order. -/
theorem IsDiscoveryOrder.unique {U : Finset V} {ω : ℕ → V}
    {τ τ' : List V} (h : IsDiscoveryOrder U ω τ)
    (h' : IsDiscoveryOrder U ω τ') : τ = τ' :=
  List.Perm.eq_of_pairwise
    (le := fun u v => hitTime ω u < hitTime ω v)
    (fun _ _ _ _ hab hba => absurd hab (not_lt.mpr hba.le))
    h.2.2 h'.2.2
    (List.perm_of_nodup_nodup_toFinset_eq h.nodup h'.nodup
      (h.1.trans h'.1.symm))

/-- The orderings of the non-roots. -/
noncomputable def orderings (B : Finset V) : Finset (List V) :=
  (univ \ B).toList.permutations.toFinset

theorem mem_orderings (B : Finset V) (τ : List V) :
    τ ∈ orderings B ↔ τ.Nodup ∧ τ.toFinset = univ \ B := by
  unfold orderings
  rw [List.mem_toFinset, List.mem_permutations]
  constructor
  · intro hperm
    refine ⟨hperm.nodup_iff.mpr (Finset.nodup_toList _), ?_⟩
    rw [List.toFinset_eq_of_perm _ _ hperm, Finset.toList_toFinset]
  · rintro ⟨hnodup, hfin⟩
    exact List.perm_of_nodup_nodup_toFinset_eq hnodup
      (Finset.nodup_toList _) (by rw [hfin, Finset.toList_toFinset])

/-! ## Growth orders among the orderings -/

/-- Every vertex of the order has its parent in the base that
precedes it. -/
def ParentsBefore (g : V → V) : Finset V → List V → Prop
  | _, [] => True
  | U, z :: rest => g z ∈ U ∧ ParentsBefore g (insert z U) rest

omit [Fintype V] in
theorem parentsBefore_iff (g : V → V) :
    ∀ (τ : List V) (U : Finset V), ParentsBefore g U τ ↔
      ∀ i : Fin τ.length, g (τ.get i) ∈ U ∪ (τ.take i).toFinset := by
  intro τ
  induction τ with
  | nil =>
      intro U
      simp only [ParentsBefore, true_iff]
      intro i
      exact absurd i.2 (by simp)
  | cons z rest ih =>
      intro U
      have hbase : ∀ l : ℕ, U ∪ ((z :: rest).take (l + 1)).toFinset =
          insert z U ∪ (rest.take l).toFinset := by
        intro l
        ext x
        simp
      simp only [ParentsBefore]
      rw [ih (insert z U)]
      constructor
      · rintro ⟨h0, hrest⟩ ⟨n, hn⟩
        cases n with
        | zero => simpa using h0
        | succ n =>
            have hn' : n < rest.length := by simpa using hn
            have h := hrest ⟨n, hn'⟩
            rw [← hbase] at h
            simpa using h
      · intro h
        refine ⟨by simpa using h ⟨0, by simp⟩, fun i => ?_⟩
        have hi := h ⟨i.1 + 1, by simp⟩
        rw [← hbase]
        simpa using hi

theorem mem_growthOrders_iff_parentsBefore (B : Finset V)
    (f : ParentAssignment B) (τ : List V) :
    τ ∈ growthOrders B f ↔
      τ ∈ orderings B ∧ ParentsBefore (extendParents B f) B τ := by
  rw [mem_growthOrders_iff, mem_orderings, parentsBefore_iff]
  exact and_assoc.symm

variable [MeasurableSpace V] [MeasurableSingletonClass V]

omit [MeasurableSpace V] [MeasurableSingletonClass V] in
/-- An ordering in which some vertex precedes its parent has zero
weight. -/
theorem excursionWeight_eq_zero (P : Matrix V V ℝ) (g : V → V) :
    ∀ (τ : List V) (U : Finset V) (a : V),
      ¬ ParentsBefore g U τ → excursionWeight P g U a τ = 0 := by
  intro τ
  induction τ with
  | nil =>
      intro U a h
      exact absurd trivial h
  | cons z rest ih =>
      intro U a h
      simp only [ParentsBefore, not_and] at h
      simp only [excursionWeight]
      by_cases hgz : g z ∈ U
      · rw [ih (insert z U) z (h hgz), mul_zero]
      · have hgreen : green P U a (g z) = 0 := by
          unfold green
          rw [dif_neg (fun h' => hgz h'.2)]
        rw [hgreen, zero_mul, zero_mul]

/-! ## The forest event as a union over discovery orders -/

/-- The union over the orderings of the events of a discovery order
with the parents of `f`. -/
def orderUnion (B : Finset V) (r : V) (f : ParentAssignment B) :
    Set (ℕ → V) :=
  ⋃ τ ∈ orderings B, orderEvent (extendParents B f) B r τ

omit [MeasurableSpace V] [MeasurableSingletonClass V] in
theorem forestEvent_inter_start (B : Finset V) (r : V)
    (f : ParentAssignment B) :
    forestEvent B f ∩ {ω | ω 0 = r} =
      orderUnion B r f ∩ {ω | ∀ v, Hits ω v} := by
  apply Set.ext
  intro ω
  simp only [forestEvent, orderUnion, orderEvent, Set.mem_inter_iff,
    Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨⟨hcover, hforest⟩, h0⟩
    obtain ⟨τ, hfin, hpair⟩ := exists_pairwise_hitTime ω (univ \ B)
      (fun v _ => hcover v)
    have hdisc : IsDiscoveryOrder B ω τ :=
      ⟨hfin, fun v _ => hcover v, hpair⟩
    refine ⟨⟨τ, (mem_orderings B τ).mpr ⟨hdisc.nodup, hfin⟩, h0,
      hdisc, ?_⟩, hcover⟩
    intro v hv
    have hvB : v ∉ B := by
      have hmem : v ∈ τ.toFinset := List.mem_toFinset.mpr hv
      rw [hfin] at hmem
      exact (Finset.mem_sdiff.mp hmem).2
    rw [extendParents_nonroot B f hvB, ← hforest]
    rfl
  · rintro ⟨⟨τ, -, h0, hdisc, hpar⟩, hcover⟩
    refine ⟨⟨hcover, ?_⟩, h0⟩
    funext v
    have hv : (v : V) ∈ τ := by
      apply List.mem_toFinset.mp
      rw [hdisc.1]
      exact v.2
    have h := hpar v hv
    rw [extendParents_nonroot B f (nonroot_not_mem B v)] at h
    exact h

theorem measurableSet_orderUnion (B : Finset V) (r : V) (hr : r ∈ B)
    (f : ParentAssignment B) : MeasurableSet (orderUnion B r f) := by
  apply Finset.measurableSet_biUnion
  intro τ hτ
  obtain ⟨hnodup, hfin⟩ := (mem_orderings B τ).mp hτ
  apply measurableSet_orderEvent _ τ B r hr _ hnodup
  intro z hz
  have hmem : z ∈ τ.toFinset := List.mem_toFinset.mpr hz
  rw [hfin] at hmem
  exact (Finset.mem_sdiff.mp hmem).2

omit [MeasurableSpace V] [MeasurableSingletonClass V] in
/-- The unions of distinct parent assignments are disjoint: the
entrance parents determine the assignment. -/
theorem disjoint_orderUnion (B : Finset V) (r : V)
    {f f' : ParentAssignment B} (hne : f ≠ f') :
    Disjoint (orderUnion B r f) (orderUnion B r f') := by
  apply Set.disjoint_left.mpr
  intro ω hω hω'
  simp only [orderUnion, orderEvent, Set.mem_iUnion,
    Set.mem_setOf_eq, exists_prop] at hω hω'
  obtain ⟨τ, -, -, hdisc, hpar⟩ := hω
  obtain ⟨τ', -, -, hdisc', hpar'⟩ := hω'
  apply hne
  funext v
  have hv : (v : V) ∈ τ := by
    apply List.mem_toFinset.mp
    rw [hdisc.1]
    exact v.2
  have hv' : (v : V) ∈ τ' := by
    apply List.mem_toFinset.mp
    rw [hdisc'.1]
    exact v.2
  have h1 := hpar v hv
  have h2 := hpar' v hv'
  rw [extendParents_nonroot B f (nonroot_not_mem B v)] at h1
  rw [extendParents_nonroot B f' (nonroot_not_mem B v)] at h2
  exact h1.symm.trans h2

/-- Almost surely the forest event is the union over the discovery
orders. -/
theorem chainLaw_forestEvent_eq_orderUnion (P : Matrix V V ℝ)
    (hP : IsStochastic P) (hirr : IsIrreducible P) (B : Finset V)
    (r : V) (f : ParentAssignment B) :
    chainLaw P hP r (forestEvent B f) =
      chainLaw P hP r (orderUnion B r f) := by
  have hcover : chainLaw P hP r {ω | ∀ v, Hits ω v}ᶜ = 0 :=
    ae_iff.mp (ae_hits_all P hP hirr r)
  rw [← chainLaw_inter_start P hP r (forestEvent B f),
    forestEvent_inter_start B r f, measure_inter_conull hcover]

/-- The law of the first-entrance forest as a sum over orderings of
the weights of Lemma `lem:excursion`. -/
theorem chainLaw_forestEvent (P : Matrix V V ℝ) (hP : IsStochastic P)
    (hirr : IsIrreducible P) (B : Finset V) (r : V) (hr : r ∈ B)
    (f : ParentAssignment B) :
    chainLaw P hP r (forestEvent B f) =
      ∑ τ ∈ orderings B, ENNReal.ofReal
        (excursionWeight P (extendParents B f) B r τ) := by
  rw [chainLaw_forestEvent_eq_orderUnion P hP hirr B r f,
    orderUnion, measure_biUnion_finset]
  · apply Finset.sum_congr rfl
    intro τ hτ
    obtain ⟨hnodup, hfin⟩ := (mem_orderings B τ).mp hτ
    exact chainLaw_orderEvent P hP hirr _ τ B r hr hnodup hfin
  · intro τ _ τ' _ hne
    apply Set.disjoint_left.mpr
    rintro ω ⟨-, hdisc, -⟩ ⟨-, hdisc', -⟩
    exact hne (hdisc.unique hdisc')
  · intro τ hτ
    obtain ⟨hnodup, hfin⟩ := (mem_orderings B τ).mp hτ
    apply measurableSet_orderEvent _ τ B r hr _ hnodup
    intro z hz
    have hmem : z ∈ τ.toFinset := List.mem_toFinset.mpr hz
    rw [hfin] at hmem
    exact (Finset.mem_sdiff.mp hmem).2

/-- Only growth orders contribute. -/
theorem chainLaw_forestEvent_growthOrders (P : Matrix V V ℝ)
    (hP : IsStochastic P) (hirr : IsIrreducible P) (B : Finset V)
    (r : V) (hr : r ∈ B) (f : ParentAssignment B) :
    chainLaw P hP r (forestEvent B f) =
      ∑ τ ∈ growthOrders B f, ENNReal.ofReal
        (excursionWeight P (extendParents B f) B r τ) := by
  rw [chainLaw_forestEvent P hP hirr B r hr f]
  symm
  apply Finset.sum_subset
  · intro τ hτ
    exact ((mem_growthOrders_iff_parentsBefore B f τ).mp hτ).1
  · intro τ hτ hnot
    have hparents : ¬ ParentsBefore (extendParents B f) B τ :=
      fun h => hnot
        ((mem_growthOrders_iff_parentsBefore B f τ).mpr ⟨hτ, h⟩)
    rw [excursionWeight_eq_zero P _ τ B r hparents,
      ENNReal.ofReal_zero]

end EAB.Paper.Chain
