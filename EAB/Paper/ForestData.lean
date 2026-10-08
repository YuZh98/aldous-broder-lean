import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Permutation
import Mathlib.Tactic

/-!
# Partial parent maps and first-hit root blocks

This module contains the finite forest objects that do not depend on the
matrix calculation. Parent maps are defined only on non-root vertices.
Their root-fixing extension is used solely to express finite iterates.
-/

open Finset Matrix

namespace EAB.Paper

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A parent assignment on precisely the non-root vertices. -/
abbrev ParentAssignment (B : Finset V) := (univ \ B : Finset V) → V

/-- Extend a partial parent assignment by fixing every root. -/
noncomputable def extendParents (B : Finset V)
    (f : ParentAssignment B) : V → V :=
  fun v => if hv : v ∈ B then v else
    f ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hv⟩⟩

theorem extendParents_root (B : Finset V)
    (f : ParentAssignment B) {v : V} (hv : v ∈ B) :
    extendParents B f v = v := by
  simp [extendParents, hv]

theorem extendParents_nonroot (B : Finset V)
    (f : ParentAssignment B) {v : V} (hv : v ∉ B) :
    extendParents B f v =
      f ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hv⟩⟩ := by
  simp [extendParents, hv]

/-- A non-root vertex is not a root. -/
theorem nonroot_not_mem (B : Finset V) (v : (univ \ B : Finset V)) :
    (v : V) ∉ B :=
  (Finset.mem_sdiff.mp v.2).2

/-- Every non-root reaches a root after a positive number of steps. -/
def IsPaperParentMap (B : Finset V) (f : ParentAssignment B) : Prop :=
  ∀ v : (univ \ B : Finset V),
    ∃ n : ℕ, (extendParents B f)^[n + 1] (v : V) ∈ B

/-- The least positive time at which the parent chain enters the roots. -/
noncomputable def firstHitTime (B : Finset V)
    (f : ParentAssignment B) (hpm : IsPaperParentMap B f)
    (v : (univ \ B : Finset V)) : ℕ :=
  Nat.find (hpm v) + 1

theorem firstHitTime_pos (B : Finset V)
    (f : ParentAssignment B) (hpm : IsPaperParentMap B f)
    (v : (univ \ B : Finset V)) :
    0 < firstHitTime B f hpm v := by
  simp [firstHitTime]

theorem firstHitTime_mem (B : Finset V)
    (f : ParentAssignment B) (hpm : IsPaperParentMap B f)
    (v : (univ \ B : Finset V)) :
    (extendParents B f)^[firstHitTime B f hpm v] (v : V) ∈ B := by
  exact Nat.find_spec (hpm v)

/-- The chain has not visited any root before its first hitting time. -/
theorem firstHitTime_minimal (B : Finset V)
    (f : ParentAssignment B) (hpm : IsPaperParentMap B f)
    (v : (univ \ B : Finset V)) {t : ℕ}
    (ht : t < firstHitTime B f hpm v) :
    (extendParents B f)^[t] (v : V) ∉ B := by
  cases t with
  | zero =>
      simpa using (Finset.mem_sdiff.mp v.2).2
  | succ n =>
      have hn : n < Nat.find (hpm v) := by
        unfold firstHitTime at ht
        omega
      exact Nat.find_min (hpm v) hn

/-- The last non-root before the first hit is a child of that root. -/
theorem last_nonroot_before_hit (B : Finset V)
    (f : ParentAssignment B) (hpm : IsPaperParentMap B f)
    (v : (univ \ B : Finset V)) :
    ∃ w : (univ \ B : Finset V),
      (extendParents B f)^[firstHitTime B f hpm v - 1] (v : V) = (w : V) ∧
      f w =
        (extendParents B f)^[firstHitTime B f hpm v] (v : V) := by
  let q := firstHitTime B f hpm v
  have hqpos : 0 < q := firstHitTime_pos B f hpm v
  have hpred : q - 1 < q := by omega
  have hwB : (extendParents B f)^[q - 1] (v : V) ∉ B :=
    firstHitTime_minimal B f hpm v hpred
  let w : (univ \ B : Finset V) :=
    ⟨(extendParents B f)^[q - 1] (v : V),
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hwB⟩⟩
  refine ⟨w, rfl, ?_⟩
  have hq : q - 1 + 1 = q := by omega
  change f w = (extendParents B f)^[q] (v : V)
  rw [← hq, Function.iterate_succ_apply']
  exact (extendParents_nonroot B f hwB).symm

/-- The first root reached from a non-root vertex. -/
noncomputable def firstRoot (B : Finset V)
    (f : ParentAssignment B) (hpm : IsPaperParentMap B f)
    (v : (univ \ B : Finset V)) : B :=
  ⟨(extendParents B f)^[firstHitTime B f hpm v] (v : V),
    firstHitTime_mem B f hpm v⟩

/-- The vertices whose first reached root is j. -/
noncomputable def rootBlock (B : Finset V)
    (f : ParentAssignment B) (hpm : IsPaperParentMap B f)
    (j : B) : Finset (univ \ B : Finset V) :=
  univ.filter fun v => firstRoot B f hpm v = j

theorem mem_rootBlock_iff (B : Finset V)
    (f : ParentAssignment B) (hpm : IsPaperParentMap B f)
    (j : B) (v : (univ \ B : Finset V)) :
    v ∈ rootBlock B f hpm j ↔ firstRoot B f hpm v = j := by
  simp [rootBlock]

theorem rootBlock_pairwiseDisjoint (B : Finset V)
    (f : ParentAssignment B) (hpm : IsPaperParentMap B f)
    {i j : B} (hij : i ≠ j) :
    Disjoint (rootBlock B f hpm i) (rootBlock B f hpm j) := by
  apply Finset.disjoint_left.mpr
  intro v hvi hvj
  exact hij ((mem_rootBlock_iff B f hpm i v).mp hvi |>.symm.trans
    ((mem_rootBlock_iff B f hpm j v).mp hvj))

theorem rootBlocks_cover (B : Finset V)
    (f : ParentAssignment B) (hpm : IsPaperParentMap B f) :
    (univ : Finset B).biUnion (rootBlock B f hpm) = univ := by
  ext v
  simp [rootBlock]

/-- Descendants whose path visits w before hitting any root. -/
noncomputable def descendantBlock (B : Finset V)
    (f : ParentAssignment B) (hpm : IsPaperParentMap B f)
    (w : (univ \ B : Finset V)) :
    Finset (univ \ B : Finset V) :=
  univ.filter fun v =>
    ∃ t < firstHitTime B f hpm v,
      (extendParents B f)^[t] (v : V) = (w : V)

theorem self_mem_descendantBlock (B : Finset V)
    (f : ParentAssignment B) (hpm : IsPaperParentMap B f)
    (w : (univ \ B : Finset V)) :
    w ∈ descendantBlock B f hpm w := by
  simp only [descendantBlock, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨0, firstHitTime_pos B f hpm w, by simp⟩

/-- If w has a root as parent, a path visiting w visits it
immediately before its first root. -/
theorem descendant_child_last_step (B : Finset V)
    (f : ParentAssignment B) (hpm : IsPaperParentMap B f)
    {v w : (univ \ B : Finset V)}
    (hw : f w ∈ B) (hv : v ∈ descendantBlock B f hpm w) :
    ∃ t : ℕ, t + 1 = firstHitTime B f hpm v ∧
      (extendParents B f)^[t] (v : V) = (w : V) := by
  obtain ⟨t, ht, htw⟩ := (Finset.mem_filter.mp hv).2
  have hwB : (w : V) ∉ B := (Finset.mem_sdiff.mp w.2).2
  have hnext :
      (extendParents B f)^[t + 1] (v : V) ∈ B := by
    rw [Function.iterate_succ_apply', htw,
      extendParents_nonroot B f hwB]
    exact hw
  have hqle : firstHitTime B f hpm v ≤ t + 1 := by
    by_contra h
    exact (firstHitTime_minimal B f hpm v (by omega)) hnext
  exact ⟨t, by omega, htw⟩

/-- The children of a root, viewed as non-root vertices. -/
noncomputable def children (B : Finset V)
    (f : ParentAssignment B) (i : B) :
    Finset (univ \ B : Finset V) :=
  univ.filter fun w => f w = (i : V)

/-- A vertex has root i exactly when its path visits a child of i. -/
theorem mem_rootBlock_iff_child_descendant (B : Finset V)
    (f : ParentAssignment B) (hpm : IsPaperParentMap B f)
    (v : (univ \ B : Finset V)) (i : B) :
    v ∈ rootBlock B f hpm i ↔
      ∃ w ∈ children B f i, v ∈ descendantBlock B f hpm w := by
  constructor
  · intro hv
    have hroot := (mem_rootBlock_iff B f hpm i v).mp hv
    obtain ⟨w, hlast, hfw⟩ := last_nonroot_before_hit B f hpm v
    have hchild : f w = (i : V) := by
      change f w = (firstRoot B f hpm v : V) at hfw
      exact hfw.trans (congrArg Subtype.val hroot)
    refine ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hchild⟩, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, firstHitTime B f hpm v - 1, ?_, hlast⟩
    have := firstHitTime_pos B f hpm v
    omega
  · rintro ⟨w, hw, hv⟩
    have hchild : f w = (i : V) := (Finset.mem_filter.mp hw).2
    obtain ⟨t, ht, htw⟩ :=
      descendant_child_last_step B f hpm
        (hchild.symm ▸ i.2) hv
    apply (mem_rootBlock_iff B f hpm i v).2
    apply Subtype.ext
    change (extendParents B f)^[firstHitTime B f hpm v] (v : V) = (i : V)
    rw [← ht, Function.iterate_succ_apply', htw]
    exact (extendParents_nonroot B f
      (Finset.mem_sdiff.mp w.2).2).trans hchild

/-- The child descendant sets cover the root block. -/
theorem childDescendants_cover (B : Finset V)
    (f : ParentAssignment B) (hpm : IsPaperParentMap B f)
    (i : B) :
    (children B f i).biUnion (descendantBlock B f hpm) =
      rootBlock B f hpm i := by
  ext v
  rw [Finset.mem_biUnion, mem_rootBlock_iff_child_descendant]

/-- Different children of the same root have disjoint descendants. -/
theorem childDescendants_disjoint (B : Finset V)
    (f : ParentAssignment B) (hpm : IsPaperParentMap B f)
    (i : B) {w w' : (univ \ B : Finset V)}
    (hw : w ∈ children B f i)
    (hw' : w' ∈ children B f i) (hne : w ≠ w') :
    Disjoint (descendantBlock B f hpm w)
      (descendantBlock B f hpm w') := by
  have hchild : f w ∈ B := by
    have h := (Finset.mem_filter.mp hw).2
    exact h.symm ▸ i.2
  have hchild' : f w' ∈ B := by
    have h := (Finset.mem_filter.mp hw').2
    exact h.symm ▸ i.2
  apply Finset.disjoint_left.mpr
  intro v hv hv'
  obtain ⟨t, ht, htv⟩ :=
    descendant_child_last_step B f hpm hchild hv
  obtain ⟨s, hs, hsv⟩ :=
    descendant_child_last_step B f hpm hchild' hv'
  have hts : t = s := by omega
  apply hne
  apply Subtype.ext
  calc
    (w : V) = (extendParents B f)^[t] (v : V) := htv.symm
    _ = (extendParents B f)^[s] (v : V) := by rw [hts]
    _ = (w' : V) := hsv

theorem childDescendants_pairwise (B : Finset V)
    (f : ParentAssignment B) (hpm : IsPaperParentMap B f)
    (i : B) :
    ((children B f i : Finset (univ \ B : Finset V)) : Set _).PairwiseDisjoint
      (descendantBlock B f hpm) := by
  intro w hw w' hw' hne
  exact childDescendants_disjoint B f hpm i
    (Finset.mem_coe.mp hw) (Finset.mem_coe.mp hw') hne

/-- A growth order lists every non-root once, after its parent. -/
def IsGrowthOrder (B : Finset V) (f : ParentAssignment B)
    (τ : List V) : Prop :=
  τ.Nodup ∧ τ.toFinset = univ \ B ∧
    ∀ i : Fin τ.length,
      extendParents B f (τ.get i) ∈ B ∪ (τ.take i).toFinset

/-- The finite set of all compatible growth orders. -/
noncomputable def growthOrders (B : Finset V)
    (f : ParentAssignment B) : Finset (List V) := by
  classical
  exact ((univ \ B).toList.permutations.toFinset).filter (IsGrowthOrder B f)

theorem mem_growthOrders_iff (B : Finset V)
    (f : ParentAssignment B) (τ : List V) :
    τ ∈ growthOrders B f ↔ IsGrowthOrder B f τ := by
  classical
  unfold growthOrders
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨?_, h⟩
    rw [List.mem_toFinset, List.mem_permutations]
    exact List.perm_of_nodup_nodup_toFinset_eq h.1
      (Finset.nodup_toList _) (by rw [h.2.1, Finset.toList_toFinset])

/-- The paper's zero-one root indicator, indexed by non-roots and roots. -/
noncomputable def rootIndicator (B : Finset V)
    (f : ParentAssignment B) (hpm : IsPaperParentMap B f)
    {K : Type*} [Zero K] [One K] :
    Matrix (univ \ B : Finset V) B K :=
  fun v j => if firstRoot B f hpm v = j then 1 else 0

theorem rootIndicator_row_sum (B : Finset V)
    (f : ParentAssignment B) (hpm : IsPaperParentMap B f)
    {K : Type*} [AddCommMonoid K] [One K] :
    ∀ v, ∑ j : B, rootIndicator (K := K) B f hpm v j = 1 := by
  classical
  intro v
  simp [rootIndicator]

end EAB.Paper
