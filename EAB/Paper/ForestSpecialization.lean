import EAB.Paper.ForestData
import EAB.Paper.TransferFoundation

/-!
# The forest specialization of one-vertex transfer

This file connects partial parent assignments and their root
indicators to the general aggregation and fold calculation.
-/

open Finset Matrix

namespace EAB.Paper

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Restrict a partial parent assignment after making w a new root. -/
noncomputable def peelParents (B : Finset V)
    (f : ParentAssignment B) (w : V) :
    ParentAssignment (insert w B) :=
  fun v => f ⟨v, Finset.mem_sdiff.mpr
    ⟨Finset.mem_univ (v : V), by
      have hv : (v : V) ∉ insert w B := (Finset.mem_sdiff.mp v.2).2
      exact fun h => hv (Finset.mem_insert_of_mem h)⟩⟩

/-- Before the path meets the enlarged root set, the restricted
and original parent maps take the same next step. -/
theorem peelParents_agree_off_roots (B : Finset V)
    (f : ParentAssignment B) (w v : V)
    (hv : v ∉ insert w B) :
    extendParents (insert w B) (peelParents B f w) v =
      extendParents B f v := by
  rw [extendParents_nonroot (insert w B) (peelParents B f w) hv]
  rw [extendParents_nonroot B f
    (fun h => hv (Finset.mem_insert_of_mem h))]
  rfl

/-- Enlarging the root set by a non-root preserves the parent-map
property for the restriction to the remaining vertices. -/
theorem peelParents_isParentMap (B : Finset V)
    (f : ParentAssignment B) (hpm : IsPaperParentMap B f)
    (w : V) :
    IsPaperParentMap (insert w B) (peelParents B f w) := by
  intro v
  let g := extendParents (insert w B) (peelParents B f w)
  let f₀ := extendParents B f
  let v₀ : (univ \ B : Finset V) :=
    ⟨v, Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ (v : V), by
        intro hv
        exact (Finset.mem_sdiff.mp v.2).2
          (Finset.mem_insert_of_mem hv)⟩⟩
  obtain ⟨n, hn⟩ := hpm v₀
  by_contra h
  have hno : ∀ t : ℕ, g^[t + 1] (v : V) ∉ insert w B := by
    intro t ht
    exact h ⟨t, ht⟩
  have havoid : ∀ t : ℕ, g^[t] (v : V) ∉ insert w B := by
    intro t
    cases t with
    | zero => simpa using (Finset.mem_sdiff.mp v.2).2
    | succ t => exact hno t
  have heq : ∀ t : ℕ, g^[t] (v : V) = f₀^[t] (v : V) := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        have hagree :=
          peelParents_agree_off_roots B f w _ (havoid t)
        change g (g^[t] (v : V)) = f₀ (g^[t] (v : V)) at hagree
        rw [hagree, ih]
  have hB : f₀^[n + 1] (v : V) ∈ B := hn
  exact (havoid (n + 1))
    ((heq (n + 1)) ▸ Finset.mem_insert_of_mem hB)

/-- A newly remaining vertex is also an original non-root. -/
def oldNonroot (B : Finset V) (w : V)
    (v : (univ \ insert w B : Finset V)) :
    (univ \ B : Finset V) :=
  ⟨v, Finset.mem_sdiff.mpr
    ⟨Finset.mem_univ (v : V), fun h =>
      (Finset.mem_sdiff.mp v.2).2
        (Finset.mem_insert_of_mem h)⟩⟩

/-- A hit at n with no earlier hit identifies the least first-hit time. -/
private theorem firstHitTime_eq_of_hit (B : Finset V)
    (f : ParentAssignment B) (hpm : IsPaperParentMap B f)
    (v : (univ \ B : Finset V)) (n : ℕ)
    (hhit : (extendParents B f)^[n] (v : V) ∈ B)
    (hbefore : ∀ t < n, (extendParents B f)^[t] (v : V) ∉ B) :
    firstHitTime B f hpm v = n := by
  have hle : firstHitTime B f hpm v ≤ n := by
    by_contra h
    exact (firstHitTime_minimal B f hpm v (by omega)) hhit
  have hge : n ≤ firstHitTime B f hpm v := by
    by_contra h
    exact hbefore _ (by omega) (firstHitTime_mem B f hpm v)
  omega

/-- Iterates of the restricted and original map agree before the
restricted path reaches its enlarged root set. -/
private theorem peel_iterate_agree (B : Finset V)
    (f : ParentAssignment B) (w : V)
    (v : (univ \ insert w B : Finset V)) (n : ℕ)
    (havoid : ∀ t < n,
      (extendParents (insert w B) (peelParents B f w))^[t]
        (v : V) ∉ insert w B) :
    (extendParents (insert w B) (peelParents B f w))^[n]
        (v : V) = (extendParents B f)^[n] (v : V) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have hagree := peelParents_agree_off_roots B f w _
        (havoid n (by omega))
      rw [hagree]
      congr 1
      apply ih
      intro t ht
      exact havoid t (by omega)

/-- If the restricted path first hits the new root `w` at time `q`,
the original path is at `w` at time `q` and first hits the old root
set one step later. -/
theorem peel_hit_new (B : Finset V)
    (f : ParentAssignment B) (hpm : IsPaperParentMap B f)
    (w : V) (hw : w ∉ B)
    (hchild : f ⟨w, Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ w, hw⟩⟩ ∈ B)
    (hpm' : IsPaperParentMap (insert w B) (peelParents B f w))
    (v : (univ \ insert w B : Finset V))
    (hnew : (firstRoot (insert w B) (peelParents B f w) hpm' v : V) = w) :
    (extendParents B f)^[firstHitTime (insert w B)
        (peelParents B f w) hpm' v] (v : V) = w ∧
      firstHitTime B f hpm (oldNonroot B w v) =
        firstHitTime (insert w B) (peelParents B f w) hpm' v + 1 := by
  let q := firstHitTime (insert w B) (peelParents B f w) hpm' v
  let g := extendParents (insert w B) (peelParents B f w)
  let f₀ := extendParents B f
  have hbeforeNew : ∀ t < q, g^[t] (v : V) ∉ insert w B := by
    intro t ht
    exact firstHitTime_minimal (insert w B) (peelParents B f w)
      hpm' v ht
  have heq : ∀ t ≤ q, g^[t] (v : V) = f₀^[t] (v : V) := by
    intro t ht
    apply peel_iterate_agree B f w v t
    intro s hs
    exact hbeforeNew s (by omega)
  have hq : f₀^[q] (v : V) = w := by
    change g^[q] (v : V) = w at hnew
    exact (heq q le_rfl).symm.trans hnew
  have hhit : f₀^[q + 1] (v : V) ∈ B := by
    rw [Function.iterate_succ_apply', hq]
    change extendParents B f w ∈ B
    rw [extendParents_nonroot B f hw]
    exact hchild
  have hbefore : ∀ t < q + 1, f₀^[t] (v : V) ∉ B := by
    intro t ht
    rcases lt_or_eq_of_le (by omega : t ≤ q) with hlt | rfl
    · rw [← heq t (by omega)]
      exact fun h => hbeforeNew t hlt (Finset.mem_insert_of_mem h)
    · rw [hq]
      exact hw
  exact ⟨hq, firstHitTime_eq_of_hit B f hpm (oldNonroot B w v) (q + 1)
    hhit hbefore⟩

/-- If the restricted path first hits the new root w, the
original path immediately continues to w's parent root. -/
theorem peel_firstRoot_at_new (B : Finset V)
    (f : ParentAssignment B) (hpm : IsPaperParentMap B f)
    (w : V) (hw : w ∉ B) (i : B)
    (hchild : f ⟨w, Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ w, hw⟩⟩ = (i : V))
    (hpm' : IsPaperParentMap (insert w B) (peelParents B f w))
    (v : (univ \ insert w B : Finset V))
    (hnew : (firstRoot (insert w B) (peelParents B f w) hpm' v : V) = w) :
    firstRoot B f hpm (oldNonroot B w v) = i := by
  obtain ⟨hq, htime⟩ := peel_hit_new B f hpm w hw
    (hchild.symm ▸ i.2) hpm' v hnew
  apply Subtype.ext
  change (extendParents B f)^[firstHitTime B f hpm (oldNonroot B w v)]
    (v : V) = (i : V)
  rw [htime, Function.iterate_succ_apply', hq]
  rw [extendParents_nonroot B f hw]
  exact hchild

/-- If the restricted path first hits an original root, the
original first-hit root is the same. -/
theorem peel_firstRoot_at_old (B : Finset V)
    (f : ParentAssignment B) (hpm : IsPaperParentMap B f)
    (w : V) (j : B)
    (hpm' : IsPaperParentMap (insert w B) (peelParents B f w))
    (v : (univ \ insert w B : Finset V))
    (hnew : firstRoot (insert w B) (peelParents B f w) hpm' v =
      ⟨j, Finset.mem_insert_of_mem j.2⟩) :
    firstRoot B f hpm (oldNonroot B w v) = j := by
  let v₀ := oldNonroot B w v
  let q := firstHitTime (insert w B) (peelParents B f w) hpm' v
  let g := extendParents (insert w B) (peelParents B f w)
  let f₀ := extendParents B f
  have hbeforeNew : ∀ t < q, g^[t] (v : V) ∉ insert w B := by
    intro t ht
    exact firstHitTime_minimal (insert w B) (peelParents B f w)
      hpm' v ht
  have heq : ∀ t ≤ q, g^[t] (v : V) = f₀^[t] (v : V) := by
    intro t ht
    apply peel_iterate_agree B f w v t
    intro s hs
    exact hbeforeNew s (by omega)
  have hq : f₀^[q] (v : V) = (j : V) := by
    have hnew' : g^[q] (v : V) = (j : V) :=
      congrArg Subtype.val hnew
    exact (heq q le_rfl).symm.trans hnew'
  have hhit : f₀^[q] (v : V) ∈ B := hq.symm ▸ j.2
  have hbefore : ∀ t < q, f₀^[t] (v : V) ∉ B := by
    intro t ht
    rw [← heq t (by omega)]
    exact fun h => hbeforeNew t ht (Finset.mem_insert_of_mem h)
  have htime := firstHitTime_eq_of_hit B f hpm v₀ q
    hhit hbefore
  apply Subtype.ext
  change f₀^[firstHitTime B f hpm v₀] (v : V) = (j : V)
  rw [htime]
  exact hq

/-- A child of i reaches i on its first parent step. -/
theorem firstRoot_child (B : Finset V)
    (f : ParentAssignment B) (hpm : IsPaperParentMap B f)
    (w : V) (hw : w ∉ B) (i : B)
    (hchild : f ⟨w, Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ w, hw⟩⟩ = (i : V)) :
    firstRoot B f hpm
      ⟨w, Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hw⟩⟩ = i := by
  let wB : (univ \ B : Finset V) :=
    ⟨w, Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hw⟩⟩
  have hhit : (extendParents B f)^[1] (w : V) ∈ B := by
    change extendParents B f w ∈ B
    rw [extendParents_nonroot B f hw]
    exact hchild.symm ▸ i.2
  have hbefore : ∀ t < 1,
      (extendParents B f)^[t] (w : V) ∉ B := by
    intro t ht
    have : t = 0 := by omega
    subst t
    simpa using hw
  have htime := firstHitTime_eq_of_hit B f hpm wB 1
    hhit hbefore
  apply Subtype.ext
  change (extendParents B f)^[firstHitTime B f hpm wB] w = (i : V)
  rw [htime]
  change extendParents B f w = (i : V)
  rw [extendParents_nonroot B f hw]
  exact hchild

theorem rootIndicator_unitRowSums (B : Finset V)
    (f : ParentAssignment B) (hpm : IsPaperParentMap B f)
    {K : Type*} [Field K] :
    Foundation.UnitRowSums B
      (rootIndicator (K := K) B f hpm) :=
  rootIndicator_row_sum B f hpm

/-- The remaining vertices whose restricted path first meets the new
root `w` are the descendants of `w` other than `w` itself. -/
theorem peel_firstRoot_eq_new_iff (B : Finset V)
    (f : ParentAssignment B) (hpm : IsPaperParentMap B f)
    (w : V) (hw : w ∉ B)
    (hchild : f ⟨w, Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ w, hw⟩⟩ ∈ B)
    (hpm' : IsPaperParentMap (insert w B) (peelParents B f w))
    (v : (univ \ insert w B : Finset V)) :
    (firstRoot (insert w B) (peelParents B f w) hpm' v : V) = w ↔
      oldNonroot B w v ∈ descendantBlock B f hpm
        ⟨w, Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hw⟩⟩ := by
  let g := extendParents (insert w B) (peelParents B f w)
  let f₀ := extendParents B f
  constructor
  · intro hnew
    obtain ⟨hq, htime⟩ := peel_hit_new B f hpm w hw hchild hpm' v hnew
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, _, by rw [htime]; omega, hq⟩
  · intro hv
    obtain ⟨t, ht, htw⟩ :=
      descendant_child_last_step B f hpm hchild hv
    have htw' : f₀^[t] (v : V) = w := htw
    have havoid : ∀ s, s ≤ t → ∀ s' < s, g^[s'] (v : V) ∉ insert w B := by
      intro s
      induction s with
      | zero => intro _ s' hs'; omega
      | succ s ih =>
          intro hs s' hs'
          rcases Nat.lt_succ_iff_lt_or_eq.mp hs' with hlt | rfl
          · exact ih (by omega) s' hlt
          · have hagree : g^[s'] (v : V) = f₀^[s'] (v : V) :=
              peel_iterate_agree B f w v s' (ih (by omega))
            rw [hagree]
            have hnotB : f₀^[s'] (v : V) ∉ B :=
              firstHitTime_minimal B f hpm (oldNonroot B w v)
                (by omega)
            have hnext : f₀^[s' + 1] (v : V) ∉ B :=
              firstHitTime_minimal B f hpm (oldNonroot B w v)
                (by omega)
            intro hmem
            rcases Finset.mem_insert.mp hmem with hw' | hB
            · apply hnext
              rw [Function.iterate_succ_apply', hw']
              change extendParents B f w ∈ B
              rw [extendParents_nonroot B f hw]
              exact hchild
            · exact hnotB hB
    have hgt : g^[t] (v : V) = w :=
      (peel_iterate_agree B f w v t (havoid t le_rfl)).trans htw'
    have hhit : g^[t] (v : V) ∈ insert w B := by
      rw [hgt]
      exact Finset.mem_insert_self w B
    have htime := firstHitTime_eq_of_hit (insert w B)
      (peelParents B f w) hpm' v t hhit (havoid t le_rfl)
    change g^[firstHitTime (insert w B) (peelParents B f w) hpm' v]
      (v : V) = w
    rw [htime]
    exact hgt

variable {K : Type*} [Field K]

/-- The indicator vector `𝟏_{D_w}` of a descendant block. -/
noncomputable def descendantIndicator (B : Finset V)
    (f : ParentAssignment B) (hpm : IsPaperParentMap B f)
    (w : (univ \ B : Finset V)) : (univ \ B : Finset V) → K :=
  fun v => if v ∈ descendantBlock B f hpm w then 1 else 0

/-- Lemma `lem:blocks` in indicator form: the descendant blocks of
the children of a root `i` partition its root block, so their
indicators sum to the column `i` of the root indicator. -/
theorem sum_descendantIndicator (B : Finset V)
    (f : ParentAssignment B) (hpm : IsPaperParentMap B f) (i : B) :
    ∑ w ∈ children B f i, descendantIndicator (K := K) B f hpm w =
      fun v => rootIndicator (K := K) B f hpm v i := by
  classical
  funext v
  rw [Finset.sum_apply]
  simp only [descendantIndicator, rootIndicator]
  by_cases hv : firstRoot B f hpm v = i
  · rw [if_pos hv]
    obtain ⟨w₀, hw₀, hvw₀⟩ :=
      (mem_rootBlock_iff_child_descendant B f hpm v i).mp
        ((mem_rootBlock_iff B f hpm i v).mpr hv)
    rw [Finset.sum_eq_single_of_mem w₀ hw₀, if_pos hvw₀]
    intro w hw hne
    rw [if_neg]
    intro hvw
    exact Finset.disjoint_left.mp
      (childDescendants_disjoint B f hpm i hw hw₀ hne) hvw hvw₀
  · rw [if_neg hv]
    apply Finset.sum_eq_zero
    intro w hw
    rw [if_neg]
    intro hvw
    exact hv ((mem_rootBlock_iff B f hpm i v).mp
      ((mem_rootBlock_iff_child_descendant B f hpm v i).mpr
        ⟨w, hw, hvw⟩))

/-- Lemma `lem:forest-fold`, first identity: the root indicator is
the fold of the peeled root indicator along the coordinate vector at
the root `i` whose child `w` was moved into the root set. -/
theorem rootIndicator_eq_fold (B : Finset V)
    (f : ParentAssignment B) (hpm : IsPaperParentMap B f)
    (w : V) (hw : w ∉ B) (i : B)
    (hchild : f ⟨w, Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ w, hw⟩⟩ = (i : V))
    (hpm' : IsPaperParentMap (insert w B) (peelParents B f w)) :
    rootIndicator (K := K) B f hpm =
      Foundation.fold B w hw
        (rootIndicator (K := K) (insert w B) (peelParents B f w) hpm')
        (Pi.single i 1) := by
  classical
  funext v j
  by_cases hvw : (v : V) = w
  · have hv : v = ⟨w, Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ w, hw⟩⟩ := Subtype.ext hvw
    subst hv
    rw [Foundation.fold_at_new_vertex]
    simp only [rootIndicator, firstRoot_child B f hpm w hw i hchild,
      Pi.single_apply]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  · have hvB' : (v : V) ∉ insert w B := by
      simp [Finset.mem_insert, hvw, nonroot_not_mem B v]
    let v' : (univ \ insert w B : Finset V) :=
      ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ (v : V), hvB'⟩⟩
    have hfold := Foundation.fold_at_old_boundary B w hw
      (rootIndicator (K := K) (insert w B) (peelParents B f w) hpm')
      (Pi.single i 1) (v : V) hvB' j
    have hjw : (j : V) ≠ w := fun h => hw (h ▸ j.2)
    refine Eq.trans ?_ hfold.symm
    by_cases hnew :
        (firstRoot (insert w B) (peelParents B f w) hpm' v' : V) = w
    · have hroot : firstRoot B f hpm v = i :=
        peel_firstRoot_at_new B f hpm w hw i hchild hpm' v' hnew
      have hne : firstRoot (insert w B) (peelParents B f w) hpm' v' ≠
          ⟨j, Finset.mem_insert_of_mem j.2⟩ := by
        intro h
        exact hjw ((congrArg Subtype.val h).symm.trans hnew)
      have heq : firstRoot (insert w B) (peelParents B f w) hpm' v' =
          ⟨w, Finset.mem_insert_self w B⟩ := Subtype.ext hnew
      simp only [rootIndicator, hroot, Pi.single_apply]
      rw [if_neg hne, if_pos heq]
      by_cases hij : i = j
      · simp [hij]
      · simp [hij, Ne.symm hij]
    · have hmemB :
          (firstRoot (insert w B) (peelParents B f w) hpm' v' : V) ∈ B :=
        (Finset.mem_insert.mp
          (firstRoot (insert w B) (peelParents B f w) hpm' v').2).resolve_left
          hnew
      have hroot : firstRoot B f hpm v = ⟨_, hmemB⟩ :=
        peel_firstRoot_at_old B f hpm w ⟨_, hmemB⟩ hpm' v' (Subtype.ext rfl)
      have hne : firstRoot (insert w B) (peelParents B f w) hpm' v' ≠
          ⟨w, Finset.mem_insert_self w B⟩ :=
        fun h => hnew (congrArg Subtype.val h)
      simp only [rootIndicator, hroot]
      rw [if_neg hne, zero_mul, add_zero]
      by_cases hj : (firstRoot (insert w B) (peelParents B f w)
          hpm' v' : V) = (j : V)
      · rw [if_pos (Subtype.ext hj), if_pos (Subtype.ext hj)]
      · rw [if_neg (fun h => hj (congrArg Subtype.val h)),
          if_neg (fun h => hj (congrArg Subtype.val h))]

/-- Lemma `lem:forest-fold`, second identity: the boundary vector
`s̃ + e_w` of the transfer lemma is the indicator of the descendant
block of `w`. -/
theorem transferBoundary_rootIndicator (B : Finset V)
    (f : ParentAssignment B) (hpm : IsPaperParentMap B f)
    (w : V) (hw : w ∉ B)
    (hchild : f ⟨w, Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ w, hw⟩⟩ ∈ B)
    (hpm' : IsPaperParentMap (insert w B) (peelParents B f w)) :
    Foundation.transferBoundary B w hw
        (rootIndicator (K := K) (insert w B) (peelParents B f w) hpm') =
      descendantIndicator B f hpm
        ⟨w, Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hw⟩⟩ := by
  classical
  funext v
  unfold descendantIndicator
  by_cases hvw : (v : V) = w
  · have hv : v = ⟨w, Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ w, hw⟩⟩ := Subtype.ext hvw
    subst hv
    rw [if_pos (self_mem_descendantBlock B f hpm _)]
    simp [Foundation.transferBoundary, Foundation.extendZero]
  · have hvB' : (v : V) ∉ insert w B := by
      simp [Finset.mem_insert, hvw, nonroot_not_mem B v]
    let v' : (univ \ insert w B : Finset V) :=
      ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ (v : V), hvB'⟩⟩
    have hne : v ≠ (⟨w, Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ w, hw⟩⟩ : (univ \ B : Finset V)) :=
      fun h => hvw (congrArg Subtype.val h)
    have hzero := Foundation.extendZero_at_old_boundary B w
      (fun u => rootIndicator (K := K) (insert w B)
        (peelParents B f w) hpm' u ⟨w, Finset.mem_insert_self w B⟩)
      (v : V) hvB'
    have hiff :
        (firstRoot (insert w B) (peelParents B f w) hpm' v' : V) = w ↔
          v ∈ descendantBlock B f hpm
            ⟨w, Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hw⟩⟩ :=
      peel_firstRoot_eq_new_iff B f hpm w hw hchild hpm' v'
    have hval : Foundation.transferBoundary B w hw
        (rootIndicator (K := K) (insert w B) (peelParents B f w) hpm') v =
        rootIndicator (K := K) (insert w B) (peelParents B f w) hpm' v'
          ⟨w, Finset.mem_insert_self w B⟩ := by
      simp only [Foundation.transferBoundary, Pi.add_apply,
        Pi.single_apply, if_neg hne, add_zero]
      exact hzero
    rw [hval]
    simp only [rootIndicator]
    by_cases hnew :
        (firstRoot (insert w B) (peelParents B f w) hpm' v' : V) = w
    · rw [if_pos (Subtype.ext hnew), if_pos (hiff.mp hnew)]
    · rw [if_neg (fun h => hnew (congrArg Subtype.val h)),
        if_neg (fun h => hnew (hiff.mpr h))]

end EAB.Paper
