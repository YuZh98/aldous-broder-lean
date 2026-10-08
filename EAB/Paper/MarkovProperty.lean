import Mathlib.MeasureTheory.Constructions.Cylinders
import EAB.Paper.ChainLaw

/-!
# The Markov property at a fixed time

An event that depends on the trajectory up to time `m` only, and on
which the state at time `m` is `c`, is independent of the future
after time `m`, whose law is that of the chain started at `c`. The
proof uses the finite-cylinder formula: the two sides agree when
both events are cylinders, then when the future event depends on
finitely many coordinates, and then for every measurable future
event because such events generate the product σ-algebra.
-/

open MeasureTheory ProbabilityTheory Finset

namespace EAB.Paper.Chain

variable {V : Type*} [Fintype V] [DecidableEq V]
  [MeasurableSpace V] [MeasurableSingletonClass V]

/-! ## Shifts and splices -/

/-- The trajectory after time `m`. -/
def shift (m : ℕ) (ω : ℕ → V) : ℕ → V :=
  fun t => ω (t + m)

omit [Fintype V] [DecidableEq V] [MeasurableSingletonClass V] in
theorem measurable_shift (m : ℕ) : Measurable (shift (V := V) m) :=
  measurable_pi_lambda _ fun t => measurable_pi_apply (t + m)

omit [Fintype V] [DecidableEq V] [MeasurableSpace V]
  [MeasurableSingletonClass V] in
theorem shift_shift (m n : ℕ) (ω : ℕ → V) :
    shift n (shift m ω) = shift (n + m) ω := by
  funext t
  simp [shift, Nat.add_assoc]

/-- Follow `y` up to time `m`, then `x`. -/
def splice (y : ℕ → V) (m : ℕ) (x : ℕ → V) : ℕ → V :=
  fun t => if t ≤ m then y t else x (t - m)

omit [Fintype V] [DecidableEq V] [MeasurableSpace V]
  [MeasurableSingletonClass V] in
theorem cylinder_inter_shift (y x : ℕ → V) (m n : ℕ)
    (h : x 0 = y m) :
    cylinder y m ∩ shift m ⁻¹' cylinder x n =
      cylinder (splice y m x) (m + n) := by
  apply Set.ext
  intro ω
  simp only [cylinder, Set.mem_inter_iff, Set.mem_setOf_eq,
    Set.mem_preimage, shift, splice]
  constructor
  · rintro ⟨hy, hx⟩ t ht
    by_cases htm : t ≤ m
    · rw [if_pos htm]
      exact hy t htm
    · rw [if_neg htm]
      have h' := hx (t - m) (by omega)
      rwa [Nat.sub_add_cancel (by omega)] at h'
  · intro hω
    constructor
    · intro t ht
      have h' := hω t (by omega)
      rwa [if_pos ht] at h'
    · intro s hs
      have h' := hω (s + m) (by omega)
      by_cases hs0 : s = 0
      · subst hs0
        rw [if_pos (by omega)] at h'
        simpa [h] using h'
      · rw [if_neg (by omega), Nat.add_sub_cancel] at h'
        exact h'

omit [Fintype V] [DecidableEq V] [MeasurableSpace V]
  [MeasurableSingletonClass V] in
theorem cylinder_inter_shift_of_ne (y x : ℕ → V) (m n : ℕ)
    (h : x 0 ≠ y m) :
    cylinder y m ∩ shift m ⁻¹' cylinder x n = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  rintro ω ⟨hy, hx⟩
  apply h
  have h1 : ω m = y m := hy m le_rfl
  have h2 : ω (0 + m) = x 0 := hx 0 (Nat.zero_le n)
  rw [Nat.zero_add] at h2
  exact h2.symm.trans h1

omit [Fintype V] [DecidableEq V] [MeasurableSpace V]
  [MeasurableSingletonClass V] in
theorem prod_splice (P : Matrix V V ℝ) (y x : ℕ → V) (m n : ℕ)
    (h : x 0 = y m) :
    ∏ t ∈ Finset.range (m + n),
        ENNReal.ofReal (P (splice y m x t) (splice y m x (t + 1))) =
      (∏ t ∈ Finset.range m, ENNReal.ofReal (P (y t) (y (t + 1)))) *
        ∏ t ∈ Finset.range n, ENNReal.ofReal (P (x t) (x (t + 1))) := by
  rw [Finset.prod_range_add]
  congr 1
  · apply Finset.prod_congr rfl
    intro t ht
    have htm : t < m := Finset.mem_range.mp ht
    simp only [splice]
    rw [if_pos (by omega), if_pos (by omega)]
  · apply Finset.prod_congr rfl
    intro s _
    simp only [splice]
    rw [if_neg (by omega : ¬ m + s + 1 ≤ m)]
    have hsucc : m + s + 1 - m = s + 1 := by omega
    rw [hsucc]
    by_cases hs0 : s = 0
    · subst hs0
      rw [if_pos (by omega), Nat.add_zero, h]
    · rw [if_neg (by omega), Nat.add_sub_cancel_left]

/-! ## Two cylinders -/

theorem chainLaw_cylinder_inter_shift_cylinder (P : Matrix V V ℝ)
    (hP : IsStochastic P) (a : V) (y x : ℕ → V) (m n : ℕ) :
    chainLaw P hP a (cylinder y m ∩ shift m ⁻¹' cylinder x n) =
      chainLaw P hP a (cylinder y m) *
        chainLaw P hP (y m) (cylinder x n) := by
  by_cases h : x 0 = y m
  · rw [cylinder_inter_shift y x m n h, chainLaw_cylinder,
      chainLaw_cylinder, chainLaw_cylinder, prod_splice P y x m n h,
      if_pos h]
    have h0 : splice y m x 0 = y 0 := by simp [splice]
    rw [h0]
    ring
  · rw [cylinder_inter_shift_of_ne y x m n h, measure_empty,
      chainLaw_cylinder P hP (y m), if_neg h]
    simp

/-! ## Events that depend on finitely many coordinates -/

/-- The event `E` depends on the trajectory up to time `n` only. -/
def PrefixEvent (n : ℕ) (E : Set (ℕ → V)) : Prop :=
  ∀ ω ω' : ℕ → V, (∀ t ≤ n, ω t = ω' t) → (ω ∈ E ↔ ω' ∈ E)

/-- Extend a trajectory of length `n` by freezing its last state. -/
def freeze (n : ℕ) (x : Fin (n + 1) → V) : ℕ → V :=
  fun t => x ⟨min t n, by omega⟩

omit [Fintype V] [DecidableEq V] [MeasurableSpace V]
  [MeasurableSingletonClass V] in
theorem freeze_apply_of_le (n : ℕ) (x : Fin (n + 1) → V) {t : ℕ}
    (ht : t ≤ n) : freeze n x t = x ⟨t, by omega⟩ := by
  simp only [freeze]
  congr 1
  exact Fin.ext (Nat.min_eq_left ht)

omit [Fintype V] [DecidableEq V] [MeasurableSpace V]
  [MeasurableSingletonClass V] in
theorem cylinder_disjoint_of_ne (n : ℕ) {x x' : Fin (n + 1) → V}
    (h : x ≠ x') :
    Disjoint (cylinder (freeze n x) n) (cylinder (freeze n x') n) := by
  apply Set.disjoint_left.mpr
  intro ω hω hω'
  apply h
  funext i
  have hi : (i : ℕ) ≤ n := by omega
  have h1 := hω i hi
  have h2 := hω' i hi
  rw [freeze_apply_of_le n x hi] at h1
  rw [freeze_apply_of_le n x' hi] at h2
  exact h1.symm.trans h2

open scoped Classical in
omit [DecidableEq V] [MeasurableSpace V]
  [MeasurableSingletonClass V] in
/-- A prefix event is the finite disjoint union of the cylinders it
contains. -/
theorem PrefixEvent.eq_biUnion {n : ℕ} {E : Set (ℕ → V)}
    (hE : PrefixEvent n E) :
    E = ⋃ x ∈ (Finset.univ.filter
        (fun x : Fin (n + 1) → V => freeze n x ∈ E) : Finset _),
      cylinder (freeze n x) n := by
  apply Set.ext
  intro ω
  simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ,
    true_and, exists_prop]
  constructor
  · intro hω
    refine ⟨fun i => ω i, ?_, ?_⟩
    · apply (hE ω _ ?_).mp hω
      intro t ht
      rw [freeze_apply_of_le n _ ht]
    · intro t ht
      rw [freeze_apply_of_le n _ ht]
  · rintro ⟨x, hx, hω⟩
    exact (hE ω _ hω).mpr hx

omit [DecidableEq V] in
theorem PrefixEvent.measurableSet {n : ℕ} {E : Set (ℕ → V)}
    (hE : PrefixEvent n E) : MeasurableSet E := by
  classical
  rw [hE.eq_biUnion]
  exact Finset.measurableSet_biUnion _
    (fun x _ => measurableSet_cylinder _ n)

open scoped Classical in
omit [DecidableEq V] in
/-- The measure of a prefix event, intersected with a measurable
set, is the finite sum over the cylinders it contains. -/
theorem PrefixEvent.measure_inter {n : ℕ} {E : Set (ℕ → V)}
    (hE : PrefixEvent n E) (μ : Measure (ℕ → V)) {F : Set (ℕ → V)}
    (hF : MeasurableSet F) :
    μ (E ∩ F) = ∑ x : Fin (n + 1) → V,
      if freeze n x ∈ E then μ (cylinder (freeze n x) n ∩ F)
        else 0 := by
  have hunion : E ∩ F = ⋃ x ∈ (Finset.univ.filter
      (fun x : Fin (n + 1) → V => freeze n x ∈ E) : Finset _),
      (cylinder (freeze n x) n ∩ F) := by
    conv_lhs => rw [hE.eq_biUnion]
    rw [Set.iUnion₂_inter]
  rw [hunion, measure_biUnion_finset]
  · rw [Finset.sum_filter]
  · intro x _ x' _ hne
    exact (cylinder_disjoint_of_ne n hne).mono
      Set.inter_subset_left Set.inter_subset_left
  · intro x _
    exact (measurableSet_cylinder _ n).inter hF

omit [Fintype V] [DecidableEq V] [MeasurableSpace V]
  [MeasurableSingletonClass V] in
theorem prefixEvent_cylinder (x : ℕ → V) (n : ℕ) :
    PrefixEvent n (cylinder x n) := by
  intro ω ω' h
  simp only [cylinder, Set.mem_setOf_eq]
  constructor
  · intro hω t ht
    rw [← h t ht]
    exact hω t ht
  · intro hω t ht
    rw [h t ht]
    exact hω t ht

omit [Fintype V] [DecidableEq V] [MeasurableSpace V]
  [MeasurableSingletonClass V] in
theorem PrefixEvent.mono {n n' : ℕ} {E : Set (ℕ → V)}
    (hE : PrefixEvent n E) (hn : n ≤ n') : PrefixEvent n' E :=
  fun ω ω' h => hE ω ω' fun t ht => h t (ht.trans hn)

/-! ## The Markov property -/

/-- A cylinder against a future prefix event. -/
theorem chainLaw_cylinder_inter_shift_prefix (P : Matrix V V ℝ)
    (hP : IsStochastic P) (a : V) (y : ℕ → V) (m : ℕ) {n : ℕ}
    {E : Set (ℕ → V)} (hE : PrefixEvent n E) :
    chainLaw P hP a (cylinder y m ∩ shift m ⁻¹' E) =
      chainLaw P hP a (cylinder y m) * chainLaw P hP (y m) E := by
  classical
  have hleft : chainLaw P hP a (cylinder y m ∩ shift m ⁻¹' E) =
      ∑ x : Fin (n + 1) → V, if freeze n x ∈ E then
        chainLaw P hP a
          (cylinder y m ∩ shift m ⁻¹' cylinder (freeze n x) n)
        else 0 := by
    have hpre : shift m ⁻¹' E = ⋃ x ∈ (Finset.univ.filter
        (fun x : Fin (n + 1) → V => freeze n x ∈ E) : Finset _),
        shift m ⁻¹' cylinder (freeze n x) n := by
      conv_lhs => rw [hE.eq_biUnion]
      simp only [Set.preimage_iUnion]
    rw [hpre, Set.inter_iUnion₂, measure_biUnion_finset]
    · rw [Finset.sum_filter]
    · intro x _ x' _ hne
      exact ((cylinder_disjoint_of_ne n hne).preimage (shift m)).mono
        Set.inter_subset_right Set.inter_subset_right
    · intro x _
      exact (measurableSet_cylinder y m).inter
        (measurable_shift m (measurableSet_cylinder _ n))
  have hright : chainLaw P hP (y m) E =
      ∑ x : Fin (n + 1) → V, if freeze n x ∈ E then
        chainLaw P hP (y m) (cylinder (freeze n x) n) else 0 := by
    have h := hE.measure_inter (chainLaw P hP (y m))
      MeasurableSet.univ
    simpa using h
  rw [hleft, hright, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : freeze n x ∈ E
  · rw [if_pos hx, if_pos hx,
      chainLaw_cylinder_inter_shift_cylinder]
  · rw [if_neg hx, if_neg hx, mul_zero]

omit [Fintype V] [DecidableEq V] [MeasurableSingletonClass V] in
/-- A measurable cylinder of the product space is a prefix event. -/
theorem prefixEvent_of_mem_measurableCylinders {E : Set (ℕ → V)}
    (hE : E ∈ measurableCylinders (fun _ : ℕ => V)) :
    ∃ n, PrefixEvent n E := by
  obtain ⟨I, S, -, rfl⟩ := (mem_measurableCylinders E).mp hE
  refine ⟨I.sup id, ?_⟩
  intro ω ω' h
  have heq : I.restrict ω = I.restrict ω' := by
    funext i
    exact h i (Finset.le_sup (f := id) i.2)
  simp only [MeasureTheory.mem_cylinder, heq]

/-- The Markov property for a cylinder and a measurable future
event. -/
theorem chainLaw_cylinder_inter_shift (P : Matrix V V ℝ)
    (hP : IsStochastic P) (a : V) (y : ℕ → V) (m : ℕ)
    {E : Set (ℕ → V)} (hE : MeasurableSet E) :
    chainLaw P hP a (cylinder y m ∩ shift m ⁻¹' E) =
      chainLaw P hP a (cylinder y m) * chainLaw P hP (y m) E := by
  let ν₁ : Measure (ℕ → V) :=
    ((chainLaw P hP a).restrict (cylinder y m)).map (shift m)
  let ν₂ : Measure (ℕ → V) :=
    chainLaw P hP a (cylinder y m) • chainLaw P hP (y m)
  have h₁ : ∀ F, MeasurableSet F →
      ν₁ F = chainLaw P hP a (cylinder y m ∩ shift m ⁻¹' F) := by
    intro F hF
    simp only [ν₁]
    rw [Measure.map_apply (measurable_shift m) hF,
      Measure.restrict_apply (measurable_shift m hF), Set.inter_comm]
  have h₂ : ∀ F, ν₂ F =
      chainLaw P hP a (cylinder y m) * chainLaw P hP (y m) F := by
    intro F
    simp [ν₂]
  haveI : IsFiniteMeasure ν₁ := by
    simp only [ν₁]
    infer_instance
  have heq : ν₁ = ν₂ := by
    apply ext_of_generate_finite (measurableCylinders (fun _ : ℕ => V))
      generateFrom_measurableCylinders.symm
      isPiSystem_measurableCylinders
    · intro F hF
      obtain ⟨n, hn⟩ := prefixEvent_of_mem_measurableCylinders hF
      rw [h₁ F hn.measurableSet, h₂,
        chainLaw_cylinder_inter_shift_prefix P hP a y m hn]
    · rw [h₁ Set.univ MeasurableSet.univ, h₂]
      simp
  rw [← h₁ E hE, heq, h₂]

/-- **The Markov property.** If the event `G` depends on the
trajectory up to time `m` only and the state at time `m` is `c` on
`G`, then `G` and the future after time `m` are independent, and the
future has the law of the chain started at `c`. -/
theorem chainLaw_prefix_inter_shift (P : Matrix V V ℝ)
    (hP : IsStochastic P) (a c : V) {m : ℕ} {G : Set (ℕ → V)}
    (hG : PrefixEvent m G) (hc : ∀ ω ∈ G, ω m = c)
    {E : Set (ℕ → V)} (hE : MeasurableSet E) :
    chainLaw P hP a (G ∩ shift m ⁻¹' E) =
      chainLaw P hP a G * chainLaw P hP c E := by
  classical
  have hleft := hG.measure_inter (chainLaw P hP a)
    (measurable_shift m hE)
  have hright := hG.measure_inter (chainLaw P hP a)
    MeasurableSet.univ
  simp only [Set.inter_univ] at hright
  rw [hleft, hright, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : freeze m x ∈ G
  · rw [if_pos hx, if_pos hx,
      chainLaw_cylinder_inter_shift P hP a _ m hE, hc _ hx]
  · rw [if_neg hx, if_neg hx, zero_mul]

end EAB.Paper.Chain
