import EAB.Paper.MarkovProperty
import EAB.Paper.FiniteChain

/-!
# Confined excursions and almost-sure hitting

The probability that the chain started at `a` stays in `U` for `n`
steps and is at `b` at time `n` is the entry `(P[U]^n)_{ab}`. Summed
over `n` it is the Green entry `(G_U)_{ab}`. The geometric estimate
of Lemma `lem:confined` makes every state almost surely visited,
which is the first part of Lemma `lem:cover`.
-/

open MeasureTheory ProbabilityTheory Finset Filter Topology

namespace EAB.Paper.Chain

open Foundation

variable {V : Type*} [Fintype V] [DecidableEq V]
  [MeasurableSpace V] [MeasurableSingletonClass V]

/-! ## Entries of the confined matrix, for arbitrary states -/

/-- The entry `(P[U]^n)_{ab}`, and `0` unless `a, b ∈ U`. -/
noncomputable def confinedPow (P : Matrix V V ℝ) (U : Finset V)
    (n : ℕ) (a b : V) : ℝ :=
  if h : a ∈ U ∧ b ∈ U then
    (Foundation.principal P U ^ n) ⟨a, h.1⟩ ⟨b, h.2⟩
  else 0

/-- The Green entry `(G_U)_{ab} = ((I - P[U])⁻¹)_{ab}`, and `0`
unless `a, b ∈ U`. -/
noncomputable def green (P : Matrix V V ℝ) (U : Finset V)
    (a b : V) : ℝ :=
  if h : a ∈ U ∧ b ∈ U then
    (1 - Foundation.principal P U)⁻¹ ⟨a, h.1⟩ ⟨b, h.2⟩
  else 0

omit [MeasurableSpace V] [MeasurableSingletonClass V] in
theorem confinedPow_nonneg {P : Matrix V V ℝ} (hP : IsStochastic P)
    (U : Finset V) (n : ℕ) (a b : V) : 0 ≤ confinedPow P U n a b := by
  unfold confinedPow
  split_ifs with h
  · exact (principal_isSubstochastic hP U).pow_nonneg n _ _
  · exact le_rfl

omit [MeasurableSpace V] [MeasurableSingletonClass V] in
/-- Equation `eq:confined`, the Green series, for arbitrary states. -/
theorem hasSum_confinedPow {P : Matrix V V ℝ} (hP : IsStochastic P)
    (hirr : IsIrreducible P) (U : Finset V) (hU : U ≠ univ)
    (a b : V) :
    HasSum (fun n => confinedPow P U n a b) (green P U a b) := by
  unfold confinedPow green
  split_ifs with h
  · exact confined_hasSum hP hirr U ⟨a, h.1⟩ hU _ _
  · exact hasSum_zero

omit [MeasurableSpace V] [MeasurableSingletonClass V] in
theorem green_nonneg {P : Matrix V V ℝ} (hP : IsStochastic P)
    (hirr : IsIrreducible P) (U : Finset V) (hU : U ≠ univ)
    (a b : V) : 0 ≤ green P U a b :=
  (hasSum_confinedPow hP hirr U hU a b).nonneg
    fun n => confinedPow_nonneg hP U n a b

/-! ## The start and the first step -/

theorem chainLaw_start_eq (P : Matrix V V ℝ) (hP : IsStochastic P)
    (a b : V) :
    chainLaw P hP a {ω | ω 0 = b} = if b = a then 1 else 0 := by
  have hset : {ω : ℕ → V | ω 0 = b} = cylinder (fun _ => b) 0 := by
    apply Set.ext
    intro ω
    simp [cylinder]
  rw [hset, chainLaw_cylinder]
  simp

theorem chainLaw_start (P : Matrix V V ℝ) (hP : IsStochastic P)
    (a : V) : chainLaw P hP a {ω | ω 0 = a} = 1 := by
  rw [chainLaw_start_eq, if_pos rfl]

omit [Fintype V] [DecidableEq V] in
theorem measurableSet_coordinate (t : ℕ) (b : V) :
    MeasurableSet {ω : ℕ → V | ω t = b} := by
  change MeasurableSet ((fun ω : ℕ → V => ω t) ⁻¹' {b})
  exact (measurable_pi_apply t) (measurableSet_singleton b)

omit [Fintype V] [DecidableEq V] in
theorem measurableSet_start (a : V) :
    MeasurableSet {ω : ℕ → V | ω 0 = a} :=
  measurableSet_coordinate 0 a

theorem chainLaw_start_compl (P : Matrix V V ℝ) (hP : IsStochastic P)
    (a : V) : chainLaw P hP a {ω | ω 0 = a}ᶜ = 0 := by
  rw [measure_compl (measurableSet_start a) (measure_ne_top _ _),
    chainLaw_start, measure_univ, tsub_self]

/-- Almost surely the chain starts at its initial state. -/
theorem chainLaw_inter_start (P : Matrix V V ℝ) (hP : IsStochastic P)
    (a : V) (E : Set (ℕ → V)) :
    chainLaw P hP a (E ∩ {ω | ω 0 = a}) = chainLaw P hP a E :=
  measure_inter_conull (chainLaw_start_compl P hP a)

/-- The law of the first step. -/
theorem chainLaw_first_step (P : Matrix V V ℝ) (hP : IsStochastic P)
    (c b : V) :
    chainLaw P hP c {ω | ω 1 = b} = ENNReal.ofReal (P c b) := by
  have hset : {ω : ℕ → V | ω 1 = b} ∩ {ω | ω 0 = c} =
      cylinder (fun t => if t = 0 then c else b) 1 := by
    apply Set.ext
    intro ω
    simp only [cylinder, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h0⟩ t ht
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ht with rfl | rfl
      · simpa using h0
      · simpa using h1
    · intro h
      exact ⟨by simpa using h 1 le_rfl, by simpa using h 0 (by omega)⟩
  rw [← chainLaw_inter_start, hset, chainLaw_cylinder]
  simp

/-! ## Staying in a set -/

/-- The chain stays in `U` up to time `n` and is at `b` at time `n`. -/
def confinedAt (U : Finset V) (n : ℕ) (b : V) : Set (ℕ → V) :=
  {ω | (∀ t ≤ n, ω t ∈ U) ∧ ω n = b}

omit [Fintype V] [DecidableEq V] [MeasurableSpace V]
  [MeasurableSingletonClass V] in
theorem prefixEvent_confinedAt (U : Finset V) (n : ℕ) (b : V) :
    PrefixEvent n (confinedAt U n b) := by
  intro ω ω' h
  simp only [confinedAt, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hU, hb⟩
    exact ⟨fun t ht => h t ht ▸ hU t ht, h n le_rfl ▸ hb⟩
  · rintro ⟨hU, hb⟩
    exact ⟨fun t ht => (h t ht).symm ▸ hU t ht,
      (h n le_rfl).symm ▸ hb⟩

omit [Fintype V] [DecidableEq V] [MeasurableSpace V]
  [MeasurableSingletonClass V] in
theorem confinedAt_last {U : Finset V} {n : ℕ} {b : V} {ω : ℕ → V}
    (h : ω ∈ confinedAt U n b) : ω n = b :=
  h.2

omit [Fintype V] [DecidableEq V] [MeasurableSpace V]
  [MeasurableSingletonClass V] in
/-- Decomposition at the last step. -/
theorem confinedAt_succ (U : Finset V) (n : ℕ) (b : V) (hb : b ∈ U) :
    confinedAt U (n + 1) b =
      ⋃ c ∈ U, (confinedAt U n c ∩ shift n ⁻¹' {ω | ω 1 = b}) := by
  apply Set.ext
  intro ω
  simp only [confinedAt, Set.mem_setOf_eq, Set.mem_iUnion,
    Set.mem_inter_iff, Set.mem_preimage, shift, exists_prop]
  constructor
  · rintro ⟨hU, hlast⟩
    refine ⟨ω n, hU n (Nat.le_succ n),
      ⟨fun t ht => hU t (ht.trans (Nat.le_succ n)), rfl⟩, ?_⟩
    rw [Nat.add_comm 1 n]
    exact hlast
  · rintro ⟨c, -, ⟨hU, -⟩, hlast⟩
    rw [Nat.add_comm 1 n] at hlast
    refine ⟨fun t ht => ?_, hlast⟩
    rcases Nat.lt_or_ge t (n + 1) with hlt | hge
    · exact hU t (by omega)
    · have ht' : t = n + 1 := by omega
      rw [ht', hlast]
      exact hb

/-- The probability of a confined excursion of length `n`. -/
theorem chainLaw_confinedAt (P : Matrix V V ℝ) (hP : IsStochastic P)
    (U : Finset V) (a : V) (n : ℕ) (b : V) :
    chainLaw P hP a (confinedAt U n b) =
      ENNReal.ofReal (confinedPow P U n a b) := by
  classical
  induction n generalizing b with
  | zero =>
      by_cases hb : b ∈ U
      · have hset : confinedAt U 0 b = {ω | ω 0 = b} := by
          apply Set.ext
          intro ω
          simp only [confinedAt, Set.mem_setOf_eq]
          constructor
          · exact fun h => h.2
          · intro h
            refine ⟨fun t ht => ?_, h⟩
            have ht0 : t = 0 := by omega
            rw [ht0, h]
            exact hb
        rw [hset, chainLaw_start_eq]
        unfold confinedPow
        by_cases ha : a ∈ U
        · rw [dif_pos ⟨ha, hb⟩, pow_zero, Matrix.one_apply]
          by_cases hab : b = a
          · subst hab
            simp
          · have hne : (⟨a, ha⟩ : U) ≠ ⟨b, hb⟩ :=
              fun h => hab (congrArg Subtype.val h).symm
            simp [hab, hne]
        · have hab : b ≠ a := fun h => ha (h ▸ hb)
          rw [dif_neg (fun h => ha h.1), if_neg hab]
          simp
      · have hset : confinedAt U 0 b = ∅ := by
          apply Set.eq_empty_of_forall_notMem
          rintro ω ⟨hU, hlast⟩
          exact hb (hlast ▸ hU 0 le_rfl)
        rw [hset, measure_empty]
        unfold confinedPow
        rw [dif_neg (fun h => hb h.2)]
        simp
  | succ n ih =>
      by_cases hb : b ∈ U
      · rw [confinedAt_succ U n b hb, measure_biUnion_finset]
        · have hterm : ∀ c ∈ U,
              chainLaw P hP a
                (confinedAt U n c ∩ shift n ⁻¹' {ω | ω 1 = b}) =
              ENNReal.ofReal (confinedPow P U n a c * P c b) := by
            intro c _
            rw [chainLaw_prefix_inter_shift P hP a c
                (prefixEvent_confinedAt U n c)
                (fun ω hω => confinedAt_last hω)
                (measurableSet_coordinate 1 b),
              ih c, chainLaw_first_step,
              ENNReal.ofReal_mul (confinedPow_nonneg hP U n a c)]
          rw [Finset.sum_congr rfl hterm,
            ← ENNReal.ofReal_sum_of_nonneg (fun c _ =>
              mul_nonneg (confinedPow_nonneg hP U n a c)
                (hP.nonneg c b))]
          congr 1
          unfold confinedPow
          by_cases ha : a ∈ U
          · rw [dif_pos ⟨ha, hb⟩, pow_succ, Matrix.mul_apply,
              ← Finset.sum_coe_sort U]
            apply Finset.sum_congr rfl
            intro c _
            rw [dif_pos ⟨ha, c.2⟩]
            rfl
          · rw [dif_neg (fun h => ha h.1)]
            apply Finset.sum_eq_zero
            intro c _
            rw [dif_neg (fun h => ha h.1), zero_mul]
        · intro c _ c' _ hne
          apply Set.disjoint_left.mpr
          rintro ω ⟨hc, -⟩ ⟨hc', -⟩
          exact hne ((confinedAt_last hc).symm.trans
            (confinedAt_last hc'))
        · intro c _
          exact (prefixEvent_confinedAt U n c).measurableSet.inter
            (measurable_shift n (measurableSet_coordinate 1 b))
      · have hset : confinedAt U (n + 1) b = ∅ := by
          apply Set.eq_empty_of_forall_notMem
          rintro ω ⟨hU, hlast⟩
          exact hb (hlast ▸ hU (n + 1) le_rfl)
        rw [hset, measure_empty]
        unfold confinedPow
        rw [dif_neg (fun h => hb h.2)]
        simp

/-- The chain stays in `U` up to time `n`. -/
def stayIn (U : Finset V) (n : ℕ) : Set (ℕ → V) :=
  {ω | ∀ t ≤ n, ω t ∈ U}

/-- The probability of staying in `U` is a row sum of `P[U]^n`. -/
theorem chainLaw_stayIn (P : Matrix V V ℝ) (hP : IsStochastic P)
    (U : Finset V) (a : U) (n : ℕ) :
    chainLaw P hP a (stayIn U n) =
      ENNReal.ofReal (rowSum (Foundation.principal P U) n a) := by
  classical
  have hset : stayIn U n = ⋃ b ∈ U, confinedAt U n b := by
    apply Set.ext
    intro ω
    simp only [stayIn, confinedAt, Set.mem_setOf_eq, Set.mem_iUnion,
      exists_prop]
    constructor
    · intro h
      exact ⟨ω n, h n le_rfl, h, rfl⟩
    · rintro ⟨b, -, h, -⟩
      exact h
  rw [hset, measure_biUnion_finset]
  · simp only [chainLaw_confinedAt]
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun b _ => confinedPow_nonneg hP U n a b)]
    congr 1
    rw [rowSum, ← Finset.sum_coe_sort U]
    apply Finset.sum_congr rfl
    intro b _
    unfold confinedPow
    rw [dif_pos ⟨a.2, b.2⟩]
  · intro b _ b' _ hne
    apply Set.disjoint_left.mpr
    intro ω hb hb'
    exact hne ((confinedAt_last hb).symm.trans (confinedAt_last hb'))
  · intro b _
    exact (prefixEvent_confinedAt U n b).measurableSet

/-! ## First entrances -/

/-- The state `v` is visited. -/
def Hits (ω : ℕ → V) (v : V) : Prop :=
  ∃ t, ω t = v

/-- The first-entrance time `T_v`. It is `0` if `v` is not visited. -/
noncomputable def hitTime (ω : ℕ → V) (v : V) : ℕ :=
  sInf {t | ω t = v}

omit [Fintype V] [DecidableEq V] [MeasurableSpace V]
  [MeasurableSingletonClass V] in
theorem hitTime_spec {ω : ℕ → V} {v : V} (h : Hits ω v) :
    ω (hitTime ω v) = v :=
  Nat.sInf_mem (s := {t | ω t = v}) h

omit [Fintype V] [DecidableEq V] [MeasurableSpace V]
  [MeasurableSingletonClass V] in
theorem hitTime_le {ω : ℕ → V} {v : V} {t : ℕ} (h : ω t = v) :
    hitTime ω v ≤ t :=
  Nat.sInf_le (s := {t | ω t = v}) h

omit [Fintype V] [DecidableEq V] [MeasurableSpace V]
  [MeasurableSingletonClass V] in
theorem ne_of_lt_hitTime {ω : ℕ → V} {v : V} {t : ℕ}
    (h : t < hitTime ω v) : ω t ≠ v :=
  fun heq => absurd (hitTime_le heq) (not_le.mpr h)

omit [Fintype V] [DecidableEq V] [MeasurableSpace V]
  [MeasurableSingletonClass V] in
theorem hitTime_eq {ω : ℕ → V} {v : V} {n : ℕ} (h : ω n = v)
    (hbefore : ∀ t < n, ω t ≠ v) : hitTime ω v = n := by
  apply le_antisymm (hitTime_le h)
  by_contra hlt
  exact hbefore _ (not_le.mp hlt) (hitTime_spec ⟨n, h⟩)

/-- Lemma `lem:cover`, first part: every state is almost surely
visited. The chance of avoiding `v` for `m (n - 1)` steps decays
geometrically. -/
theorem chainLaw_not_hits (P : Matrix V V ℝ) (hP : IsStochastic P)
    (hirr : IsIrreducible P) (a v : V) :
    chainLaw P hP a {ω | ¬ Hits ω v} = 0 := by
  classical
  by_cases hva : v = a
  · apply measure_mono_null _ (chainLaw_start_compl P hP a)
    intro ω hω hstart
    exact hω ⟨0, hstart.trans hva.symm⟩
  · let U : Finset V := univ.erase v
    have haU : a ∈ U :=
      Finset.mem_erase.mpr ⟨fun h => hva h.symm, Finset.mem_univ a⟩
    have hU : U ≠ univ := by
      intro h
      have hv : v ∈ U := by
        rw [h]
        exact Finset.mem_univ v
      exact Finset.notMem_erase v univ hv
    obtain ⟨c, hc0, hc1, hc⟩ := confined_rowSum_decay hP hirr U hU
    have hbound : ∀ m : ℕ,
        chainLaw P hP a {ω | ¬ Hits ω v} ≤ ENNReal.ofReal (c ^ m) := by
      intro m
      calc
        chainLaw P hP a {ω | ¬ Hits ω v}
            ≤ chainLaw P hP a
                (stayIn U (m * (Fintype.card V - 1))) := by
              apply measure_mono
              intro ω hω t _
              exact Finset.mem_erase.mpr
                ⟨fun h => hω ⟨t, h⟩, Finset.mem_univ _⟩
        _ = ENNReal.ofReal (rowSum (Foundation.principal P U)
              (m * (Fintype.card V - 1)) ⟨a, haU⟩) :=
              chainLaw_stayIn P hP U ⟨a, haU⟩ _
        _ ≤ ENNReal.ofReal (c ^ m) :=
              ENNReal.ofReal_le_ofReal (hc m ⟨a, haU⟩)
    have hlim : Tendsto (fun m : ℕ => ENNReal.ofReal (c ^ m)) atTop
        (𝓝 0) := by
      have h := (ENNReal.continuous_ofReal.tendsto 0).comp
        (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1)
      simpa using h
    exact le_antisymm (ge_of_tendsto' hlim hbound) bot_le

/-- Almost surely every state is visited: the cover time is finite. -/
theorem ae_hits_all (P : Matrix V V ℝ) (hP : IsStochastic P)
    (hirr : IsIrreducible P) (a : V) :
    ∀ᵐ ω ∂(chainLaw P hP a), ∀ v, Hits ω v := by
  rw [ae_all_iff]
  intro v
  exact chainLaw_not_hits P hP hirr a v

end EAB.Paper.Chain
