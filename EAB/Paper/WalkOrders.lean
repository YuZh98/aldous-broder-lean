import EAB.Paper.Excursions

/-!
# Discovery orders and the confined-excursion formula

Lemma `lem:excursion` of the blueprint. The chain starts at `a` in a
set `U` of states regarded as already present. It discovers the
states outside `U` in some order `τ`, entering each from a state
visited before. Before the first entrance into `τ_1` the walk makes
an excursion inside `U` that ends at the parent of `τ_1`, then takes
the edge into `τ_1`. After that entrance the future is the chain
started at `τ_1` with `U ∪ {τ_1}` present. The Markov property makes
the weights multiply, and summing over the length of the excursion
gives a Green entry.
-/

open MeasureTheory ProbabilityTheory Finset

namespace EAB.Paper.Chain

variable {V : Type*} [Fintype V] [DecidableEq V]
  [MeasurableSpace V] [MeasurableSingletonClass V]

/-! ## First-entrance times of a shifted trajectory -/

omit [Fintype V] [DecidableEq V] [MeasurableSpace V]
  [MeasurableSingletonClass V] in
theorem hitTime_shift_of_le {ω : ℕ → V} {v : V} {N : ℕ}
    (h : Hits ω v) (hN : N ≤ hitTime ω v) :
    Hits (shift N ω) v ∧
      hitTime (shift N ω) v = hitTime ω v - N := by
  have hval : shift N ω (hitTime ω v - N) = v := by
    simp only [shift]
    rw [Nat.sub_add_cancel hN]
    exact hitTime_spec h
  refine ⟨⟨_, hval⟩, hitTime_eq hval ?_⟩
  intro t ht
  simp only [shift]
  exact ne_of_lt_hitTime (by omega)

omit [Fintype V] [DecidableEq V] [MeasurableSpace V]
  [MeasurableSingletonClass V] in
theorem hitTime_of_shift {ω : ℕ → V} {v : V} {N : ℕ}
    (h : Hits (shift N ω) v) (hbefore : ∀ t < N, ω t ≠ v) :
    Hits ω v ∧ hitTime ω v = hitTime (shift N ω) v + N := by
  have hval : ω (hitTime (shift N ω) v + N) = v := hitTime_spec h
  refine ⟨⟨_, hval⟩, hitTime_eq hval ?_⟩
  intro t ht
  by_cases htN : t < N
  · exact hbefore t htN
  · have hlt : t - N < hitTime (shift N ω) v := by omega
    have hne := ne_of_lt_hitTime hlt
    simp only [shift] at hne
    rwa [Nat.sub_add_cancel (by omega)] at hne

/-! ## Discovery orders -/

/-- The list `τ` enumerates the states outside `U` in the order of
their first entrances. -/
def IsDiscoveryOrder (U : Finset V) (ω : ℕ → V) (τ : List V) : Prop :=
  τ.toFinset = univ \ U ∧ (∀ v ∈ τ, Hits ω v) ∧
    τ.Pairwise fun u v => hitTime ω u < hitTime ω v

/-- The state from which `v` is first entered, `X_{T_v - 1}`. -/
noncomputable def entranceParent (ω : ℕ → V) (v : V) : V :=
  ω (hitTime ω v - 1)

/-- The chain starts at `a`, discovers the states outside `U` in the
order `τ`, and first enters each `v` of `τ` from `g v`. -/
def orderEvent (g : V → V) (U : Finset V) (a : V) (τ : List V) :
    Set (ℕ → V) :=
  {ω | ω 0 = a ∧ IsDiscoveryOrder U ω τ ∧
    ∀ v ∈ τ, entranceParent ω v = g v}

/-- The chain starts at `a`, stays in `U` up to time `n`, is at the
parent `g z` at time `n`, and enters `z` at time `n + 1`. -/
def firstEntrance (g : V → V) (U : Finset V) (a z : V) (n : ℕ) :
    Set (ℕ → V) :=
  {ω | ω 0 = a ∧ (∀ t ≤ n, ω t ∈ U) ∧ ω n = g z ∧ ω (n + 1) = z}

omit [Fintype V] [DecidableEq V] [MeasurableSpace V]
  [MeasurableSingletonClass V] in
theorem prefixEvent_firstEntrance (g : V → V) (U : Finset V)
    (a z : V) (n : ℕ) :
    PrefixEvent (n + 1) (firstEntrance g U a z n) := by
  intro ω ω' h
  simp only [firstEntrance, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h0, hU, hn, hz⟩
    refine ⟨?_, fun t ht => ?_, ?_, ?_⟩
    · rw [← h 0 (by omega)]
      exact h0
    · rw [← h t (by omega)]
      exact hU t ht
    · rw [← h n (by omega)]
      exact hn
    · rw [← h (n + 1) le_rfl]
      exact hz
  · rintro ⟨h0, hU, hn, hz⟩
    refine ⟨?_, fun t ht => ?_, ?_, ?_⟩
    · rw [h 0 (by omega)]
      exact h0
    · rw [h t (by omega)]
      exact hU t ht
    · rw [h n (by omega)]
      exact hn
    · rw [h (n + 1) le_rfl]
      exact hz

omit [Fintype V] [DecidableEq V] [MeasurableSpace V]
  [MeasurableSingletonClass V] in
theorem firstEntrance_hitTime {g : V → V} {U : Finset V} {a z : V}
    {n : ℕ} (hz : z ∉ U) {ω : ℕ → V}
    (h : ω ∈ firstEntrance g U a z n) : hitTime ω z = n + 1 :=
  hitTime_eq h.2.2.2 fun t ht heq =>
    hz (heq ▸ h.2.1 t (by omega))

/-- The probability of an excursion of length `n` inside `U` from
`a` to the parent of `z`, followed by the edge into `z`. -/
theorem chainLaw_firstEntrance (P : Matrix V V ℝ)
    (hP : IsStochastic P) (g : V → V) (U : Finset V) (a z : V)
    (n : ℕ) :
    chainLaw P hP a (firstEntrance g U a z n) =
      ENNReal.ofReal (confinedPow P U n a (g z)) *
        ENNReal.ofReal (P (g z) z) := by
  have hset : firstEntrance g U a z n =
      (confinedAt U n (g z) ∩ {ω | ω 0 = a}) ∩
        shift n ⁻¹' {ω | ω 1 = z} := by
    apply Set.ext
    intro ω
    simp only [firstEntrance, confinedAt, Set.mem_setOf_eq,
      Set.mem_inter_iff, Set.mem_preimage, shift]
    rw [Nat.add_comm 1 n]
    tauto
  have hprefix : PrefixEvent n
      (confinedAt U n (g z) ∩ {ω : ℕ → V | ω 0 = a}) := by
    intro ω ω' h
    have h1 := prefixEvent_confinedAt U n (g z) ω ω' h
    have h0 := h 0 (Nat.zero_le n)
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, h1, h0]
  rw [hset, chainLaw_prefix_inter_shift P hP a (g z) hprefix
      (fun ω hω => confinedAt_last hω.1)
      (measurableSet_coordinate 1 z),
    chainLaw_inter_start, chainLaw_confinedAt, chainLaw_first_step]

/-! ## Decomposition at the first entrance -/

omit [MeasurableSpace V] [MeasurableSingletonClass V] in
/-- The event of a discovery order `(z, rest)` is the disjoint union
over the length of the first excursion. -/
theorem orderEvent_cons (g : V → V) (U : Finset V) (a z : V)
    (rest : List V) (ha : a ∈ U) (hz : z ∉ U) :
    orderEvent g U a (z :: rest) =
      ⋃ n : ℕ, firstEntrance g U a z n ∩
        shift (n + 1) ⁻¹' orderEvent g (insert z U) z rest := by
  have hcompl : univ \ insert z U = (univ \ U).erase z := by
    ext x
    simp
  apply Set.ext
  intro ω
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · rintro ⟨h0, ⟨hfin, hhits, hpair⟩, hpar⟩
    have hzhit : Hits ω z := hhits z (by simp)
    obtain ⟨hfirst, hrestPair⟩ := List.pairwise_cons.mp hpair
    have hzrest : z ∉ rest := fun h => lt_irrefl _ (hfirst z h)
    have hN : 1 ≤ hitTime ω z := by
      by_contra hlt
      have h0' : hitTime ω z = 0 := by omega
      have hspec := hitTime_spec hzhit
      rw [h0', h0] at hspec
      exact hz (hspec ▸ ha)
    have hbeforeU : ∀ t < hitTime ω z, ω t ∈ U := by
      intro t ht
      by_contra hnot
      have hmem : ω t ∈ (z :: rest).toFinset := by
        rw [hfin]
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩
      rcases List.mem_cons.mp (List.mem_toFinset.mp hmem) with
        hzeq | hrest
      · exact ne_of_lt_hitTime ht hzeq
      · have h1 := hfirst _ hrest
        have h2 : hitTime ω (ω t) ≤ t := hitTime_le rfl
        omega
    have hshift : ∀ v ∈ rest,
        Hits (shift (hitTime ω z) ω) v ∧
          hitTime (shift (hitTime ω z) ω) v =
            hitTime ω v - hitTime ω z :=
      fun v hv => hitTime_shift_of_le
        (hhits v (List.mem_cons_of_mem z hv)) (hfirst v hv).le
    refine ⟨hitTime ω z - 1,
      ⟨h0, fun t ht => hbeforeU t (by omega), ?_, ?_⟩, ?_⟩
    · exact hpar z (by simp)
    · rw [Nat.sub_add_cancel hN]
      exact hitTime_spec hzhit
    · rw [Nat.sub_add_cancel hN]
      refine ⟨?_, ⟨?_, fun v hv => (hshift v hv).1, ?_⟩, ?_⟩
      · simp only [shift]
        rw [Nat.zero_add]
        exact hitTime_spec hzhit
      · rw [hcompl, ← hfin, List.toFinset_cons,
          Finset.erase_insert (by simpa using hzrest)]
      · apply hrestPair.imp_of_mem
        intro u v hu hv huv
        rw [(hshift u hu).2, (hshift v hv).2]
        have := hfirst u hu
        omega
      · intro v hv
        have hv' := hpar v (List.mem_cons_of_mem z hv)
        have hlt := hfirst v hv
        simp only [entranceParent] at hv' ⊢
        rw [(hshift v hv).2, ← hv']
        simp only [shift]
        congr 1
        omega
  · rintro ⟨n, ⟨h0, hU, hgz, hz1⟩, h0', ⟨hfin', hhits', hpair'⟩,
      hpar'⟩
    have hzrest : z ∉ rest := by
      intro h
      have hmem : z ∈ rest.toFinset := List.mem_toFinset.mpr h
      rw [hfin'] at hmem
      exact (Finset.mem_sdiff.mp hmem).2 (Finset.mem_insert_self z U)
    have hzhit : hitTime ω z = n + 1 :=
      hitTime_eq hz1 fun t ht heq => hz (heq ▸ hU t (by omega))
    have hrest : ∀ v ∈ rest, Hits ω v ∧
        hitTime ω v = hitTime (shift (n + 1) ω) v + (n + 1) := by
      intro v hv
      apply hitTime_of_shift (hhits' v hv)
      intro t ht heq
      have hvU : v ∉ insert z U := by
        have hmem : v ∈ rest.toFinset := List.mem_toFinset.mpr hv
        rw [hfin'] at hmem
        exact (Finset.mem_sdiff.mp hmem).2
      exact hvU (Finset.mem_insert_of_mem (heq ▸ hU t (by omega)))
    have hpos : ∀ v ∈ rest, 1 ≤ hitTime (shift (n + 1) ω) v := by
      intro v hv
      by_contra hlt
      have h0v : hitTime (shift (n + 1) ω) v = 0 := by omega
      have hspec := hitTime_spec (hhits' v hv)
      rw [h0v, h0'] at hspec
      exact hzrest (hspec ▸ hv)
    refine ⟨h0, ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [List.toFinset_cons, hfin', hcompl,
        Finset.insert_erase
          (Finset.mem_sdiff.mpr ⟨Finset.mem_univ z, hz⟩)]
    · intro v hv
      rcases List.mem_cons.mp hv with hvz | hv'
      · exact ⟨n + 1, hz1.trans hvz.symm⟩
      · exact (hrest v hv').1
    · apply List.pairwise_cons.mpr
      refine ⟨fun v hv => ?_, ?_⟩
      · rw [hzhit, (hrest v hv).2]
        have := hpos v hv
        omega
      · apply hpair'.imp_of_mem
        intro u v hu hv huv
        rw [(hrest u hu).2, (hrest v hv).2]
        omega
    · intro v hv
      rcases List.mem_cons.mp hv with hvz | hv'
      · rw [hvz]
        simp only [entranceParent]
        rw [hzhit, Nat.add_sub_cancel]
        exact hgz
      · have hparent := hpar' v hv'
        have hge := hpos v hv'
        simp only [entranceParent, shift] at hparent ⊢
        rw [(hrest v hv').2, ← hparent]
        congr 1
        omega

omit [Fintype V] [DecidableEq V] [MeasurableSpace V]
  [MeasurableSingletonClass V] in
/-- The events of the decomposition are pairwise disjoint: the
length of the first excursion is determined by the first-entrance
time of `z`. -/
theorem disjoint_firstEntrance (g : V → V) (U : Finset V) (a z : V)
    (hz : z ∉ U) (E : Set (ℕ → V)) :
    Pairwise (Function.onFun Disjoint fun n : ℕ =>
      firstEntrance g U a z n ∩ shift (n + 1) ⁻¹' E) := by
  intro n n' hne
  apply Set.disjoint_left.mpr
  rintro ω ⟨hn, -⟩ ⟨hn', -⟩
  apply hne
  have h1 := firstEntrance_hitTime hz hn
  have h2 := firstEntrance_hitTime hz hn'
  omega

/-- The event of a discovery order is measurable. -/
theorem measurableSet_orderEvent (g : V → V) :
    ∀ (τ : List V) (U : Finset V) (a : V), a ∈ U →
      (∀ z ∈ τ, z ∉ U) → τ.Nodup →
      MeasurableSet (orderEvent g U a τ) := by
  intro τ
  induction τ with
  | nil =>
      intro U a _ _ _
      by_cases hU : ([] : List V).toFinset = univ \ U
      · have hset : orderEvent g U a [] = {ω | ω 0 = a} := by
          apply Set.ext
          intro ω
          simp [orderEvent, IsDiscoveryOrder, hU]
        rw [hset]
        exact measurableSet_start a
      · have hset : orderEvent g U a [] = ∅ := by
          apply Set.eq_empty_of_forall_notMem
          rintro ω ⟨-, ⟨hfin, -⟩, -⟩
          exact hU hfin
        rw [hset]
        exact MeasurableSet.empty
  | cons z rest ih =>
      intro U a ha hdisj hnodup
      have hz : z ∉ U := hdisj z (by simp)
      obtain ⟨hzrest, hrestNodup⟩ := List.nodup_cons.mp hnodup
      rw [orderEvent_cons g U a z rest ha hz]
      apply MeasurableSet.iUnion
      intro n
      apply (prefixEvent_firstEntrance g U a z n).measurableSet.inter
      apply measurable_shift (n + 1)
      apply ih (insert z U) z (Finset.mem_insert_self z U) _
        hrestNodup
      intro v hv hmem
      rcases Finset.mem_insert.mp hmem with hvz | hvU
      · exact hzrest (hvz ▸ hv)
      · exact hdisj v (List.mem_cons_of_mem z hv) hvU

/-! ## The excursion formula -/

/-- The weight of Lemma `lem:excursion`,
`∏_l (G_{U_{l-1}})_{τ_{l-1}, g(τ_l)} P_{g(τ_l), τ_l}` with `τ_0 = a`,
by recursion on the order: the first factor belongs to the base `U`
and the remaining factors to the order `rest` started at `z` with
the base `U ∪ {z}`. -/
noncomputable def excursionWeight (P : Matrix V V ℝ) (g : V → V) :
    Finset V → V → List V → ℝ
  | _, _, [] => 1
  | U, a, z :: rest =>
      green P U a (g z) * P (g z) z *
        excursionWeight P g (insert z U) z rest

omit [MeasurableSpace V] [MeasurableSingletonClass V] in
theorem excursionWeight_nonneg {P : Matrix V V ℝ}
    (hP : IsStochastic P) (hirr : IsIrreducible P) (g : V → V) :
    ∀ (τ : List V) (U : Finset V) (a : V), (∀ z ∈ τ, z ∉ U) →
      τ.Nodup → 0 ≤ excursionWeight P g U a τ := by
  intro τ
  induction τ with
  | nil => intro U a _ _; exact zero_le_one
  | cons z rest ih =>
      intro U a hdisj hnodup
      have hz : z ∉ U := hdisj z (by simp)
      have hU : U ≠ univ := fun h => hz (h ▸ Finset.mem_univ z)
      obtain ⟨hzrest, hrestNodup⟩ := List.nodup_cons.mp hnodup
      have hrest : ∀ v ∈ rest, v ∉ insert z U := by
        intro v hv hmem
        rcases Finset.mem_insert.mp hmem with hvz | hvU
        · exact hzrest (hvz ▸ hv)
        · exact hdisj v (List.mem_cons_of_mem z hv) hvU
      exact mul_nonneg
        (mul_nonneg (green_nonneg hP hirr U hU a (g z))
          (hP.nonneg (g z) z))
        (ih (insert z U) z hrest hrestNodup)

/-- **Lemma `lem:excursion`.** The probability that the chain
started at `a ∈ U` discovers the states outside `U` in the order `τ`,
entering each from its parent under `g`. -/
theorem chainLaw_orderEvent (P : Matrix V V ℝ) (hP : IsStochastic P)
    (hirr : IsIrreducible P) (g : V → V) :
    ∀ (τ : List V) (U : Finset V) (a : V), a ∈ U → τ.Nodup →
      τ.toFinset = univ \ U →
      chainLaw P hP a (orderEvent g U a τ) =
        ENNReal.ofReal (excursionWeight P g U a τ) := by
  intro τ
  induction τ with
  | nil =>
      intro U a _ _ hfin
      have hset : orderEvent g U a [] = {ω | ω 0 = a} := by
        apply Set.ext
        intro ω
        simp [orderEvent, IsDiscoveryOrder, hfin]
      rw [hset, chainLaw_start]
      simp [excursionWeight]
  | cons z rest ih =>
      intro U a ha hnodup hfin
      have hzmem : z ∈ univ \ U := by
        rw [← hfin]
        simp
      have hz : z ∉ U := (Finset.mem_sdiff.mp hzmem).2
      have hU : U ≠ univ := fun h => hz (h ▸ Finset.mem_univ z)
      obtain ⟨hzrest, hrestNodup⟩ := List.nodup_cons.mp hnodup
      have hfin' : rest.toFinset = univ \ insert z U := by
        have hcompl : univ \ insert z U = (univ \ U).erase z := by
          ext x
          simp
        rw [hcompl, ← hfin, List.toFinset_cons,
          Finset.erase_insert (by simpa using hzrest)]
      have hdisj : ∀ v ∈ rest, v ∉ insert z U := by
        intro v hv
        have hmem : v ∈ rest.toFinset := List.mem_toFinset.mpr hv
        rw [hfin'] at hmem
        exact (Finset.mem_sdiff.mp hmem).2
      have hmeas : MeasurableSet
          (orderEvent g (insert z U) z rest) :=
        measurableSet_orderEvent g rest (insert z U) z
          (Finset.mem_insert_self z U) hdisj hrestNodup
      have hterm : ∀ n : ℕ,
          chainLaw P hP a (firstEntrance g U a z n ∩
            shift (n + 1) ⁻¹' orderEvent g (insert z U) z rest) =
          ENNReal.ofReal (confinedPow P U n a (g z)) *
            (ENNReal.ofReal (P (g z) z) *
              ENNReal.ofReal
                (excursionWeight P g (insert z U) z rest)) := by
        intro n
        rw [chainLaw_prefix_inter_shift P hP a z
            (prefixEvent_firstEntrance g U a z n)
            (fun ω hω => hω.2.2.2) hmeas,
          chainLaw_firstEntrance,
          ih (insert z U) z (Finset.mem_insert_self z U) hrestNodup
            hfin',
          mul_assoc]
      have hsum := hasSum_confinedPow hP hirr U hU a (g z)
      rw [orderEvent_cons g U a z rest ha hz,
        measure_iUnion (disjoint_firstEntrance g U a z hz _)
          (fun n => (prefixEvent_firstEntrance g U a z n).measurableSet.inter
            (measurable_shift (n + 1) hmeas))]
      simp only [hterm]
      rw [ENNReal.tsum_mul_right,
        ← ENNReal.ofReal_tsum_of_nonneg
          (fun n => confinedPow_nonneg hP U n a (g z)) hsum.summable,
        hsum.tsum_eq]
      simp only [excursionWeight]
      rw [ENNReal.ofReal_mul
          (mul_nonneg (green_nonneg hP hirr U hU a (g z))
            (hP.nonneg (g z) z)),
        ENNReal.ofReal_mul (green_nonneg hP hirr U hU a (g z)),
        mul_assoc]

end EAB.Paper.Chain
