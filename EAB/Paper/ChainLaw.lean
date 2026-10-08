import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import EAB.Paper.ConfinedChain

/-!
# The law of the chain on trajectories

The law `ℙ_r` of the Markov chain with transition matrix `P` started
at `r` is the Ionescu-Tulcea trajectory measure on `ℕ → V` with
initial law the Dirac mass at `r` and with the transition kernel
induced by `P`. The finite-cylinder formula

`ℙ_r (X_0 = x_0, …, X_m = x_m) = 𝟏_{r}(x_0) ∏_{t<m} P_{x_t x_{t+1}}`

is the only property of the measure used by the later files.
-/

open MeasureTheory ProbabilityTheory Finset

namespace EAB.Paper.Chain

variable {V : Type*} [Fintype V] [DecidableEq V]
  [MeasurableSpace V] [MeasurableSingletonClass V]

/-! ## One step -/

/-- The law of one step from `u`: the row `u` of `P`. -/
noncomputable def stepMeasure (P : Matrix V V ℝ) (u : V) : Measure V :=
  ∑ v, ENNReal.ofReal (P u v) • Measure.dirac v

theorem stepMeasure_singleton (P : Matrix V V ℝ) (u v : V) :
    stepMeasure P u {v} = ENNReal.ofReal (P u v) := by
  simp only [stepMeasure, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.smul_apply, smul_eq_mul, Measure.dirac_apply,
    Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply]
  rw [Finset.sum_eq_single v]
  · simp
  · intro w _ hw
    simp [hw]
  · intro h
    exact absurd (Finset.mem_univ v) h

omit [DecidableEq V] [MeasurableSingletonClass V] in
theorem isProbabilityMeasure_stepMeasure {P : Matrix V V ℝ}
    (hP : IsStochastic P) (u : V) :
    IsProbabilityMeasure (stepMeasure P u) := by
  constructor
  simp only [stepMeasure, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun v _ => hP.nonneg u v),
    hP.row_sum u, ENNReal.ofReal_one]

/-- The transition kernel on the state space. -/
noncomputable def transitionKernel (P : Matrix V V ℝ) : Kernel V V :=
  Kernel.ofFunOfCountable (stepMeasure P)

omit [DecidableEq V] in
theorem transitionKernel_apply (P : Matrix V V ℝ) (u : V) :
    transitionKernel P u = stepMeasure P u :=
  rfl

/-- The kernel giving the state at time `n + 1` from the trajectory
up to time `n`. It reads the last state only. -/
noncomputable def stepKernel (P : Matrix V V ℝ) (n : ℕ) :
    Kernel (Π _ : Iic n, V) V :=
  (transitionKernel P).comap
    (fun y => y ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
    (measurable_pi_apply _)

omit [DecidableEq V] in
theorem stepKernel_apply (P : Matrix V V ℝ) (n : ℕ)
    (y : Π _ : Iic n, V) :
    stepKernel P n y =
      stepMeasure P (y ⟨n, Finset.mem_Iic.mpr le_rfl⟩) :=
  rfl

omit [DecidableEq V] in
theorem isMarkovKernel_stepKernel {P : Matrix V V ℝ}
    (hP : IsStochastic P) (n : ℕ) :
    IsMarkovKernel (stepKernel P n) :=
  ⟨fun y => by
    rw [stepKernel_apply]
    exact isProbabilityMeasure_stepMeasure hP _⟩

/-! ## The law on trajectories -/

/-- The law `ℙ_r` of the chain with transition matrix `P` started
at `r`. -/
noncomputable def chainLaw (P : Matrix V V ℝ) (hP : IsStochastic P)
    (r : V) : Measure (ℕ → V) :=
  haveI : ∀ n, IsMarkovKernel (stepKernel P n) :=
    isMarkovKernel_stepKernel hP
  Kernel.trajMeasure (X := fun _ => V) (Measure.dirac r) (stepKernel P)

instance isProbabilityMeasure_chainLaw (P : Matrix V V ℝ)
    (hP : IsStochastic P) (r : V) :
    IsProbabilityMeasure (chainLaw P hP r) := by
  haveI : ∀ n, IsMarkovKernel (stepKernel P n) :=
    isMarkovKernel_stepKernel hP
  unfold chainLaw
  infer_instance

/-- The trajectory up to time `m`. -/
def initialSegment (m : ℕ) (ω : ℕ → V) : (Π _ : Iic m, V) :=
  Preorder.frestrictLe (π := fun _ => V) m ω

omit [Fintype V] [DecidableEq V] [MeasurableSingletonClass V] in
theorem measurable_initialSegment (m : ℕ) :
    Measurable (initialSegment (V := V) m) :=
  Preorder.measurable_frestrictLe (X := fun _ => V) m

/-- The event `X_0 = x_0, …, X_m = x_m`. -/
def cylinder (x : ℕ → V) (m : ℕ) : Set (ℕ → V) :=
  {ω | ∀ t ≤ m, ω t = x t}

omit [Fintype V] [DecidableEq V] [MeasurableSpace V]
  [MeasurableSingletonClass V] in
theorem cylinder_eq_preimage (x : ℕ → V) (m : ℕ) :
    cylinder x m =
      initialSegment m ⁻¹'
        ({initialSegment m x} : Set (Π _ : Iic m, V)) := by
  apply Set.ext
  intro ω
  simp only [cylinder, Set.mem_setOf_eq, Set.mem_preimage,
    Set.mem_singleton_iff]
  constructor
  · intro h
    funext i
    exact h i (Finset.mem_Iic.mp i.2)
  · intro h t ht
    exact congrFun h ⟨t, Finset.mem_Iic.mpr ht⟩

omit [Fintype V] [DecidableEq V] [MeasurableSpace V]
  [MeasurableSingletonClass V] in
theorem cylinder_succ_eq_preimage (x : ℕ → V) (m : ℕ) :
    cylinder x (m + 1) =
      (fun ω : ℕ → V => (initialSegment m ω, ω (m + 1))) ⁻¹'
        (({initialSegment m x} : Set (Π _ : Iic m, V)) ×ˢ
          ({x (m + 1)} : Set V)) := by
  apply Set.ext
  intro ω
  simp only [cylinder, Set.mem_setOf_eq, Set.mem_preimage,
    Set.mem_prod, Set.mem_singleton_iff]
  constructor
  · intro h
    refine ⟨?_, h (m + 1) le_rfl⟩
    funext i
    exact h i ((Finset.mem_Iic.mp i.2).trans (Nat.le_succ m))
  · rintro ⟨hrest, hlast⟩ t ht
    rcases Nat.lt_or_ge t (m + 1) with hlt | hge
    · exact congrFun hrest ⟨t, Finset.mem_Iic.mpr (by omega)⟩
    · have ht' : t = m + 1 := by omega
      rw [ht']
      exact hlast

omit [Fintype V] [DecidableEq V] in
theorem measurableSet_cylinder (x : ℕ → V) (m : ℕ) :
    MeasurableSet (cylinder x m) := by
  rw [cylinder_eq_preimage]
  exact measurable_initialSegment m (measurableSet_singleton _)

/-- The finite-cylinder formula. -/
theorem chainLaw_cylinder (P : Matrix V V ℝ) (hP : IsStochastic P)
    (r : V) (x : ℕ → V) (m : ℕ) :
    chainLaw P hP r (cylinder x m) =
      (if x 0 = r then 1 else 0) *
        ∏ t ∈ Finset.range m, ENNReal.ofReal (P (x t) (x (t + 1))) := by
  haveI : ∀ n, IsMarkovKernel (stepKernel P n) :=
    isMarkovKernel_stepKernel hP
  induction m with
  | zero =>
      rw [Finset.range_zero, Finset.prod_empty, mul_one,
        cylinder_eq_preimage,
        ← Measure.map_apply (measurable_initialSegment 0)
          (measurableSet_singleton _)]
      have hmarginal :
          (chainLaw P hP r).map (initialSegment 0) =
            (Measure.dirac r).map
              (MeasurableEquiv.piUnique
                (fun _ : Iic 0 => V)).symm := by
        unfold chainLaw Kernel.trajMeasure initialSegment
        rw [Measure.map_comp _ _ (Preorder.measurable_frestrictLe 0),
          Kernel.traj_map_frestrictLe, Kernel.partialTraj_self,
          Measure.id_comp]
      rw [hmarginal, Measure.map_dirac' (MeasurableEquiv.measurable _),
        Measure.dirac_apply, Set.indicator_apply]
      simp only [Set.mem_singleton_iff, Pi.one_apply]
      by_cases hx : x 0 = r
      · rw [if_pos hx, if_pos]
        funext i
        have hi : (i : ℕ) = 0 := by
          have := Finset.mem_Iic.mp i.2
          omega
        have hi' : i = ⟨0, Finset.mem_Iic.mpr le_rfl⟩ := Subtype.ext hi
        subst hi'
        exact hx.symm
      · rw [if_neg hx, if_neg]
        intro h
        apply hx
        have h0 := congrFun h ⟨0, Finset.mem_Iic.mpr le_rfl⟩
        exact h0.symm
  | succ m ih =>
      have hφ : Measurable (fun ω : ℕ → V =>
          (initialSegment m ω, ω (m + 1))) :=
        (measurable_initialSegment m).prodMk
          (measurable_pi_apply (m + 1))
      have hset : MeasurableSet
          (({initialSegment m x} : Set (Π _ : Iic m, V)) ×ˢ
            ({x (m + 1)} : Set V)) :=
        (measurableSet_singleton _).prod (measurableSet_singleton _)
      have hstep :
          (chainLaw P hP r).map (initialSegment m) ⊗ₘ stepKernel P m =
            (chainLaw P hP r).map
              (fun ω => (initialSegment m ω, ω (m + 1))) :=
        Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
          (X := fun _ => V) (μ₀ := Measure.dirac r)
          (κ := stepKernel P) (a := m)
      rw [cylinder_succ_eq_preimage, ← Measure.map_apply hφ hset,
        ← hstep, Measure.compProd_apply_prod
          (measurableSet_singleton _) (measurableSet_singleton _),
        lintegral_singleton,
        Measure.map_apply (measurable_initialSegment m)
          (measurableSet_singleton _),
        ← cylinder_eq_preimage, ih, stepKernel_apply,
        stepMeasure_singleton, Finset.prod_range_succ]
      change ENNReal.ofReal (P (x m) (x (m + 1))) * _ = _
      ring

end EAB.Paper.Chain
