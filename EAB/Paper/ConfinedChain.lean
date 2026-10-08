import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.IntermediateValue
import EAB.Paper.MatrixFoundation

/-!
# Confined chains: escape, Green series, positive minors

Lemma `lem:confined` of the blueprint. For an irreducible stochastic
matrix `P` and a nonempty proper set `U`, the confined matrix `P[U]`
has row sums of its `(n-1)`-st power below one. Its powers decay
geometrically, the Neumann series inverts `I - P[U]`, and
`det (I - P[U])` is positive.

The first part of the file concerns a substochastic matrix on an
arbitrary finite index type. The second part obtains the escape
bound for `P[U]` from irreducibility.
-/

open Finset Matrix Filter Topology

namespace EAB.Paper.Chain

/-! ## Substochastic matrices -/

section Substochastic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A nonnegative matrix whose row sums are at most one. -/
structure IsSubstochastic (A : Matrix ι ι ℝ) : Prop where
  nonneg : ∀ i j, 0 ≤ A i j
  row_le : ∀ i, ∑ j, A i j ≤ 1

/-- The row sum at `i` of the `t`-th power. -/
def rowSum (A : Matrix ι ι ℝ) (t : ℕ) (i : ι) : ℝ :=
  ∑ j, (A ^ t) i j

variable {A : Matrix ι ι ℝ}

theorem IsSubstochastic.pow_nonneg (hA : IsSubstochastic A) (t : ℕ)
    (i j : ι) : 0 ≤ (A ^ t) i j :=
  Matrix.pow_apply_nonneg hA.nonneg t i j

theorem rowSum_zero (A : Matrix ι ι ℝ) (i : ι) : rowSum A 0 i = 1 := by
  simp [rowSum, Matrix.one_apply]

theorem rowSum_one (A : Matrix ι ι ℝ) (i : ι) :
    rowSum A 1 i = ∑ j, A i j := by
  simp [rowSum]

theorem rowSum_add (A : Matrix ι ι ℝ) (a b : ℕ) (i : ι) :
    rowSum A (a + b) i = ∑ k, (A ^ a) i k * rowSum A b k := by
  simp only [rowSum, pow_add, Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_comm

theorem IsSubstochastic.rowSum_nonneg (hA : IsSubstochastic A)
    (t : ℕ) (i : ι) : 0 ≤ rowSum A t i :=
  Finset.sum_nonneg fun j _ => hA.pow_nonneg t i j

theorem IsSubstochastic.entry_le_rowSum (hA : IsSubstochastic A)
    (t : ℕ) (i j : ι) : (A ^ t) i j ≤ rowSum A t i :=
  Finset.single_le_sum (fun k _ => hA.pow_nonneg t i k)
    (Finset.mem_univ j)

/-- Submultiplicativity of the maximum row sum. -/
theorem IsSubstochastic.rowSum_add_le (hA : IsSubstochastic A)
    (a b : ℕ) {c : ℝ} (hc : ∀ k, rowSum A b k ≤ c) (i : ι) :
    rowSum A (a + b) i ≤ rowSum A a i * c := by
  rw [rowSum_add, rowSum, Finset.sum_mul]
  exact Finset.sum_le_sum fun k _ =>
    mul_le_mul_of_nonneg_left (hc k) (hA.pow_nonneg a i k)

theorem IsSubstochastic.rowSum_succ_le (hA : IsSubstochastic A)
    (t : ℕ) (i : ι) : rowSum A (t + 1) i ≤ rowSum A t i := by
  have h := hA.rowSum_add_le t 1 (c := 1)
    (fun k => by rw [rowSum_one]; exact hA.row_le k) i
  simpa using h

theorem IsSubstochastic.rowSum_antitone (hA : IsSubstochastic A)
    (i : ι) : Antitone fun t => rowSum A t i :=
  antitone_nat_of_succ_le fun t => hA.rowSum_succ_le t i

theorem IsSubstochastic.rowSum_le_one (hA : IsSubstochastic A)
    (t : ℕ) (i : ι) : rowSum A t i ≤ 1 := by
  have h := hA.rowSum_antitone i (Nat.zero_le t)
  simpa [rowSum_zero] using h

/-- Geometric decay along multiples of `N`. -/
theorem IsSubstochastic.rowSum_mul_le (hA : IsSubstochastic A)
    {N : ℕ} {c : ℝ} (hc : ∀ k, rowSum A N k ≤ c) (m : ℕ) (i : ι) :
    rowSum A (m * N) i ≤ c ^ m := by
  have hc0 : 0 ≤ c := (hA.rowSum_nonneg N i).trans (hc i)
  induction m generalizing i with
  | zero => simp [rowSum_zero]
  | succ m ih =>
      rw [Nat.succ_mul, pow_succ]
      exact (hA.rowSum_add_le (m * N) N hc i).trans
        (mul_le_mul_of_nonneg_right (ih i) hc0)

/-- The entries of the powers tend to zero. -/
theorem IsSubstochastic.tendsto_pow_entry (hA : IsSubstochastic A)
    {N : ℕ} (hN : 0 < N) {c : ℝ} (hc1 : c < 1)
    (hc : ∀ k, rowSum A N k ≤ c) (i j : ι) :
    Tendsto (fun t => (A ^ t) i j) atTop (𝓝 0) := by
  have hc0 : 0 ≤ c := (hA.rowSum_nonneg N i).trans (hc i)
  have hbound : ∀ t, (A ^ t) i j ≤ c ^ (t / N) := by
    intro t
    calc
      (A ^ t) i j ≤ rowSum A t i := hA.entry_le_rowSum t i j
      _ ≤ rowSum A (t / N * N) i :=
        hA.rowSum_antitone i (Nat.div_mul_le_self t N)
      _ ≤ c ^ (t / N) := hA.rowSum_mul_le hc (t / N) i
  have hdiv : Tendsto (fun t : ℕ => t / N) atTop atTop :=
    Nat.tendsto_div_const_atTop (Nat.pos_iff_ne_zero.mp hN)
  have hpow : Tendsto (fun t : ℕ => c ^ (t / N)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).comp hdiv
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    hpow (fun t => hA.pow_nonneg t i j) hbound

/-- `I - A` is nonsingular: a vector fixed by `A` is fixed by every
power, and the powers tend to zero. -/
theorem IsSubstochastic.det_one_sub_ne_zero (hA : IsSubstochastic A)
    {N : ℕ} (hN : 0 < N) {c : ℝ} (hc1 : c < 1)
    (hc : ∀ k, rowSum A N k ≤ c) : (1 - A).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hfix : A *ᵥ v = v := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hker
    exact hker.symm
  have hpow : ∀ t : ℕ, (A ^ t) *ᵥ v = v := by
    intro t
    induction t with
    | zero => simp
    | succ t ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hfix, ih]
  apply hv
  funext i
  have hlim : Tendsto (fun t => ((A ^ t) *ᵥ v) i) atTop (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.univ : Finset ι)
      (fun j _ => (hA.tendsto_pow_entry hN hc1 hc i j).mul_const (v j))
    simpa [Matrix.mulVec, dotProduct] using h
  have hconst : Tendsto (fun t => ((A ^ t) *ᵥ v) i) atTop (𝓝 (v i)) := by
    simp only [hpow]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hconst hlim

/-- The Neumann series: the powers of `A` sum entrywise to the
inverse of `I - A`. -/
theorem IsSubstochastic.hasSum_pow_entry (hA : IsSubstochastic A)
    {N : ℕ} (hN : 0 < N) {c : ℝ} (hc1 : c < 1)
    (hc : ∀ k, rowSum A N k ≤ c) (i j : ι) :
    HasSum (fun t => (A ^ t) i j) ((1 - A)⁻¹ i j) := by
  have hunit : IsUnit (1 - A).det :=
    isUnit_iff_ne_zero.mpr (hA.det_one_sub_ne_zero hN hc1 hc)
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun t => hA.pow_nonneg t i j)]
  have hpartial : ∀ T : ℕ,
      ∑ t ∈ Finset.range T, (A ^ t) i j =
        (1 - A)⁻¹ i j - ∑ k, (1 - A)⁻¹ i k * (A ^ T) k j := by
    intro T
    have hgeom : (1 - A) * ∑ t ∈ Finset.range T, A ^ t = 1 - A ^ T :=
      mul_neg_geom_sum A T
    have hsolve : ∑ t ∈ Finset.range T, A ^ t =
        (1 - A)⁻¹ * (1 - A ^ T) := by
      rw [← hgeom, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunit,
        Matrix.one_mul]
    have hentry := congrFun (congrFun hsolve i) j
    rw [Matrix.sum_apply] at hentry
    rw [hentry, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_apply,
      Matrix.mul_apply]
  simp only [hpartial]
  have hzero : Tendsto
      (fun T => ∑ k, (1 - A)⁻¹ i k * (A ^ T) k j) atTop (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.univ : Finset ι)
      (fun k _ => (hA.tendsto_pow_entry hN hc1 hc k j).const_mul
        ((1 - A)⁻¹ i k))
    simpa using h
  simpa using tendsto_const_nhds.sub hzero

omit [DecidableEq ι] in
theorem IsSubstochastic.smul (hA : IsSubstochastic A) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : IsSubstochastic (s • A) where
  nonneg i j := by
    simpa using mul_nonneg hs0 (hA.nonneg i j)
  row_le i := by
    have hsum : ∑ j, (s • A) i j = s * ∑ j, A i j := by
      simp [Finset.mul_sum]
    rw [hsum]
    have hnonneg : 0 ≤ ∑ j, A i j :=
      Finset.sum_nonneg fun j _ => hA.nonneg i j
    calc
      s * ∑ j, A i j ≤ 1 * ∑ j, A i j :=
        mul_le_mul_of_nonneg_right hs1 hnonneg
      _ ≤ 1 := by simpa using hA.row_le i

theorem IsSubstochastic.rowSum_smul_le (hA : IsSubstochastic A)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (t : ℕ) (i : ι) :
    rowSum (s • A) t i ≤ rowSum A t i := by
  have hpow : (s • A) ^ t = s ^ t • A ^ t := smul_pow s A t
  have hsum : rowSum (s • A) t i = s ^ t * rowSum A t i := by
    simp [rowSum, hpow, Finset.mul_sum]
  rw [hsum]
  calc
    s ^ t * rowSum A t i ≤ 1 * rowSum A t i :=
      mul_le_mul_of_nonneg_right (pow_le_one₀ hs0 hs1)
        (hA.rowSum_nonneg t i)
    _ = rowSum A t i := one_mul _

/-- `det (I - A)` is positive. The function `s ↦ det (I - sA)` is
continuous on `[0,1]`, equals `1` at `s = 0`, and does not vanish. -/
theorem IsSubstochastic.det_one_sub_pos (hA : IsSubstochastic A)
    {N : ℕ} (hN : 0 < N) {c : ℝ} (hc1 : c < 1)
    (hc : ∀ k, rowSum A N k ≤ c) : 0 < (1 - A).det := by
  let F : ℝ → ℝ := fun s => (1 - s • A).det
  have hcont : Continuous F := by
    apply Continuous.matrix_det
    exact continuous_const.sub (continuous_id.smul continuous_const)
  have hne : ∀ s ∈ Set.Icc (0 : ℝ) 1, F s ≠ 0 := by
    intro s hs
    exact (hA.smul hs.1 hs.2).det_one_sub_ne_zero hN hc1
      (fun k => (hA.rowSum_smul_le hs.1 hs.2 N k).trans (hc k))
  have hF0 : F 0 = 1 := by simp [F]
  have hF1 : F 1 = (1 - A).det := by simp [F]
  rw [← hF1]
  by_contra hneg
  have hle : F 1 ≤ 0 := not_lt.mp hneg
  have hmem : (0 : ℝ) ∈ Set.Icc (F 1) (F 0) := by
    rw [hF0]
    exact ⟨hle, zero_le_one⟩
  obtain ⟨s, hs, hs0⟩ :=
    intermediate_value_Icc' (zero_le_one : (0 : ℝ) ≤ 1)
      hcont.continuousOn hmem
  exact hne s hs hs0

end Substochastic

/-! ## Stochastic and irreducible matrices -/

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A stochastic matrix: nonnegative entries and unit row sums. -/
structure IsStochastic (P : Matrix V V ℝ) : Prop where
  nonneg : ∀ u v, 0 ≤ P u v
  row_sum : ∀ u, ∑ v, P u v = 1

/-- Irreducibility: every state reaches every state. -/
def IsIrreducible (P : Matrix V V ℝ) : Prop :=
  ∀ u v, ∃ t : ℕ, 0 < (P ^ t) u v

variable {P : Matrix V V ℝ}

omit [DecidableEq V] in
theorem IsStochastic.mulVec_one (hP : IsStochastic P) :
    P *ᵥ (fun _ => 1) = fun _ => 1 := by
  funext u
  simpa [Matrix.mulVec, dotProduct] using hP.row_sum u

theorem IsStochastic.pow_nonneg (hP : IsStochastic P) (t : ℕ)
    (u v : V) : 0 ≤ (P ^ t) u v :=
  Matrix.pow_apply_nonneg hP.nonneg t u v

theorem IsStochastic.pow_row_sum (hP : IsStochastic P) (t : ℕ)
    (u : V) : ∑ v, (P ^ t) u v = 1 := by
  induction t generalizing u with
  | zero => simp [Matrix.one_apply]
  | succ t ih =>
      simp only [pow_succ, Matrix.mul_apply]
      rw [Finset.sum_comm]
      simp only [← Finset.mul_sum, hP.row_sum, mul_one]
      exact ih u

/-- A positive path may be taken with pairwise distinct states, so
some power of order at most `n - 1` has a positive entry. The sets
of states reached within `t` steps increase strictly until they
stop growing. -/
theorem IsStochastic.exists_pow_pos_le (hP : IsStochastic P)
    (hirr : IsIrreducible P) (u v : V) :
    ∃ t ≤ Fintype.card V - 1, 0 < (P ^ t) u v := by
  classical
  let R : ℕ → Finset V := fun t =>
    Finset.univ.filter fun x => ∃ s ≤ t, 0 < (P ^ s) u x
  have hRmem : ∀ t x, x ∈ R t ↔ ∃ s ≤ t, 0 < (P ^ s) u x := by
    intro t x
    simp [R]
  have hmono : ∀ {a b : ℕ}, a ≤ b → R a ⊆ R b := by
    intro a b hab x hx
    obtain ⟨s, hs, hpos⟩ := (hRmem a x).mp hx
    exact (hRmem b x).mpr ⟨s, hs.trans hab, hpos⟩
  have hstep : ∀ t, R (t + 1) = R t → R (t + 2) = R (t + 1) := by
    intro t hstable
    apply Finset.Subset.antisymm _ (hmono (Nat.le_succ _))
    intro x hx
    obtain ⟨s, hs, hpos⟩ := (hRmem (t + 2) x).mp hx
    rcases Nat.lt_or_ge s (t + 2) with hlt | hge
    · exact (hRmem (t + 1) x).mpr ⟨s, by omega, hpos⟩
    · have hs2 : s = t + 1 + 1 := by omega
      subst hs2
      rw [pow_succ, Matrix.mul_apply] at hpos
      obtain ⟨y, -, hy⟩ := (Finset.sum_pos_iff_of_nonneg
        (fun y _ => mul_nonneg (hP.pow_nonneg (t + 1) u y)
          (hP.nonneg y x))).mp hpos
      have hy1 : 0 < (P ^ (t + 1)) u y := by
        by_contra h
        have hzero : (P ^ (t + 1)) u y = 0 :=
          le_antisymm (not_lt.mp h) (hP.pow_nonneg (t + 1) u y)
        rw [hzero, zero_mul] at hy
        exact lt_irrefl _ hy
      have hy2 : 0 < P y x := by
        by_contra h
        have hzero : P y x = 0 :=
          le_antisymm (not_lt.mp h) (hP.nonneg y x)
        rw [hzero, mul_zero] at hy
        exact lt_irrefl _ hy
      have hyR : y ∈ R t := by
        rw [← hstable]
        exact (hRmem (t + 1) y).mpr ⟨t + 1, le_rfl, hy1⟩
      obtain ⟨s', hs', hpos'⟩ := (hRmem t y).mp hyR
      refine (hRmem (t + 1) x).mpr ⟨s' + 1, by omega, ?_⟩
      rw [pow_succ, Matrix.mul_apply]
      exact (Finset.sum_pos_iff_of_nonneg
        (fun z _ => mul_nonneg (hP.pow_nonneg s' u z)
          (hP.nonneg z x))).mpr
        ⟨y, Finset.mem_univ y, mul_pos hpos' hy2⟩
  have hstable : ∀ t, R (t + 1) = R t → ∀ s, R (t + s) = R t := by
    intro t ht s
    induction s with
    | zero => rfl
    | succ s ih =>
        have hnext : ∀ m, R (t + m + 1) = R (t + m) := by
          intro m
          induction m with
          | zero => exact ht
          | succ m ihm => exact hstep (t + m) ihm
        rw [← Nat.add_assoc, hnext s, ih]
  have hgrow : ∀ t, t + 1 ≤ (R t).card ∨ ∃ t' ≤ t, R (t' + 1) = R t' := by
    intro t
    induction t with
    | zero =>
        left
        have hu : u ∈ R 0 := (hRmem 0 u).mpr ⟨0, le_rfl, by simp⟩
        exact Finset.card_pos.mpr ⟨u, hu⟩
    | succ t ih =>
        rcases ih with hcard | ⟨t', ht', hst⟩
        · by_cases heq : R (t + 1) = R t
          · exact Or.inr ⟨t, Nat.le_succ t, heq⟩
          · left
            have hss : R t ⊂ R (t + 1) :=
              Finset.ssubset_iff_subset_ne.mpr
                ⟨hmono (Nat.le_succ t), fun h => heq h.symm⟩
            have := Finset.card_lt_card hss
            omega
        · exact Or.inr ⟨t', ht'.trans (Nat.le_succ t), hst⟩
  have hcardpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨u⟩
  have hmemv : v ∈ R (Fintype.card V - 1) := by
    rcases hgrow (Fintype.card V - 1) with hcard | ⟨t', ht', hst⟩
    · have hfull : R (Fintype.card V - 1) = Finset.univ := by
        apply Finset.eq_univ_of_card
        have hle := Finset.card_le_univ (R (Fintype.card V - 1))
        omega
      rw [hfull]
      exact Finset.mem_univ v
    · obtain ⟨s, hs⟩ := hirr u v
      have hvs : v ∈ R (t' + s) :=
        hmono (Nat.le_add_left s t') ((hRmem s v).mpr ⟨s, le_rfl, hs⟩)
      rw [hstable t' hst s] at hvs
      exact hmono ht' hvs
  obtain ⟨s, hs, hpos⟩ := (hRmem _ v).mp hmemv
  exact ⟨s, hs, hpos⟩

/-! ## The confined matrix -/

open Foundation

omit [DecidableEq V] in
theorem principal_isSubstochastic (hP : IsStochastic P) (U : Finset V) :
    IsSubstochastic (principal P U) where
  nonneg i j := hP.nonneg i j
  row_le i := by
    have hsub : ∑ j : U, P i j ≤ ∑ v, P i v := by
      rw [Finset.sum_coe_sort U (fun v => P i v)]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U)
        (fun v _ _ => hP.nonneg i v)
    simpa [Foundation.principal, hP.row_sum] using hsub

/-- Confined paths are paths: the powers of `P[U]` are dominated
entrywise by those of `P`. -/
theorem principal_pow_le (hP : IsStochastic P) (U : Finset V) (t : ℕ)
    (i j : U) : (principal P U ^ t) i j ≤ (P ^ t) i j := by
  induction t generalizing j with
  | zero =>
      simp only [pow_zero, Matrix.one_apply]
      by_cases hij : i = j
      · simp [hij]
      · have hne : (i : V) ≠ (j : V) := fun h => hij (Subtype.ext h)
        simp [hij, hne]
  | succ t ih =>
      simp only [pow_succ, Matrix.mul_apply]
      calc
        ∑ k : U, (principal P U ^ t) i k * principal P U k j
            ≤ ∑ k : U, (P ^ t) i k * P k j :=
          Finset.sum_le_sum fun k _ =>
            mul_le_mul_of_nonneg_right (ih k) (hP.nonneg k j)
        _ ≤ ∑ v, (P ^ t) i v * P v j := by
          rw [Finset.sum_coe_sort U (fun v => (P ^ t) i v * P v j)]
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.subset_univ U)
            (fun v _ _ => mul_nonneg (hP.pow_nonneg t i v)
              (hP.nonneg v j))

/-- The escape estimate: every row sum of `P[U]^{n-1}` is below one. -/
theorem rowSum_principal_lt_one (hP : IsStochastic P)
    (hirr : IsIrreducible P) (U : Finset V) (hU : U ≠ univ) (i : U) :
    rowSum (principal P U) (Fintype.card V - 1) i < 1 := by
  obtain ⟨y, hy⟩ : ∃ y : V, y ∉ U := by
    by_contra h
    exact hU (Finset.eq_univ_iff_forall.mpr fun x => by
      by_contra hx
      exact h ⟨x, hx⟩)
  obtain ⟨t, ht, hpos⟩ := hP.exists_pow_pos_le hirr (i : V) y
  have hsub := principal_isSubstochastic hP U
  calc
    rowSum (principal P U) (Fintype.card V - 1) i
        ≤ rowSum (principal P U) t i := hsub.rowSum_antitone i ht
    _ ≤ ∑ j : U, (P ^ t) i j :=
      Finset.sum_le_sum fun j _ => principal_pow_le hP U t i j
    _ = ∑ v ∈ U, (P ^ t) i v :=
      Finset.sum_coe_sort U (fun v => (P ^ t) i v)
    _ < ∑ v, (P ^ t) i v := by
      apply Finset.sum_lt_sum_of_subset (Finset.subset_univ U)
        (Finset.mem_univ y) hy hpos
      intro v _ _
      exact hP.pow_nonneg t i v
    _ = 1 := hP.pow_row_sum t i

/-- A common bound below one for the row sums of `P[U]^{n-1}`. -/
theorem exists_escape_bound (hP : IsStochastic P)
    (hirr : IsIrreducible P) (U : Finset V) (hU : U ≠ univ) :
    ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧
      ∀ i : U, rowSum (principal P U) (Fintype.card V - 1) i ≤ c := by
  classical
  rcases isEmpty_or_nonempty U with hempty | hne
  · exact ⟨0, le_rfl, zero_lt_one, fun i => (hempty.false i).elim⟩
  · obtain ⟨i₀, -, hmax⟩ := Finset.exists_max_image
      (Finset.univ : Finset U)
      (fun i => rowSum (principal P U) (Fintype.card V - 1) i)
      Finset.univ_nonempty
    exact ⟨rowSum (principal P U) (Fintype.card V - 1) i₀,
      (principal_isSubstochastic hP U).rowSum_nonneg _ i₀,
      rowSum_principal_lt_one hP hirr U hU i₀,
      fun i => hmax i (Finset.mem_univ i)⟩

omit [DecidableEq V] in
/-- A nonempty proper subset forces at least two states. -/
theorem card_sub_one_pos (U : Finset V) (hUne : U.Nonempty)
    (hU : U ≠ univ) : 0 < Fintype.card V - 1 := by
  have hlt : U.card < Fintype.card V := by
    rw [← Finset.card_univ]
    exact Finset.card_lt_card
      (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ U, hU⟩)
  have hpos : 0 < U.card := Finset.card_pos.mpr hUne
  omega

/-- Lemma `lem:confined`, the geometric estimate. -/
theorem confined_rowSum_decay (hP : IsStochastic P)
    (hirr : IsIrreducible P) (U : Finset V) (hU : U ≠ univ) :
    ∃ c : ℝ, 0 ≤ c ∧ c < 1 ∧ ∀ (m : ℕ) (i : U),
      rowSum (principal P U) (m * (Fintype.card V - 1)) i ≤ c ^ m := by
  obtain ⟨c, hc0, hc1, hc⟩ := exists_escape_bound hP hirr U hU
  exact ⟨c, hc0, hc1, fun m i =>
    (principal_isSubstochastic hP U).rowSum_mul_le hc m i⟩

/-- Lemma `lem:confined`, the positive minor. -/
theorem confined_det_pos (hP : IsStochastic P)
    (hirr : IsIrreducible P) (U : Finset V) (hUne : U.Nonempty)
    (hU : U ≠ univ) : 0 < (1 - principal P U).det := by
  obtain ⟨c, -, hc1, hc⟩ := exists_escape_bound hP hirr U hU
  exact (principal_isSubstochastic hP U).det_one_sub_pos
    (card_sub_one_pos U hUne hU) hc1 hc

/-- Lemma `lem:confined`, the Green series. -/
theorem confined_hasSum (hP : IsStochastic P)
    (hirr : IsIrreducible P) (U : Finset V) (hUne : U.Nonempty)
    (hU : U ≠ univ) (i j : U) :
    HasSum (fun t => (principal P U ^ t) i j)
      ((1 - principal P U)⁻¹ i j) := by
  obtain ⟨c, -, hc1, hc⟩ := exists_escape_bound hP hirr U hU
  exact (principal_isSubstochastic hP U).hasSum_pow_entry
    (card_sub_one_pos U hUne hU) hc1 hc i j

end EAB.Paper.Chain
