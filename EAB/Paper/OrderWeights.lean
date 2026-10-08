import EAB.Paper.GrowthOrders

/-!
# Order weights, order masses and the minor condition

The weight of a growth order is the product of harmonic readings of
Definition `def:orders` in the blueprint. The order mass at a root
sums the weights of the growth orders whose first vertex is a child
of that root. Peeling the first vertex factors the weight, which
gives the sum in equation `eq:induction-sum` before the inductive
hypothesis is applied.
-/

open Finset Matrix

namespace EAB.Paper

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {K : Type*} [Field K]

/-! ## Weights -/

/-- The weight `Π(τ) = ∏_{l=1}^{k-1} γ^{U_{l-1},τ_l}_{g(τ_{l+1})}` of
an order `τ` grown from the base `U`, with parents read from `g`.
The recursion peels the first vertex: the factor `l = 1` is
`γ^{U,τ_1}_{g(τ_2)}` and the remaining factors are those of
`(τ_2, …, τ_k)` grown from `U ∪ {τ_1}`. An order of length at most
one has the empty product `1`. -/
noncomputable def orderWeight (L : Matrix V V K) (g : V → V) :
    Finset V → List V → K
  | _, [] => 1
  | _, [_] => 1
  | U, z :: y :: rest =>
      Foundation.gamma L U z (g y) *
        orderWeight L g (insert z U) (y :: rest)

/-- Equation `eq:weight-peel`. -/
theorem orderWeight_cons_cons (L : Matrix V V K) (g : V → V)
    (U : Finset V) (z y : V) (rest : List V) :
    orderWeight L g U (z :: y :: rest) =
      Foundation.gamma L U z (g y) *
        orderWeight L g (insert z U) (y :: rest) :=
  rfl

/-- The weight reads the parent map only at the vertices of the
order. -/
theorem orderWeight_congr (L : Matrix V V K) (g g' : V → V) :
    ∀ (U : Finset V) (τ : List V), (∀ y ∈ τ, g y = g' y) →
      orderWeight L g U τ = orderWeight L g' U τ
  | _, [], _ => rfl
  | _, [_], _ => rfl
  | U, z :: y :: rest, h => by
      rw [orderWeight_cons_cons, orderWeight_cons_cons,
        h y (by simp),
        orderWeight_congr L g g' (insert z U) (y :: rest)
          (fun x hx => h x (List.mem_cons_of_mem z hx))]

/-! ## Order masses -/

/-- The parent of the first vertex of an order. -/
def firstParent (g : V → V) (τ : List V) : Option V :=
  τ.head?.map g

/-- The order mass `𝒢_i(B,f)`: the sum of the weights of the growth
orders whose first vertex is a child of the root `i`. -/
noncomputable def orderMass (L : Matrix V V K) (B : Finset V)
    (f : ParentAssignment B) (i : B) : K :=
  ∑ τ ∈ (growthOrders B f).filter
      (fun τ => firstParent (extendParents B f) τ = some (i : V)),
    orderWeight L (extendParents B f) B τ

/-- Group a sum over growth orders by the root that is the parent of
the first vertex. -/
theorem sum_growthOrders_by_firstParent (B : Finset V)
    (f : ParentAssignment B) (hB : B ≠ univ) (F : List V → K) :
    ∑ τ ∈ growthOrders B f, F τ =
      ∑ x : B, ∑ τ ∈ (growthOrders B f).filter
        (fun τ => firstParent (extendParents B f) τ = some (x : V)),
        F τ := by
  classical
  have hmaps : ∀ τ ∈ growthOrders B f,
      firstParent (extendParents B f) τ ∈
        (univ : Finset B).image (fun x : B => some (x : V)) := by
    intro τ hτ
    rw [mem_growthOrders_iff] at hτ
    cases τ with
    | nil => exact absurd rfl (hτ.ne_nil hB)
    | cons y rest =>
        exact Finset.mem_image.mpr
          ⟨⟨_, hτ.head_parent_mem⟩, Finset.mem_univ _, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps F, Finset.sum_image]
  intro x _ x' _ h
  exact Subtype.ext (Option.some.inj h)

/-- Group the growth orders that enter at the root `i` by their
first vertex, a child of `i`. -/
theorem orderMass_eq_sum_children (L : Matrix V V K) (B : Finset V)
    (f : ParentAssignment B) (i : B) :
    orderMass L B f i =
      ∑ w ∈ children B f i,
        ∑ τ ∈ (growthOrders B f).filter
          (fun τ => τ.head? = some (w : V)),
          orderWeight L (extendParents B f) B τ := by
  classical
  have hmaps : ∀ τ ∈ (growthOrders B f).filter
      (fun τ => firstParent (extendParents B f) τ = some (i : V)),
      τ.head? ∈ (children B f i).image
        (fun w : (univ \ B : Finset V) => some (w : V)) := by
    intro τ hτ
    obtain ⟨hGO, hfirst⟩ := Finset.mem_filter.mp hτ
    rw [mem_growthOrders_iff] at hGO
    cases τ with
    | nil => simp [firstParent] at hfirst
    | cons y rest =>
        have hy : y ∉ B := hGO.not_mem_roots (by simp)
        have hparent : extendParents B f y = (i : V) := by
          simpa [firstParent] using hfirst
        rw [extendParents_nonroot B f hy] at hparent
        exact Finset.mem_image.mpr
          ⟨⟨y, Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hy⟩⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hparent⟩, rfl⟩
  unfold orderMass
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro w hw
    have hchild : f w = (i : V) := (Finset.mem_filter.mp hw).2
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext τ
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hGO, _⟩, hhead⟩
      exact ⟨hGO, hhead⟩
    · rintro ⟨hGO, hhead⟩
      refine ⟨⟨hGO, ?_⟩, hhead⟩
      rw [firstParent, hhead, Option.map_some,
        extendParents_nonroot B f (nonroot_not_mem B w), hchild]
  · intro w _ w' _ h
    exact Subtype.ext (Option.some.inj h)

/-- The sum of equation `eq:induction-sum` for one child `w` of a
root, before the inductive hypothesis is applied. It uses the
peeling bijection and the factorization `eq:weight-peel`, and then
groups the shortened orders by the root at which they enter. -/
theorem sum_orders_with_head (L : Matrix V V K) (B : Finset V)
    (f : ParentAssignment B) (w : (univ \ B : Finset V))
    (hchild : f w ∈ B) (hk : 2 ≤ (univ \ B).card) :
    ∑ τ ∈ (growthOrders B f).filter
        (fun τ => τ.head? = some (w : V)),
        orderWeight L (extendParents B f) B τ =
      ∑ x : (insert (w : V) B : Finset V),
        Foundation.gamma L B (w : V) (x : V) *
          orderMass L (insert (w : V) B)
            (peelParents B f (w : V)) x := by
  classical
  have hw : (w : V) ∉ B := nonroot_not_mem B w
  have hchild' : extendParents B f (w : V) ∈ B := by
    rw [extendParents_nonroot B f hw]
    exact hchild
  have hB' : insert (w : V) B ≠ univ :=
    insert_ne_univ_of_two_le B (w : V) hw hk
  rw [growthOrders_filter_head B f (w : V) hw hchild',
    Finset.sum_image (fun _ _ _ _ h => List.cons_injective h),
    sum_growthOrders_by_firstParent (insert (w : V) B)
      (peelParents B f (w : V)) hB']
  apply Finset.sum_congr rfl
  intro x _
  unfold orderMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ' hτ'
  obtain ⟨hGO, hfirst⟩ := Finset.mem_filter.mp hτ'
  rw [mem_growthOrders_iff] at hGO
  cases τ' with
  | nil => simp [firstParent] at hfirst
  | cons y rest =>
      have hagree : ∀ z ∈ y :: rest,
          extendParents B f z =
            extendParents (insert (w : V) B)
              (peelParents B f (w : V)) z := by
        intro z hz
        exact (peelParents_agree_off_roots B f (w : V) z
          (hGO.not_mem_roots hz)).symm
      have hparent : extendParents (insert (w : V) B)
          (peelParents B f (w : V)) y = (x : V) := by
        simpa [firstParent] using hfirst
      rw [orderWeight_cons_cons, hagree y (by simp), hparent,
        orderWeight_congr L _ _ (insert (w : V) B) (y :: rest) hagree]

/-! ## The minor condition -/

/-- The hypothesis `eq:minor-hypothesis`: the principal minor of `L`
is nonzero on every base `U_l`, `0 ≤ l ≤ k - 1`, of every growth
order. -/
def MinorCondition (L : Matrix V V K) (B : Finset V)
    (f : ParentAssignment B) : Prop :=
  ∀ τ ∈ growthOrders B f, ∀ l < τ.length,
    (Foundation.principal L (orderBase B τ l)).det ≠ 0

/-- The minor condition at `l = 0`. -/
theorem MinorCondition.det_base {L : Matrix V V K} {B : Finset V}
    {f : ParentAssignment B} (h : MinorCondition L B f)
    (hpm : IsPaperParentMap B f) (hB : B ≠ univ) :
    (Foundation.principal L B).det ≠ 0 := by
  obtain ⟨τ, hτ⟩ := growthOrders_nonempty_of_proper B f hpm hB
  have hne : τ ≠ [] :=
    ((mem_growthOrders_iff B f τ).mp hτ).ne_nil hB
  have h0 := h τ hτ 0 (List.length_pos_iff.mpr hne)
  rwa [orderBase_zero] at h0

/-- Lemma `lem:orders`, the prefix bases: the minor condition passes
to the restricted map. -/
theorem MinorCondition.peel {L : Matrix V V K} {B : Finset V}
    {f : ParentAssignment B} (h : MinorCondition L B f)
    (w : (univ \ B : Finset V)) (hchild : f w ∈ B) :
    MinorCondition L (insert (w : V) B) (peelParents B f (w : V)) := by
  intro τ' hτ' l hl
  have hw : (w : V) ∉ B := nonroot_not_mem B w
  have hchild' : extendParents B f (w : V) ∈ B := by
    rw [extendParents_nonroot B f hw]
    exact hchild
  have hτ : (w : V) :: τ' ∈ growthOrders B f := by
    rw [mem_growthOrders_iff] at hτ' ⊢
    exact (isGrowthOrder_cons_iff B f (w : V) hw hchild' τ').mpr hτ'
  have hdet := h ((w : V) :: τ') hτ (l + 1) (by simpa using hl)
  rwa [orderBase_cons_succ] at hdet

end EAB.Paper
