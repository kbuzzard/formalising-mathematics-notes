import Mathlib.Tactic
-- this import below is used to write coset, but is not needed anymore
-- import Mathlib.Algebra.Group.Pointwise.Set.Basic

namespace Project1
/-
This project tries to define what an orbit and stabilizer is in a group G,
and proves the orbit-stabilizer theorem.
Note that MulAction is from the lean library.
-/

--define an orbit of an element x ∈ X in a group G
def Orbit (G : Type) [Group G] {X : Type} [MulAction G X] (x : X) :
  Set X := {x' : X | ∃ g : G, g • x = x'}

lemma orb_def (G : Type) [Group G] {X : Type} [MulAction G X] (x x' : X) :
    x' ∈ Orbit G x ↔ ∃ g : G, g • x = x' := by
  rfl

--A legacy for proving that the cardinality of X is the sum of all index of stablizer

--show that orbit of x always have x in its orbit
lemma id_orb_mem (G : Type) [Group G] {X : Type} [MulAction G X] (x : X) :
    x ∈ Orbit G x := by
  rw [orb_def]
  use 1
  exact MulAction.one_smul x

--This lemma shows that two orbits of x₁ and x₂ are equal iff one element is in other one's orbit
lemma orb_iff_same_orb (G : Type) [Group G] {X : Type} [Fintype X] [MulAction G X] (x1 x2 : X) :
    Orbit G x1 = Orbit G x2 ↔ x2 ∈ Orbit G x1 := by
  rw [orb_def]
  constructor
  · intro h
    rw [← orb_def, h]
    exact (id_orb_mem G x2)
  · intro h
    cases' h with g hg
    ext x
    rw [orb_def, orb_def]
    constructor
    · intro h1
      cases' h1 with g1 hg1
      use g1 * g⁻¹
      rw [← hg, ← mul_smul, inv_mul_cancel_right]
      exact hg1
    · intro h2
      cases' h2 with g2 hg2
      use g2 * g
      rw [mul_smul, hg]
      exact hg2

/-This lemma prepares to prove orbit create a partition for X, and by
making use of orb_iff_same_orb and id_orb_mem, the lemma is easy to prove-/
lemma orb_intersect_iff_same_orb
    (G : Type) [Group G] {X : Type} [Fintype X] [MulAction G X] (x1 x2 : X) :
    (∃ x: X, x ∈ (Orbit G x1) ∩ (Orbit G x2)) ↔ Orbit G x1 = Orbit G x2 := by
  rw [orb_iff_same_orb]
  constructor
  · intro hinter
    obtain ⟨x, ⟨hx1, hx2⟩⟩ := hinter
    apply (orb_iff_same_orb G x1 x2).mp
    apply (orb_iff_same_orb G x1 x).mpr at hx1
    apply (orb_iff_same_orb G x2 x).mpr at hx2
    rw[hx1, hx2]
  · intro hx1
    use x2
    exact Set.mem_inter hx1 (id_orb_mem G x2)

-- opening Classical makes it convenient to prove things relating to Fintype
open Classical

-- defining stabilizer and proving that stabilizer is a subgroup
def Stabilizer (G : Type) [Group G] {X : Type} [Fintype X] [MulAction G X] (x : X) :
    Subgroup G where
  -- the definition of Stabilizer of x is the subgroup of all element of g fixes x
  carrier := {g : G | g • x = x}
  one_mem' := by
    --show that 1 ∈ G is in the Stabilizer since 1 • x = x by property of an action.
    rw [@Set.mem_setOf]
    exact MulAction.one_smul x
  inv_mem' := by
    --show that g⁻¹ ∈ G is in the Stabilizer since x = 1 • x = g⁻¹ • (g • x) = g⁻¹ • x
    intro g'
    rw [@Set.mem_setOf]
    intro h
    rw [@Set.mem_setOf]
    have h1 : (g'⁻¹ * g') • x = g'⁻¹ • x := by
      rw [mul_smul, h]
    rw [inv_mul_cancel g', one_smul] at h1
    exact Eq.symm h1
  mul_mem' := by
    --again by property of action
    dsimp
    intro a b ha hb
    rw [mul_smul, hb, ha]

-- add the definition of the carrier of stabilizer to simp
@[simp]
lemma stab_def (G : Type) [Group G] {X : Type} [Fintype X] [MulAction G X] (x : X) (g : G):
    g ∈ Stabilizer G x ↔ g • x = x := by
  rfl

open scoped Pointwise
-- Lots of "noncomputable" def whenever there is a "Fintype" used

-- Kevin wrote this
noncomputable def osqe_toFun
    (G : Type) [Group G] {X : Type} [Fintype X] [MulAction G X] (x : X) :
    /- y.2 is the proof of y.1 being a member of orbit, and .choose is using
    the axiom of choice to pick the element g ∈ G so that g • x = x-/
    Orbit G x → G := fun y ↦ y.2.choose

-- Kevin proved this
theorem osqe_toFun_spec (G : Type) [Group G] {X : Type} [Fintype X]
    [MulAction G X] (x : X) (y : Orbit G x)  : (osqe_toFun G x y) • x = y :=
  -- .choose_spec gives a proof that the chosen element indeed satisfy the condition
  y.2.choose_spec

noncomputable def osqe_invFun
    (G : Type) [Group G] {X : Type} [Fintype X] [MulAction G X] (x : X) :
    G⧸(Stabilizer G x) → Orbit G x :=
  -- similar to y.2, ⟨g, rfl⟩ is a proof for g • x to be an Orbit of x
  Quotient.lift (fun g ↦ ⟨g • x, ⟨g, rfl⟩⟩) <| by
  intro g₁ g₂ h
  -- property of (cosets?) : aH = bH ↔ a⁻¹ * b  ∈ H ≤ G
  apply QuotientGroup.leftRel_apply.mp at h
  simp
  simp at h
  rw[@mul_smul, @inv_smul_eq_iff] at h
  exact id (Eq.symm h)

/- We need osqe_invFun_spec (as well as the osqe_toFun_spec above) so that we may "extract"
some of the property of the function we constructed that is "hidden" inside the definitions-/
theorem osqe_invFun_spec (G : Type) [Group G] {X : Type} [Fintype X] [MulAction G X] (x : X)
    (g : G) : osqe_invFun G x g = ⟨g • x, g, rfl⟩ := by
  rfl

/-lean4 is smart enough to consider element g of group G
as an element ("gH") of G/H (by trivial homomorphism)-/
variable (G : Type) [Group G] {X : Type} [Fintype X] [MulAction G X] (x : X) in
example (g : G) : G ⧸ (Stabilizer G x) := g

/- defines an Equiv relation between Orbit G x and G⧸(Stabilizer G x), and to do that,
we need to find a function f with a two-sided inverse function (so basically a bijection)-/
noncomputable def orbit_stabilizer_quot_equiv
    (G : Type) [Group G] {X : Type} [Fintype X] [MulAction G X] (x : X) :
    (Orbit G x ≃ G⧸(Stabilizer G x)) where
  toFun y := osqe_toFun G x y
  invFun := osqe_invFun G x
  left_inv := by
    intro y
    simp
    rw [osqe_invFun_spec]
    ext
    dsimp
    rw [osqe_toFun_spec]
  right_inv q := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    simp
    rw [@QuotientGroup.eq]
    simp
    rw [@mul_smul]
    rw [osqe_invFun_spec]
    rw [@inv_smul_eq_iff]
    rw [osqe_toFun_spec]

/- Finally, by proving that G⧸(Stabilizer G x) is indeed finite, and that equiv relation implies
the same cardinality, we can prove the orbit-stabilizer theorem:
|O(x)| = [G : Stab(x)]-/
theorem orbit_Stabilizer (G : Type) [Group G] {X : Type} [Fintype X] [MulAction G X] (x : X) :
    Fintype.card (Orbit G x) = (Stabilizer G x).index := by
  have h : (Fintype (G⧸(Stabilizer G x) )) := by
    exact Fintype.ofEquiv (Orbit G x) (orbit_stabilizer_quot_equiv G x)
  rw[Fintype.card_congr (orbit_stabilizer_quot_equiv G x)]
  rw[Fintype.card_eq_nat_card]
  rfl
