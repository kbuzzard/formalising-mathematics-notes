import Mathlib.Order.CompleteLattice

-- Knaster-Tarski Theorem
-- We prove that the set of fixed points of a monotone function on a complete lattice is a complete lattice

set_option autoImplicit true

-- f is a monotone function
def monotone {α : Type*} [Preorder α] [Preorder β] (f : α → β) : Prop :=
  ∀ ⦃a b : α⦄, a ≤ b → f a ≤ f b

variable [CompleteLattice α] (f : α → α) (hf : monotone f)

-- meet of pre-fixed points is a pre-fixed point
lemma sInf_pre_fixed (f : α → α) (hf : monotone f) (X : Set α) (pre_fixed: X ⊆ {x | f x ≤ x}) :
    f (sInf X) ≤ sInf X := by
  simp only [le_sInf_iff]
  -- (f (sInf X)) is the lower bound of X (proof below)
  -- Therefore it's lesser than the greatest lower bound, sInf X
  intro x x_in_X
  calc
    f (sInf X) ≤ f x := hf (sInf_le x_in_X)
    _ ≤ x := pre_fixed x_in_X

-- define the join operator of a set of fixed points
-- note that we don't yet show that this join is the least upper bound,
-- just that it belongs to the set of fixed points
def HasSupSet [CompleteLattice α] (f : α → α) (hf : monotone f) :
    SupSet { x : α // f x = x } where
      sSup X :=
        -- cast the set of fixed points to a set of elements of α
        let X' : Set α := {↑x | x ∈ X}
        -- BM: while lean can figure out what the type of X' is, it's nice to add this for
        -- readability
        -- and state each element in `X'` is a fixed point
        have x_fixed_point: ∀ x ∈ X', f x = x := by simp +contextual [X']
        -- set of all upper bounds of `X`, which are also pre-fixed points
        let Y : Set α := {y : α | f y ≤ y ∧ y ∈ upperBounds X'}
        let z : α := sInf Y -- the supposed join of `X`
        have : Y ⊆ {x | f x ≤ x} := by aesop
        -- infernce that `Y` contains only pre-fixed points is not automatic
        -- since there's a conjunct in the def of `Y`
        have pre_fixed : f (sInf Y) ≤ sInf Y := (@sInf_pre_fixed _ _ f hf Y this)
        -- BM: you had an @ here, that's a pretty clear sign that `pre_fixed` should have been
        -- explicit!
        -- for now we only need to show that `z` is a fixed point
        -- (ie, element of `{ x: α // f x = x }`)
        let z_fixed : f z = z := by
          apply le_antisymm
          · exact pre_fixed
          · -- prove that `z` is a post fixed point as well
            -- we try to show that `f z` is in `Y`

            -- this holds because every `x` is a lower bound and `z` is the greatest lower bound
            have z_upper_bound_X : z ∈ upperBounds X' := by
              intro x x_in_X
              have x_lower_bound_Y : x ∈ lowerBounds Y := by
                simp only [lowerBounds, Set.mem_setOf_eq]
                intro a ha
                exact ha.2 x_in_X
                -- BM: I unfolded the aesop here, it turns out it's doing way more than necessary

              rw [le_sInf_iff]
              exact x_lower_bound_Y -- in fact x_lower_bound_Y might not even be needed!
            -- this proof is more interesting using monotonicity of the function
            -- Lean encourages working backward from the goal making this proof easier
            have fz_upper_Bound_X : f z ∈ upperBounds X' := by
              intro x x_in_X
              rw [← x_fixed_point x x_in_X] -- key step is noticing that x = fx
              exact hf (z_upper_bound_X x_in_X)

            -- if `f z` is in `Y`, then its greater than `z` the meet of `Y`
            have hzY : f z ∈ Y := ⟨hf pre_fixed, fz_upper_Bound_X⟩
            exact sInf_le hzY
        ⟨z, z_fixed⟩ -- construct the subtype element

-- BM: I stopped here

-- showing that the join operator defined above actually gives the least upper bound
def fixed_point [CompleteLattice α] (f: α → α) (hf: monotone f) :
    CompleteLattice { x : α // f x = x } :=
  completeLatticeOfSup _ (H2 := HasSupSet f hf) (fun X ↦ by
    rw [IsLUB, IsLeast]
    constructor
    · -- show that `sSup X` is an upper bound
      simp [upperBounds]
      intro x ha hX
      change x ≤ sInf _
      apply le_sInf
      aesop
    · -- and that `sSup X` is the least upper bound
      simp [lowerBounds]
      let X': Set α := {↑x| x ∈ X}
      intro UB hUB x
      have : UB ∈ upperBounds X' := by
        rw [upperBounds] at x ⊢
        simp at x ⊢
        aesop
      change sInf {y | f y ≤ y ∧ y ∈ upperBounds X'} ≤ UB
      apply sInf_le
      aesop
  )


-- The latter part of Knaster-Tarski
-- Now we provide a way of constructing the least fixed point as the meet of pre-fixed points
-- we have shown previously that the least fixed point exists as the fixed points form a complete lattice
theorem least_fixed_point {hf: monotone f}: IsLeast {x | f x = x} (sInf {px | f px ≤ px}) := by
  -- meet of pre-fixed points `z`
  let z := sInf {px | f px ≤ px}
  -- we use that the least fixed point in both cases of proof `z_fixed` below
  have z_pre_fixed: f z ≤ z := by
      apply sInf_pre_fixed f hf {px | f px ≤ px}
      simp
  -- rw [z]
  constructor
  · -- prove that `z` is a fixed point
    apply le_antisymm
    · exact z_pre_fixed
    · -- prove that `z` is a post fixed point
      have fz_pre_fixed: f z ∈ {px | f px ≤ px} := hf z_pre_fixed
      -- since `f z` is also a pre-fixed point, `z` as a lower bound of that Set is lesser than it
      apply sInf_le
      exact fz_pre_fixed
  · -- then we know that `z` is lesser than all fix points (as fix points are also pre-fixed points)
    simp [lowerBounds, sInf]
    intro x hx
    apply sInf_le
    simp [hx]

-- I have not provided the dual proofs for constructing the greatest fixed point
-- This involves join of post-fixed point lemma dual to the above meet of pre-fixed points lemma
