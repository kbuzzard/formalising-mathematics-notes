import Mathlib.Tactic -- imports all the Lean tactics

open Function
open MonoidHom
open QuotientGroup

-- A very specific result we will need in theorem T1
-- Prove that if N is a normal subgroup of G and g * k⁻¹ ∈ N, then ∃ n ∈ N, k * n = g
lemma L1 {G : Type} [Group G] (N : Subgroup G) (hN : Subgroup.Normal N) (g k : G) :
    g * k⁻¹ ∈ N → (∃ n ∈ N, k * n = g) := by

  intro q1

  -- Getting k⁻¹ * g ∈ N from g * k⁻¹ ∈ N, because N is normal
  have q2 : k⁻¹ * g ∈ N := hN.mem_comm q1

  have q3 : ∃ n ∈ N, k⁻¹ * g = n := exists_eq_right'.mpr q2

  -- Just unpacking hypotheses with cases
  cases' q3 with n q4
  cases' q4 with q5 q6

  -- Trying to get g = k * n
  have q7 : k * (k⁻¹ * g) = k * n := by exact congrArg (HMul.hMul k) q6
  rw [← mul_assoc k k⁻¹ g, mul_inv_cancel, one_mul] at q7

  -- Using n and breaking into cases
  use n
  constructor
  · exact q5

  -- Silly step to get k * n = g from g = k * n
  exact q7.symm


-- Definition of injectivity
theorem injective_def (X Y : Type) (f : X → Y) : Injective f ↔ ∀ a b : X, f a = f b → a = b := by
  rfl
  done


-- Let φ : G → H be a group homomorphism, and N a normal subgroup of G such that N ≤ ker(φ)
-- Then 'QuotientGroup.lift N φ h' is the group homomorphism ψ : G/N → H, such that ψ ∘ η = φ,
-- where η : G → G/N is the natural serjection, given by 'quotient_group.mk' N', and
-- h is proof of '∀ x, x ∈ N → φ x = 1'

-- Here we consider the special case N = ker(φ)

-- Prove that ψ is injective
theorem T1 {G H : Type} [Group G] [Group H] (φ : G →* H) (h : ∀ x, x ∈ φ.ker → φ x = 1) :
    Injective (lift φ.ker φ h) := by

  rw [injective_def]

  intro a b h1

-- Using the fact that η is serjective
  have h2 : ∃ (g : G), mk' φ.ker g = a := by exact Quot.exists_rep a
  have h3 : ∃ (g : G), mk' φ.ker g = b := by exact Quot.exists_rep b

-- So now we have η(g) = a and η(k) = b
  cases' h2 with g h4
  cases' h3 with k h5

-- Substituting η(g) for a and η(k) for b, in h1
  rw [← h4] at h1
  rw [← h5] at h1

-- Using the fact that ψ ∘ η = φ to reduce h1 to the prop φ(g) = φ(k)
  have h6 : lift φ.ker φ h (QuotientGroup.mk' (φ.ker) g) = φ g := by rfl
  have h7 : lift φ.ker φ h (QuotientGroup.mk' (φ.ker) k) = φ k := by rfl
  rw [h6] at h1
  rw [h7] at h1

-- Bunch of steps to go from φ(g) = φ(k) to φ(g * k⁻¹) = 1
  have p1 : (φ g) * (φ k)⁻¹ = (φ k) * (φ k)⁻¹ := by exact congrFun (congrArg HMul.hMul h1) (φ k)⁻¹
  rw [mul_inv_cancel (φ k), ← φ.map_inv k, ← φ.map_mul g k⁻¹] at p1

-- Using lemma L1 to get p3 as '∃ n ∈ φ.ker, k * n = g'
  have p3 : ∃ n ∈ φ.ker, k * n = g :=
    L1 (ker φ) (normal_ker φ) g k (h (g * k⁻¹) (h (g * k⁻¹) (h (g * k⁻¹) (h (g * k⁻¹) p1))))

-- Using p3 to get η(k) = η(g)
-- Had to get p3 in a very specific format to use 'mk'_eq_mk'
  have p4 : QuotientGroup.mk' φ.ker k = QuotientGroup.mk' φ.ker g :=
    (mk'_eq_mk' (ker φ)).mpr p3

-- Substituting a for η(g) and b for η(k)
  rw [h5] at p4
  rw [h4] at p4

-- Silly step to get a = b from b = a
  exact p4.symm

  done


-- Prove that range(ψ) = range(φ)
theorem T2 {G H : Type} [Group G] [Group H] (φ : G →* H) (h : ∀ x, x ∈ φ.ker → φ x = 1) :
    (lift φ.ker φ h).range = φ.range := by

  -- range(ψ) = range(φ) ↔ range(ψ) ≤ range(φ) ∧ range(φ) ≤ range(ψ)
  -- We will break into two cases and prove them one at a time
  have t1 : (lift φ.ker φ h).range = φ.range ↔
      (lift φ.ker φ h).range ≤ φ.range ∧ φ.range ≤ (lift φ.ker φ h).range :=
    le_antisymm_iff
  rw [t1]
  constructor

  -- Showing range(ψ) ≤ range(φ)
  intro k t2
  have t3 : ∃ a : G⧸φ.ker, lift (ker φ) φ h a = k := by exact t2
  cases' t3 with a t4
  have t5 : ∃ (g : G), mk' φ.ker g = a := by exact Quot.exists_rep a
  cases' t5 with g t6
  rw [← t6] at t4
  have t7 : lift φ.ker φ h (QuotientGroup.mk' φ.ker g) = φ g := by rfl
  rw [t7] at t4
  have t8 : ∃ x : G, φ x = k := by exact Exists.intro g t4
  exact t8

  -- Showing range(φ) ≤ range(ψ)
  intro m r1
  have r2 : ∃ p : G, φ p = m := by exact r1
  cases' r2 with p r3
  have r4 : φ p = lift φ.ker φ h (QuotientGroup.mk' φ.ker p) := by rfl
  rw [r4] at r3
  have r5 : ∃ b : G⧸φ.ker, lift φ.ker φ h b = m := by exact exists_mk.mpr r1
  exact r5

  done


-- Now we are ready for the final theorem
-- Given Groups G and H, and group homomorphism φ : G → H
-- Show that there exists an injective group homomorphism ψ : G/ker(φ) → H, with range(ψ) = range(φ)
-- This is essentially the first isomorphism theorem for groups, stating that G/ker(φ) ≅ range(φ)

theorem T {G H : Type} [Group G] [Group H] (φ : G →* H) :
    ∃ ψ : G⧸φ.ker →* H, Injective ψ ∧ ψ.range = φ.range := by

  -- Prove the hypothesis we need to define the lift
  have h (x : G) (hx : x ∈ φ.ker) : φ x = 1 := hx

  use lift φ.ker φ h

  -- Split into two cases and use theorem T1 and T2
  constructor
  exact T1 φ h
  exact T2 φ h

  done
