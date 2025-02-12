
import Mathlib.Tactic -- imports all the tactics

/-!
# Group Homomorphisms

This file defines the notion of Group, Subgroup and Group Homomorphism.

Instead of using the predefined Group structure in Lean, I defined the class `MyGroup`
and from this class I defined `MySubgroup` and `myHomorphism` that satisfy the
usual conditions subgroups and group homomorphisms satisfy.

This file can be divided in the initial definitions with some usefull lemmas and the proof
of 6 basic theorems about group homomorphisms. For the proof of some the theorems
extra lemmas and definitions are introduced to shorten the proof.

## Theorems

- Let `φ : G → H` be an homomorphism then `φ 1 = 1`.
- Let `φ : G → H` be an homomorphism then `∀ g ∈ G , φ g⁻¹ = (φ g)⁻¹`.
- Let `φ : G → H` be an homomorphism then then image of `φ` is a subgroup of `H`.
- Let `φ : G → H` be an homomorphism then then kernel of `φ` is a subgroup of `G`.
- Let `φ : G → H` be an homomorphism then `kernel φ = {1}` ↔ `φ` injective`
- Let `φ : G → H` and `ψ: H → K` be homomorphisms then `ψ ∘ φ: G → K` is an homorphism.

-/

set_option autoImplicit true

/-!
Definition of a group. In Lean, a group is a Type, with the 5
standard axioms.

· `∀ a b c ∈ G, a * b * c = a * (b * c)`
· `∀ a ∈ G, 1 * a = a`
· `∀ a ∈ G, a * 1 = a`
· `∀ a ∈ G, a⁻¹ * a = 1`
· `∀ a ∈ G, a * a⁻¹ = 1`

-/
class MyGroup (G : Type) extends One G, Mul G, Inv G : Type where
  mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)
  one_mul : ∀ a : G, 1 * a = a
  mul_one : ∀ a : G, a * 1 = a
  inv_mul_self : ∀ a : G, a⁻¹ * a = 1
  mul_inv_self : ∀ a : G, a * a⁻¹ = 1

namespace MyGroup

-- Usefull lemma I will use
lemma mul_left_cancel [MyGroup G] {a b c : G} (h : a * b = a * c) : b = c := by
  have h3 : a⁻¹ * a * b = a⁻¹ * a * c := by
    /-
     a⁻¹ * a * b = a⁻¹ * a * c   ←   a⁻¹ * (a * b) = a⁻¹ * (a * c)
     ← a⁻¹ * (a * c) = a⁻¹ * (a * c)   ←   a⁻¹ * a * c = a⁻¹ * a * c
     ←  1 * c = 1 * c   ←   c = c
    -/
    rw[mul_assoc, h, ← mul_assoc, inv_mul_self, one_mul]

  -- a⁻¹ * a * b = a⁻¹ * a * c   →   1 * b = 1 * c   →   b = c
  rw[inv_mul_self a, one_mul, one_mul] at h3
  exact h3
/-!
Definition of subgroup

A subgroup `S` is a subset of `G` that satisfies the subgroup test:
· `∀ a b ∈ S → a * b ∈ S`
· `1 ∈ S`
· `∀ a ∈ S → a⁻¹ ∈ S`
-/
def MySubgroup [MyGroup G] (S : Set G) : Prop :=
  (∀ a b, a ∈ S ∧ b ∈  S → a * b ∈ S) ∧ ((1 : G) ∈ S) ∧ (∀ a, a ∈ S → a⁻¹ ∈ S)

-- Subgroup definition
lemma subgroup_def [MyGroup G] (S: Set G) :
    MySubgroup S ↔ ((∀ a b, a ∈ S ∧  b ∈  S → a * b ∈ S) ∧ ((1 : G) ∈ S) ∧ (∀ a, a ∈ S → a⁻¹ ∈ S)) := by
  rfl

-- Define the trivial subgroup = {1}
def trivialSubgroup (G : Type) [MyGroup G] : Set G := {1}

-- Prove that if g ∈ trivialSubgroup ↔ g = 1
lemma trivial_one_mem (G : Type) [MyGroup G] (g : G) : g ∈ trivialSubgroup G ↔ g = 1 := by
  -- Divide the goal in double implication
  apply Set.mem_singleton_iff

-- Prove that the trivial subgroup is actually a subgroup
lemma trivial_is_subgroup (G : Type) [MyGroup G] : MySubgroup (trivialSubgroup G) := by
  rw[subgroup_def]
  constructor
  · -- Proof: a ∈ trivialSubgroup ∧ b ∈ trivialSubgroup → a * b ∈ trivialSubgroup
    intro a b hab
    cases' hab with ha hb
    -- If a ∈ trivialSubgroup and b ∈ trivialSubgroup → a * b ∈ trivialSubgroup
    rw[trivial_one_mem] at ha hb
    -- a = 1 and b = 1
    rw[ha,hb]
    -- a * b = 1 * 1 = 1 → 1 ∈ {1}
    rw[one_mul, trivialSubgroup, @Set.mem_singleton_iff]

  · constructor
    · -- Proof: 1 ∈ trivialSubgroup
      rw[trivialSubgroup, @Set.mem_singleton_iff]

    · -- Proof: a ∈ trivialSubgroup → a⁻¹ ∈ trivialSubgroup
      intro a ha
      -- a ∈ trivialSubgroup → a = 1
      rw[trivial_one_mem] at ha
      -- a⁻¹ ∈ trivialSubgroup ← 1⁻¹ ∈ subgroup ← 1⁻¹ = 1
      rw[ha, trivialSubgroup, @Set.mem_singleton_iff]
      -- 1⁻¹ = 1 ← 1⁻¹ = 1⁻¹ * 1 ← 1⁻¹ = 1⁻¹
      nth_rw 2 [← inv_mul_self 1]
      nth_rw 1 [← mul_one 1⁻¹]


/-!
Definition of a group homomorphism

A group homomorphism is a function between groups `φ : G → H` that satisfies:
· `∀ a b : G,   φ (a * b) = φ a * φ b`
-/
def MyHomomorphism [MyGroup G] [MyGroup H] (φ: G → H) : Prop :=
  ∀ a b : G,   φ (a * b) = φ a * φ b

-- Homomorphism definition
lemma homomorphism_def [MyGroup G] [MyGroup H] (φ: G → H) : MyHomomorphism φ ↔ ∀ a b : G,   φ (a * b) = φ a * φ b := by
  rfl

/-!
(1) First result:
    Let `φ: G → H` be an homomorphism then `φ(1) = 1`.
-/
theorem homo_img_one [MyGroup G] [MyGroup H] (φ : G → H) (h_homo : MyHomomorphism φ) : φ 1 = 1 := by
  -- From φ being an homomprohism get the definition
  rw [homomorphism_def] at h_homo
  -- φ (1 * 1) = φ 1 * φ 1
  specialize h_homo 1 1
  apply mul_left_cancel (a := φ 1)

  --  φ 1 = φ 1 ← φ 1 = φ 1 * 1 ← φ (1 * 1) = φ 1 * 1
  --  ←  φ 1 * φ 1 = φ 1 * 1  ←  φ 1 = 1
  rw [mul_one (φ 1),← h_homo, mul_one  1]

/-!
  Second proof of the first result to show the difference between forward and backward reasoning.
  This proof was my first correct proof of this result and I found difficult to change my thinking
  into proving results by backward reasoning, which as Kevin Buzzard recomended me is better for
  Lean proofs.
-/
theorem homo_img_one_2 [MyGroup G] [MyGroup H] (φ : G → H) (h_homo : MyHomomorphism φ) : φ 1 = 1 := by
  -- From φ being an homomprohism get the definition
  rw [homomorphism_def] at h_homo

  -- Start with a true statement
  have h : φ 1 = φ 1 := by
    rfl

  -- Use rewirte to modify the hypothesis h
  -- φ 1 = φ 1 → φ (1 * 1) = φ 1 * 1
  nth_rw 2 [← mul_one (φ 1)] at h
  nth_rw 1 [← mul_one 1] at h
  -- → φ 1 * φ 1 = φ 1 * 1
  rw[h_homo 1 1] at h
  -- → φ 1 = 1
  apply mul_left_cancel at h
  exact h


/-!
(2) Second result:
    Let `φ: G → H` be an homomorphism then `∀ g ∈ G , φ g⁻¹ = (φ g)⁻¹`.
-/
theorem homo_img_inv [MyGroup G] [MyGroup H] (φ : G → H) (h_homo : MyHomomorphism φ) (g : G) : (φ g)⁻¹ =  φ g⁻¹ := by
  -- Get the definition of homomorphism

  apply mul_left_cancel (a := (φ g))
  --  φ g * (φ g)⁻¹ = φ g * φ g⁻¹ → 1 = φ g * φ g⁻¹ → 1 = φ (g * g⁻¹) = φ 1 → 1 = 1
  rw[← h_homo g g⁻¹, mul_inv_self, mul_inv_self, homo_img_one φ h_homo]

/-!
Define the image of a function `φ : G → H`.
The image of `φ` is the set of elements h of H such that `∃ g ∈ G, φ g = h`
-/
def image [MyGroup G] [MyGroup H] (φ : G →  H) : Set H := {φ g | g : G}

/-!
(3) Third result:
    Let `φ : G → H` be an homomorphism then then image of `φ` is a subgroup of `H`.
-/
theorem img_subgroup [MyGroup G][MyGroup H] (φ : G → H) (h_homo : MyHomomorphism φ) :  (MySubgroup (image φ )) := by
  -- Definition of subgroup
  rw[subgroup_def]
  -- Divide the proof in proving the three conditions for a set to being a subgroup
  constructor
  -- Proof : ∀ (a b : H), a ∈ image φ ∧ b ∈ image φ → a * b ∈ image φ
  · intro a b hab
    cases' hab with ha hb
    rw[image, @Set.mem_setOf ] at *
    -- Get the preimage of a and b ,ga and gb respectively
    cases' ha with ga h_ga
    cases' hb with gb h_gb
    -- Use φ gb = b and φ ga = a at the goal to deduce φ (ga * gb) = a * b
    rw[← h_gb, ← h_ga,← h_homo ga gb]
    use (ga * gb)

  · constructor
    -- Proof: 1 ∈ image φ
    · rw[image, @Set.mem_setOf]
      -- Use φ 1 = 1
      use 1
      rw[homo_img_one φ h_homo]

    -- Proof: ∀ a ∈ image φ, a⁻¹ ∈ image φ
    · intro a ha
      rw[image, @Set.mem_setOf] at *
      -- Let g ∈ G such that φ g = a
      cases' ha with g hg
      -- if φ g = a → φ g⁻¹ = a⁻¹
      use g⁻¹
      rw[← homo_img_inv φ h_homo g, hg]

/-!
Define the kernel of a function `φ : G → H`.
The kernel of `φ` is the set of elements g of G such that φ g = 1
-/
def kernel [MyGroup G] [MyGroup H] (φ : G →  H) : Set G :=
  φ⁻¹'(trivialSubgroup H)

/-
  Proof of `g ∈ ker φ ↔ φ g = 1`
-/
lemma ker_mem_iff_img_one [MyGroup G][MyGroup H](φ : G → H) (g : G) : (g ∈ kernel φ  ↔ φ g = 1 ):= by rfl

/-!
(4) Forth result:
    Let `φ : G → H` be an homomorphism then then kernel of `φ` is a subgroup of `G`.
-/
theorem ker_subgroup [MyGroup G][MyGroup H] (φ : G → H) (h_homo : MyHomomorphism φ) : (MySubgroup (kernel φ)) := by
  rw[subgroup_def]
  -- Divide the proof in proving the three conditions for a set to being a subgroup
  constructor
  -- Proof : ∀ (a b : H), a ∈ ker φ ∧ b ∈ ker φ → a * b ∈ ker φ
  · intro a b hab
    cases' hab with ha hb
    rw[ker_mem_iff_img_one] at *
    -- φ a = 1 and φ b = 1
    -- 1 = φ a * φ b = φ (a * b) = 1 → a * b ∈ ker φ
    rw[h_homo a b, ha , hb, one_mul]

  · constructor
    -- Proof: 1 ∈ ker φ
    · -- Use φ 1 = 1
      rw[ker_mem_iff_img_one, homo_img_one φ h_homo]

    -- Proof: ∀ a ∈ kernel φ, a⁻¹ ∈ kernel φ
    · intro a ha
      rw[ker_mem_iff_img_one] at *
      -- if φ a = 1 then φ a⁻¹ = (φ a)⁻¹ = 1⁻¹ = 1
      rw[← inv_mul_self (φ a), ← mul_one (φ a⁻¹), homo_img_inv φ h_homo a, ha]


-- Definition of injectivity from the notes Section03functionsSheet2
lemma injective_def (f : X → Y) : Function.Injective f ↔ ∀ a b : X, f a = f b → a = b := by
  rfl

/-!
(5) Fifth result:
    Let `φ : G → H` be an homomorphism then `kernel φ = {1}` ↔ `φ` injective`
-/
theorem injectivite_iff_ker_one [MyGroup G][MyGroup H] (φ : G → H) (h_homo : MyHomomorphism φ) :  Function.Injective φ ↔ kernel φ = trivialSubgroup G := by
  -- Divide the ↔ into → and ←
  constructor
  -- Proof: Injectivity → ker φ = {1}
  · intro h_inj
    -- Rewrite de definition of injectivity and the trivialSubgroup
    rw[injective_def] at h_inj
    rw[trivialSubgroup, @Set.eq_singleton_iff_unique_mem]

    -- to prove that ker φ = {1} we prove 1 ∈ ker φ ∧ ( x ∈ ker φ → x = 1 )
    constructor
    --Proof: 1 ∈ ker φ
    · -- Using φ 1 = 1
      rw[ker_mem_iff_img_one,homo_img_one φ h_homo]

    -- Proof: x ∈ ker φ → x = 1
    · -- Using φ 1 = 1
      intro x hx
      -- Using x ∈ ker φ → φ x = 1
      rw[h_inj x 1]
      -- x = 1 ← φ x = φ 1 ← φ x = 1 ← x ∈ ker φ
      rw[homo_img_one φ h_homo ,← ker_mem_iff_img_one]
      exact hx

  -- Proof ker φ = {1} → Injectivity
  · intro h_ker
    -- Rewirte the injectivity definition
    rw[injective_def]
    intro a b h_img
    -- Rewrite ker φ = {1} to 1 ∈ ker φ ∧ ( x ∈ ker φ → x = 1 )
    rw[trivialSubgroup,@Set.eq_singleton_iff_unique_mem] at h_ker
    cases' h_ker with h1 h_only_1
    -- a = b ← b⁻¹ * a = 1 ← b⁻¹ * a ∈ kernel φ
    apply mul_left_cancel (a := b⁻¹)
    rw[inv_mul_self]
    apply h_only_1 (b⁻¹ * a)
    -- b⁻¹ * a ∈ kernel φ ← φ (b⁻¹ * a) = 1 ← φ b⁻¹ * φ a = (φ b)⁻¹ * φ b ← φ b⁻¹ * φ b = φ b ⁻¹ * φ b
    rw[ker_mem_iff_img_one, h_homo b⁻¹ a, ← inv_mul_self (φ b), homo_img_inv φ h_homo, h_img]



-- Definition of composition evaluation from the notes Section03functionsSheet2
theorem comp_eval (f : X → Y) (g : Y → Z) (x : X) : (g ∘ f) x = g (f x) := by
  rfl
/-!
(6) Sixth result:
    Let `φ : G → H` and `ψ: H → K` be homomorphisms then `ψ ∘ φ: G → K` is an homorphism.
-/
theorem homo_composition [MyGroup G][MyGroup H][MyGroup K] (φ : G → H) (ψ : H → K) (h_phi : MyHomomorphism φ) (h_psi : MyHomomorphism ψ) :  MyHomomorphism (ψ ∘ φ) := by
  -- As φ and ψ are homomorphisms rewrite the definition also at the goal
  rw[homomorphism_def] at *
  -- Take a and b arbitrary
  intro a b
  -- Use that φ and ψ are homomorphism on a b and φ a and φ b, respectively
  specialize h_phi a b
  specialize h_psi (φ a) (φ b)
  -- Use composition evaluation and the hypothesis on φ and ψ to conclude
  rw[comp_eval] at *
  rw[h_phi, h_psi,comp_eval, comp_eval]


end MyGroup
