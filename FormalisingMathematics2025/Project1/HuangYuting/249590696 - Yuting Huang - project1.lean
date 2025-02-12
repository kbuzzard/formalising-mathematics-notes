/-
This is the first project (coursework) for Formalising Mathematics.
My attempt is to prove the first part of Proposition 2.7.7 in Group Representation
Theory from the lecture note (by Travis Schedler), that is:
Let (V,ρ) be a represetnation of group G, then there is a bijection between
Hom(ℂ[G], V) and V.
-/

import Mathlib.RepresentationTheory.Basic
import Mathlib.Data.Complex.Basic

/-
The first part is to define what is a homomorphism of group representations.
-/

-- `k` is the field (in later proof we will use `ℂ`), `G` is the group
-- The vector space `V` and represetentation `ρ` forms (V,ρ)
-- The vector space `W` also has its corresponding representation `σ`, i.e. (W,σ)
variable {k : Type} [Field k] {G : Type} [Group G]
variable {V : Type} [AddCommGroup V] [Module k V]
variable {W : Type} [AddCommGroup W] [Module k W]
variable (ρ : Representation k G V) (σ : Representation k G W)

-- The following structure is provided in problem sheet 23-24
/--Homomorphism: A homomorphism of representations T: (V,ρ) → (W, σ) is a linear
map T: V → W such that T ∘ ρ(g) = σ(g) ∘ T for all g ∈ G.-/
@[ext]
structure RepMap (ρ : Representation k G V) (σ : Representation k G W) extends
    V →ₗ[k] W : Type where
  map_apply : ∀ (g : G) (v : V), toLinearMap (ρ g v) = σ g (toLinearMap v)

/--Two representations are equal iff their linear map is equal.-/
lemma RepMap.eq_iff (T S : RepMap ρ σ): T = S ↔ T.toLinearMap = S.toLinearMap := by
  rw [RepMap.ext_iff]
  simp

-- The following instance and theorem is to write `T x` instead of `T.toLinearMap x`
/--Show homomorphism is defined by its function-/
instance instFunLike (ρ : Representation k G V) (σ : Representation k G W) :
    FunLike (RepMap ρ σ) V W where
  coe T := T.toLinearMap
  coe_injective' := by
    simp [Function.Injective]
    intro T S hT_eq_S
    rw [RepMap.eq_iff]
    exact hT_eq_S

/--Write T.toLinearMap as T-/
@[simp]
lemma coe_repMap (ρ : Representation k G V) (σ : Representation k G W) (T : RepMap ρ σ) (x : V) :
    T.toLinearMap x = T x := rfl

-- In the following proof, we need `G` to be finite.
variable [Fintype G]
-- We first define ℂ[X], where `X` is a set, and `G` acts on `X` by left multiplicaiton.
variable (X: Type)
variable [MulAction G X]

/--Representation G → ℂ[X], where ℂ[X] = {∑_{x∈X} aₓx | aₓ ∈ ℂ} and G acts on ℂ[X] by
left multimplication-/
def rep_G_on_CX : Representation ℂ G (X → ℂ) where
  toFun := fun g => {
    toFun := fun a => a ∘ (fun x ↦ g⁻¹ • x)
    map_add' := by
      intro a b
      ext x
      dsimp
    map_smul' := by
      intro r a
      ext y
      simp
  }
  map_one' := by
    ext a
    simp
  map_mul' := by
    intro g h
    ext a x
    simp
    rw [mul_smul]

-- Now we use `ℂ` instead of `k` for the field
variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)

open BigOperators

/--A homomorphism ℂ[G] → V given by T(g) = ρ(g)v, where v ∈ V-/
def Hom_CG_V (v : V): RepMap (rep_G_on_CX G) ρ where
  toFun := fun a ↦ ∑ g : G, a g • (ρ g) v
  map_add' := by
    intro a b
    simp
    rw [← Finset.sum_add_distrib]
    congr! 1 with g
    exact add_smul (a g) (b g) ((ρ g) v)
  map_smul' := by
    intro r a
    simp
    rw [Finset.smul_sum]
    congr! 1 with g
    exact mul_smul r (a g) ((ρ g) v)
  map_apply := by
    intro g a
    simp
    apply Finset.sum_bij (fun h _ => g⁻¹ • h)
    · intro a _
      simp
    · intro x _ h _ h3
      have h4: g• (g⁻¹ • x) = g• (g⁻¹ • h):= by rw [h3]
      simp at h4
      exact h4
    · intro b _
      use g • b
      simp
    · intro x _
      have h1: rep_G_on_CX G g a x = a (g⁻¹ • x) := rfl
      rw [h1]
      have h2 : (ρ g) ((ρ (g⁻¹ • x)) v) = ((ρ g) * ρ (g⁻¹ • x)) v := by
        exact rfl
      rw [h2]
      have h3 : g⁻¹ • x = g⁻¹ * x := by simp
      rw [h3]
      rw [← MonoidHom.map_mul ρ g (g⁻¹ * x)]
      simp

open Classical

variable (v : V)

variable (g : G)

/--The simplification of T(g) = ρ(g)v, where T is the homomorphism ℂ[G] → V and T(e) = v-/
@[simp]
lemma Hom_singleton : (Hom_CG_V ρ v) (Pi.single g 1) = (ρ g) v := by
  rw [← coe_repMap]
  simp [Hom_CG_V]
  rw [Finset.sum_eq_single g]
  · simp
  · intro h h1 h2
    rw [Pi.single_eq_of_ne]
    rw [zero_smul]
    exact h2
  · intro h
    exfalso
    apply h
    exact Finset.mem_univ g

/--∃! homomorphism of representations ℂ[G] → V sending e ∈ G ⊆ ℂ[G] to v ∈ V-/
theorem exists_unique_hom_v : ∃! T : RepMap (rep_G_on_CX G) ρ, T (Pi.single 1 1) = v := by
  use Hom_CG_V ρ v
  constructor
  · simp
  · intro T hT
    simp [RepMap.eq_iff]
    -- real proof starts here
    let b : Basis G ℂ  _ := Pi.basisFun ℂ G
    apply b.ext
    intro g
    rw [Pi.basisFun_apply]
    simp
    show T (b g) = _
    have h1: b g = rep_G_on_CX G g (b 1) := by
      ext x
      simp [b, rep_G_on_CX ]
      rw [Pi.single_apply, Pi.single_apply, inv_mul_eq_one (G := G), eq_comm (α := G)]
    rw [h1, ← coe_repMap, T.map_apply]
    congr

-- Example: all of the homomorphisms ℂ[G] → v are of this form
lemma Hom_CG_V_inv (T : RepMap (rep_G_on_CX G) ρ) : ∃ (v : V), T = Hom_CG_V ρ v := by
  let v := T (Pi.single 1 1)
  use v
  apply (exists_unique_hom_v ρ v).unique
  · simp [v]
  · simp

/-- Bijection between Hom(ℂ[G],V) and V-/
noncomputable def bijection_CG_V : Equiv (RepMap (rep_G_on_CX G) ρ) V where
  toFun := fun T => T (Pi.single 1 1)
  invFun := fun v => Hom_CG_V ρ v
  left_inv := by
    intro T
    obtain ⟨v, hTv⟩ := Hom_CG_V_inv ρ T
    rw [hTv]
    simp
  right_inv := by
    intro v
    simp
