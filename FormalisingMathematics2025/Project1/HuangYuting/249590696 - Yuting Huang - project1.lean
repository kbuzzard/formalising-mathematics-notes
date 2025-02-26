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
@[simps]
def rep_G_on_CX : Representation ℂ G (X → ℂ) where
  toFun g := {
    toFun a x := a (g⁻¹ • x)
    map_add' a b := rfl
    map_smul' r a := rfl
  }
  map_one' := by
    ext a
    simp
  map_mul' g h := by
    ext a x
    simp [mul_smul]

-- Now we use `ℂ` instead of `k` for the field
variable {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)

open BigOperators

/--A homomorphism ℂ[G] → V given by T(g) = ρ(g)v, where v ∈ V-/
def Hom_CG_V (v : V): RepMap (rep_G_on_CX G) ρ where
  toFun a := ∑ g : G, a g • ρ g v
  map_add' a b := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' r a := by simp [Finset.smul_sum, mul_smul]
  map_apply g a := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk, rep_G_on_CX_apply_apply, smul_eq_mul, map_sum,
      map_smul]
    apply Fintype.sum_bijective (fun h ↦ g⁻¹ • h) (MulAction.bijective g⁻¹)
    intro x
    have h2 : ρ g (ρ (g⁻¹ • x) v) = (ρ g * ρ (g⁻¹ • x)) v := rfl
    rw [h2, ← map_mul ρ]
    simp

open Classical

variable (v : V)

variable (g : G)

/--The simplification of T(g) = ρ(g)v, where T is the homomorphism ℂ[G] → V and T(e) = v-/
@[simp]
lemma Hom_singleton : (Hom_CG_V ρ v) (Pi.single g 1) = (ρ g) v := by
  rw [← coe_repMap]
  simp only [Hom_CG_V, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single g (by simp +contextual) (by simp)]
  simp

/--∃! homomorphism of representations ℂ[G] → V sending e ∈ G ⊆ ℂ[G] to v ∈ V-/
theorem exists_unique_hom_v : ∃! T : RepMap (rep_G_on_CX G) ρ, T (Pi.single 1 1) = v := by
  use Hom_CG_V ρ v
  constructor
  · simp
  · intro T hT
    simp only [RepMap.eq_iff]
    -- real proof starts here
    let b : Basis G ℂ _ := Pi.basisFun ℂ G
    apply b.ext
    intro g
    rw [Pi.basisFun_apply]
    simp only [coe_repMap, Hom_singleton]
    show T (b g) = _
    have h1 : b g = rep_G_on_CX G g (b 1) := by
      ext x
      simp [b, Pi.single_apply, inv_mul_eq_one, eq_comm]
    rw [h1, ← coe_repMap, T.map_apply, ← hT]
    rfl

-- Example: all of the homomorphisms ℂ[G] → v are of this form
lemma Hom_CG_V_inv (T : RepMap (rep_G_on_CX G) ρ) : ∃ (v : V), T = Hom_CG_V ρ v := by
  let v := T (Pi.single 1 1)
  use v
  apply (exists_unique_hom_v ρ v).unique
  · simp [v]
  · simp

/-- Bijection between Hom(ℂ[G],V) and V-/
noncomputable def bijection_CG_V : RepMap (rep_G_on_CX G) ρ ≃ V where
  toFun T := T (Pi.single 1 1)
  invFun v := Hom_CG_V ρ v
  left_inv T := by
    obtain ⟨v, hTv⟩ := Hom_CG_V_inv ρ T
    rw [hTv]
    simp
  right_inv v := by simp
