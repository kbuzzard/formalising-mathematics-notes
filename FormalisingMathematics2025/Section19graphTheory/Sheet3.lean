/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
-- trees and forests

/-

# Trees and forests

A *forest* is a graph with no cycles. A *tree* is a connected forest.

Here's how to do this in Lean. Let `G` be a graph with vertex set `V`.

-/

variable (V : Type) (G : SimpleGraph V)

namespace SimpleGraph

-- Here's how to say "G is a forest"
example : Prop :=
  G.IsAcyclic

-- It's defined to mean "For all `v : V`, every walk from `v` to `v` is not a cycle. "
example : G.IsAcyclic ↔ ∀ (v : V) (p : G.Walk v v), ¬p.IsCycle := by rfl

-- Here's how to say "G is a tree"
example : Prop :=
  G.IsTree

example : G.IsTree ↔ G.Connected ∧ G.IsAcyclic :=
  G.isTree_iff

-- Here are some harder theorems from the library. Recall that a *path* is a walk
-- with no repeated vertices.
-- A graph is acyclic iff for all `v w : V`, there's at most one path from `v` to `w`.
example : G.IsAcyclic ↔ ∀ (v w : V) (p q : G.Path v w), p = q :=
  SimpleGraph.isAcyclic_iff_path_unique

-- A graph is a tree iff `V` is nonempty and for all `v w : V`,
-- there's exactly one path from `v` to `w`.
example : G.IsTree ↔ Nonempty V ∧ ∀ v w : V, ∃! p : G.Walk v w, p.IsPath :=
  SimpleGraph.isTree_iff_existsUnique_path

-- If you want a logic puzzle, rephrase this in terms of `G.path`
-- (i.e. use the theorem above and then unpack and repack the RHS)
example : G.IsTree ↔ Nonempty V ∧ ∀ v w : V, ∃! p : G.Path v w, True := by sorry

@[simp] lemma ofLE_comp_ofLE {A B C : SimpleGraph V} (a : A ≤ B) (b : B ≤ C) :
    (Hom.ofLE b).comp (Hom.ofLE a) = Hom.ofLE (a.trans b) := by
  rfl

lemma sSup_walk {S : Set (SimpleGraph V)} (hS' : DirectedOn (· ≤ ·) S) {v w : V}
    (p : (sSup S).Walk v w) (hS : S.Nonempty) :
    ∃ G, ∃ (h : G ∈ S), ∃ p' : G.Walk v w, p'.map (.ofLE (le_sSup h)) = p := by
  induction p with
  | nil =>
      obtain ⟨G, hG⟩ := hS
      use G, hG, .nil
      simp
  | cons h p ih =>
      obtain ⟨G, hG, p', rfl⟩ := ih
      simp only [SimpleGraph.sSup_adj] at h
      obtain ⟨G', hG', huv⟩ := h
      obtain ⟨H, hH, hGH, hG'H⟩ := hS' _ hG _ hG'
      use H, hH
      use Walk.cons ((Hom.ofLE hG'H).map_adj huv) (p'.map (.ofLE hGH))
      simp

lemma Walk.IsCycle.of_map {W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) {v : V} (p : G.Walk v v) (hp : (p.map f).IsCycle) :
    p.IsCycle := by
  cases p with
  | nil => simp at hp
  | cons vw hwv =>
      rw [Walk.map_cons, Walk.cons_isCycle_iff] at hp
      rw [Walk.cons_isCycle_iff]
      refine ⟨hp.1.of_map, ?_⟩
      intro h
      apply hp.2
      simp only [Walk.edges_map, List.mem_map]
      exact ⟨_, h, rfl⟩

lemma sSup_acyclic {S : Set (SimpleGraph V)} (hS : ∀ x ∈ S, x.IsAcyclic) (hS' : IsChain (· ≤ ·) S) :
    (sSup S).IsAcyclic := by
  obtain rfl | hS'' := S.eq_empty_or_nonempty
  · simp
  intro v c hc
  obtain ⟨G, hG, c, rfl⟩ := sSup_walk _ hS'.directedOn c hS''
  exact hS _ hG _ (hc.of_map _)

example (hG : G.IsAcyclic) : ∃ H ≥ G, Maximal IsAcyclic H := by
  let S : Set (SimpleGraph V) := {H | H.IsAcyclic}
  change ∃ H, G ≤ H ∧ Maximal (· ∈ S) H
  refine zorn_le_nonempty₀ S ?_ _ hG
  intro c hcS hc y hy
  use sSup c
  constructor
  · refine sSup_acyclic _ ?_ hc
    intro x hx
    exact hcS hx
  · intro z hz
    exact le_sSup hz

lemma maximal_simpleGraph_iff_edgeSet {G : SimpleGraph V} {p : SimpleGraph V → Prop} :
    Maximal p G ↔ Maximal (fun s ↦ Disjoint s {i | i.IsDiag} ∧ p (fromEdgeSet s)) G.edgeSet := by
  sorry

lemma maximal_simpleGraph_iff {G : SimpleGraph V} {p : SimpleGraph V → Prop} :
    Maximal p G ↔
      p G ∧ ∀ x y : V, ¬ G.Adj x y → ¬ p (fromEdgeSet (insert s(x, y) G.edgeSet)) := by
  simp only [not_imp_not]
  constructor
  · rintro ⟨h₁, h₂⟩

  · sorry

lemma isTree_of_maximal_isAcyclic {G : SimpleGraph V} (hG : Maximal IsAcyclic G) :
    G.IsTree := by
  sorry


-- Here's a result which isn't yet in mathlib: `G` is a tree iff it's a maximal acyclic graph
-- If you fill this one in, let me know and we can put it in mathlib!
example : G.IsTree ↔ Maximal IsAcyclic G := by
  sorry
