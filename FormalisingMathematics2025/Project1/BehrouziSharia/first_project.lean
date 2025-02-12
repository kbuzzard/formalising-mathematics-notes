import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Trails
import Init.Data.Range
import Batteries.Data.Range.Lemmas

/-!
Here we are trying to formalise the existance of Eulerian Circuits
in SimpleGraphs. For now we are only focusing on SimpleGraphs with
all vertices of even degrees.

## Main results

* `exists_eulerian_circuit`: Given a simple graph with even degree vertices (starting from an
    arbitrary vertex in the graph) there exists an Eulerian Circuit.

* `nil`: The base case of the Proof in `exists_eulerian_circuit` with
    a single vertex and zero edges.

* `add_edge`: A function used to add an edge to a given SimpleGraph
    generating a new SimpleGraph consequently.

* `has_vert_if_rem_still_conn`: If the graph is connected, then there is atleast
    two edges in the graph, then there exists a vertex such that when removed
    (with its incident edges) the graph would still remain connected.
-/

universe u
open Set SimpleGraph Classical Path
variable (V :Type) (G : SimpleGraph V)
variable (x y v : V)
variable [DecidableRel G.Adj]

-- Base case of the `exists_eulerian_circuit`
lemma IsEulerian.nil {G : SimpleGraph V} [DecidableEq V] [Fintype V]
    [DecidableRel G.Adj] {v : V} (h: Finset.card G.edgeFinset = Nat.zero):
    (SimpleGraph.Walk.nil : G.Walk v v).IsEulerian := by
  have hEmp : SimpleGraph.edgeSet G = ∅ := by
    rw[Finset.card_eq_zero] at h
    -- The finset of a set is empty iff the set is also empty
    exact toFinset_eq_empty.mp h

  -- take an arbitrary edge w from the walk
  -- hw : w is in the edge set of G
  intro w hw
  rw [hEmp] at hw
  -- from False any proposition holds
  exact hw.elim

/-- This lemma is not generally true, we can use it here
  because we know the graphs G₁ won't be empty, This is because
  in the inductive case, we use the lemma (IsEulerian.has_vert_if_rem_still_conn)
  which says the graph G will still be connected after removing the
  vertex vertNotDiscon, in Lean "Connected" means preconnected and
  non-empty, hence the resulting graph after deleting vertNotDiscon (with
  its incident edges) will be still connected -/
lemma connected_when_subgraph_preconnected {G G₁ G₂ : SimpleGraph V}
    (v₁ : G.support) (hG₁SubG₂ : G₁ ≤ G₂)
    (hG₁Precon : G₁.Preconnected) : G₂.Connected := by
  -- a graph is connected iff there is vertex that is reachable
  -- by other vertices
  rw[connected_iff_exists_forall_reachable]
  use v₁
  -- G₂ is also preconnected
  have hG₂Precon : G₂.Preconnected := by
    -- G₁ ≤ G₂ and G₁ is preconnected hence G₂ is preconnected
    exact Preconnected.mono hG₁SubG₂ hG₁Precon

  rw [Preconnected] at hG₂Precon
  -- every vertex is reachable in G₂ from v₁
  intro vReach
  exact hG₂Precon v₁ vReach
  -- specialize hG₂Precon v₁
  -- -- take an arbitrary vertex vReach
  -- intro vReach
  -- specialize hG₂Precon vReach
  -- exact hG₂Precon

/-- Given a connected graph, with two or more vertices
  The graph has a vertex that can be removed (along with its incident edges)
  without disconnecting the remaining graph -/
lemma IsEulerian.has_vert_if_rem_still_conn {G : SimpleGraph V} {v : V}
    [Fintype V] [DecidableEq V] :
    (G.Connected ∧ Fintype.card G.edgeFinset ≥ 2) →
    ∃ v : G.support, (G.induce (fun v' : V ↦ v' ≠ v)).Connected := by

  rintro ⟨hGconn, hVertCardCount⟩
  sorry

/-- Generate a new graph give graph G and add a vertex between u and v -/
def add_edge (G : SimpleGraph V) (u v : V) : SimpleGraph V :=
  .fromEdgeSet (insert s(u, v) G.edgeSet)

theorem IsEulerian.exists_eulerian_circuit (G : SimpleGraph V)
    [Fintype V]
    (hNonEmptV : Fintype.card G.support ≥ 1) (hGconn : G.Connected):
    (∀ v : G.support, Even (G.degree v)) →
    (∀ v : G.support, ∃ w : G.Walk v v, (Walk.IsEulerian w)) := by

  -- hk : k is the number of edges
  set k := Finset.card G.edgeFinset with ← hk
  -- clear the body of the definition of k
  clear_value k

  -- induction on the number of edges
  induction k generalizing G with

  -- base case
  | zero =>
    intro hEvenV v₀
    -- take an empty walk from v₀ to v₀
    use SimpleGraph.Walk.nil
    -- using the base-case (IsEulerian.nil lemma)
    exact nil V hk

  -- inductive case
  | succ k i_k =>
    intro hEvDeg v₁

    have numVertGe2 : Fintype.card G.edgeFinset ≥ 2 := by
      -- let's assume number of edges < 2
      by_contra h
      push_neg at h
      sorry

    /- hVerDelCon is using the lemma that there is
       a vertex such that if we delete it with its
       connecting edges, the graph would still remain connected -/
    have hVertDelCon : ∃ v : G.support, (G.induce (fun v' : V ↦ v' ≠ v)).Connected  := by
      apply IsEulerian.has_vert_if_rem_still_conn
      obtain ⟨v, vInG₁⟩ := v₁
      exact v
      simp_all

    cases' hVertDelCon with vertNotDiscon hVertNotDiscon


    /- Each vertex is atleast of degree 2, hence
       there must be atleas4 two edges x and y that
       are the neighbours of vertNotDiscon -/
    have hTwoNeighbors : ∃ x y : G.support, G.Adj x vertNotDiscon ∧
        G.Adj y vertNotDiscon := by
      sorry
      done

    -- x and y are adjacent to vertNotDiscon
    rcases hTwoNeighbors with ⟨x, y, hx, hy⟩
    obtain ⟨xv, xvInG⟩ := x
    obtain ⟨yv, yvInG⟩ := y
    -- the edge between vertNotDisconn and x
    set vertxNotDisconEdge := s(xv, vertNotDiscon)
    --the edge between vertNotDisconn and y
    set vertyNotDisconEdge := s(yv, vertNotDiscon)
    set G₁ := (G.deleteEdges {vertyNotDisconEdge, vertxNotDisconEdge})
    -- construct a graph G₂ by adding an edge between x and y
    set G₂ := add_edge V G₁ xv yv

    set xyEdge := s(xv, yv)

    have hG₁SubG₂ : G₁ ≤ G₂ := by
      -- Introduce vertices a, b and their adjacency hypothesis in G₁
      intro a b hab
      -- Expand definitions to work with edge sets
      simp [G₁, G₂, add_edge] at hab ⊢
      -- Decompose the adjacency hypothesis into its components
      rcases hab with ⟨habG, habNotDeleted⟩
      aesop_graph

    have hG₁Precon : G₁.Preconnected := by
      sorry
      done

    -- G₂ should be connected
    have hG₂Connected : G₂.Connected := by
      exact connected_when_subgraph_preconnected V v₁ hG₁SubG₂ hG₁Precon


    /- this is because by removing two edges and adding one to
        graph G (with number of edges k + 1), then we end up
        with a graph of k edges -/
    have hG₂kEdges : (G₂.edgeFinset.card = k) := by
      -- simp [G₂, add_edge, insert]
      sorry
      done

    /- in G₂ all vertices should have even degrees. This is because in
       G every edge has an even degree. And we know G₂ has all vertices
       of G other than vertNotDiscon. Removing two edges (x, vertNotDiscon) and
       (y, vertNotDiscon) removes one edge incident to x and one edge incident
       to y, making those of an odd degree. But we have added the edge (x, y)
       making those vertices of even degree again, hence all vertices in G₂ should
       have even degrees -/
    have hG₂AllEvenDeg : (∀ v : G₂.support, Even (G₂.degree v)) := by
      sorry
      done

    have hG₂NonEmptv : Fintype.card G₂.support ≥ 1 := by
      sorry
      done

    /- Assuming vertNotDiscon is not the same as v₁
       this case should be handled later -/
    set v₁ : G₂.support := by
      sorry
      done

    -- using the induction hypothesis
    specialize i_k G₂ hG₂NonEmptv
    apply i_k at hG₂Connected
    apply hG₂Connected at hG₂kEdges
    specialize hG₂kEdges hG₂AllEvenDeg v₁

    /- Now hG₂kEdges says that g₂ has an eulerian walk
       now we kknow w₁ is a walk from the vertex v₁ to v₁ -/
    cases' hG₂kEdges with w₁ hw₁

    sorry
    done

#lint
