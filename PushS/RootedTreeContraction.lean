/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.RootedTreeGrowth

/-! A genuine standard edge-contraction trace contracts a listed growing tree in reverse order. -/

public section
namespace PushPuzzle.Graph

open Cslib.Complexity.Graph

open Cslib.Complexity

namespace RotationSystem

open Cslib.Complexity.Graph.RotationSystem

/-- Reinterpret a rotation across a literal equality of its indexed listed graphs. -/
@[expose] def castGraph {G H : Graph} (h : G = H) (r : RotationSystem G) : RotationSystem H := h ▸ r

/-- A trace uses only literal graph equalities and actual standard nonloop last-edge contractions. -/
inductive ContractionTrace : {G H : Graph} → RotationSystem G → RotationSystem H → Prop
  | refl {G : Graph} (r : RotationSystem G) : ContractionTrace r r
  | cast {G H : Graph} (h : G = H) (r : RotationSystem G) : ContractionTrace r (castGraph h r)
  | contract {G : Graph} {u v : ℕ} (r : RotationSystem (lastEdgeGraph G u v)) (huv : u ≠ v) :
      ContractionTrace r (r.contractLastEdge huv)
  | trans {G H K : Graph} {r : RotationSystem G} {s : RotationSystem H} {t : RotationSystem K}
      (first : ContractionTrace r s) (second : ContractionTrace s t) : ContractionTrace r t

/-- Genuine contraction traces preserve both actual endpoint declarations and numerical genus zero. -/
theorem ContractionTrace.preserves {G H : Graph} {r : RotationSystem G} {s : RotationSystem H}
    (trace : ContractionTrace r s)
    (hG : ∀ vertex ∈ G.incidenceVertices, vertex ∈ G.vertices) (hr : r.NumericalGenusZero) :
    (∀ vertex ∈ H.incidenceVertices, vertex ∈ H.vertices) ∧ s.NumericalGenusZero := by
  induction trace with
  | refl => exact ⟨hG, hr⟩
  | cast h r => cases h; exact ⟨hG, hr⟩
  | contract r huv => exact ⟨endpoints_declared_contractLastEdge hG, r.numericalGenusZero_contractLastEdge huv hG hr⟩
  | trans first second ihfirst ihsecond =>
    obtain ⟨hH, hs⟩ := ihfirst hG hr
    exact ihsecond hH hs

end RotationSystem

namespace RootedTreeGrowth

/-- Attach the exact growing tree edge array after the original indexed base edges. -/
@[expose] def graph (base : Graph) (edges : List (ℕ × ℕ)) : Graph := ⟨base.vertices, base.edges ++ edges⟩

/-- The exact original base graph after eliminating the actual tree children from last to first. -/
@[expose] def contractedBase (base : Graph) (edges : List (ℕ × ℕ)) : Graph :=
  edges.foldr (fun edge result => result.relabel (Function.update id edge.1 edge.2)) base

/-- Actual relabeling contractions retain every original indexed base edge occurrence. -/
theorem contractedBase_edges_length (base : Graph) (edges : List (ℕ × ℕ)) :
    (contractedBase base edges).edges.length = base.edges.length := by
  induction edges with
  | nil => rfl
  | cons edge edges ih =>
    change ((contractedBase base edges).relabel (Function.update id edge.1 edge.2)).edges.length = _
    simpa only [relabel, List.length_map] using ih

/-- Each literal final tree edge is eliminated before the preceding actual edge word. -/
theorem contractedBase_snoc (base : Graph) (edges : List (ℕ × ℕ)) (child parent : ℕ) :
    contractedBase base (edges ++ [(child, parent)]) =
      contractedBase (base.relabel (Function.update id child parent)) edges := by
  simp only [contractedBase, List.foldr_append, List.foldr_cons, List.foldr_nil]

private theorem update_mem_prefix {root child parent vertex : ℕ} {edges : List (ℕ × ℕ)}
    (fresh : child ∉ root :: edges.map Prod.fst) (attached : parent ∈ root :: edges.map Prod.fst)
    (hv : vertex ∈ root :: (edges ++ [(child, parent)]).map Prod.fst) :
    Function.update id child parent vertex ∈ root :: edges.map Prod.fst := by
  simp only [List.map_append, List.map_cons, List.map_nil, List.mem_cons, List.mem_append,
    List.not_mem_nil, or_false] at hv
  rcases hv with hv | hv | hv
  · have hm : vertex ∈ root :: edges.map Prod.fst := List.mem_cons.mpr (Or.inl hv)
    rw [update_node fresh hm]
    exact hm
  · have hm : vertex ∈ root :: edges.map Prod.fst := List.mem_cons_of_mem _ hv
    rw [update_node fresh hm]
    exact hm
  · subst vertex
    simpa only [Function.update_self] using attached

/-- Eliminating a genuine growing spanning tree sends every original indexed base end to its root. -/
theorem contractedBase_eq_root {root : ℕ} {edges : List (ℕ × ℕ)} (tree : RootedTreeGrowth root edges)
    (base : Graph) (hV : ∀ vertex ∈ base.vertices, vertex ∈ root :: edges.map Prod.fst)
    (hE : ∀ edge ∈ base.edges, edge.1 ∈ root :: edges.map Prod.fst ∧ edge.2 ∈ root :: edges.map Prod.fst) :
    contractedBase base edges = ⟨base.vertices.map (fun _ => root), base.edges.map (fun _ => (root, root))⟩ := by
  induction tree generalizing base with
  | nil =>
    change base = _
    apply Graph.ext
    · symm
      calc
        _ = base.vertices.map id := List.map_congr_left (fun vertex hv => (List.mem_singleton.mp (hV vertex hv)).symm)
        _ = _ := List.map_id _
    · symm
      calc
        _ = base.edges.map id := List.map_congr_left (fun edge he => Prod.ext
          (List.mem_singleton.mp (hE edge he).1).symm (List.mem_singleton.mp (hE edge he).2).symm)
        _ = _ := List.map_id _
  | @snoc edges child parent tree fresh attached ih =>
    rw [contractedBase_snoc]
    have hV' : ∀ vertex ∈ (base.relabel (Function.update id child parent)).vertices,
        vertex ∈ root :: edges.map Prod.fst := by
      intro vertex hv
      obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hv
      exact update_mem_prefix fresh attached (hV old hold)
    have hE' : ∀ edge ∈ (base.relabel (Function.update id child parent)).edges,
        edge.1 ∈ root :: edges.map Prod.fst ∧ edge.2 ∈ root :: edges.map Prod.fst := by
      intro edge he
      obtain ⟨old, hold, rfl⟩ := List.mem_map.mp he
      exact ⟨update_mem_prefix fresh attached (hE old hold).1, update_mem_prefix fresh attached (hE old hold).2⟩
    rw [ih _ hV' hE']
    simp only [relabel, List.map_map, Function.comp_def]

/-- Reverse growth order gives a real standard contraction trace, retaining the exact final base graph. -/
theorem exists_contraction {root : ℕ} {edges : List (ℕ × ℕ)} (tree : RootedTreeGrowth root edges)
    (base : Graph) (r : RotationSystem (graph base edges)) :
    ∃ s : RotationSystem (contractedBase base edges), RotationSystem.ContractionTrace r s := by
  induction tree generalizing base with
  | nil =>
    have hg : graph base [] = base := by simp [graph]
    exact ⟨RotationSystem.castGraph hg r, .cast hg r⟩
  | @snoc edges child parent tree fresh attached ih =>
    have hfirst : graph base (edges ++ [(child, parent)]) = RotationSystem.lastEdgeGraph (graph base edges) child parent := by
      simp only [graph, RotationSystem.lastEdgeGraph, List.append_assoc]
    let first := RotationSystem.castGraph hfirst r
    let middle := first.contractLastEdge (child_ne_parent fresh attached)
    have hmiddle : RotationSystem.contractLastEdgeGraph (graph base edges) child parent =
        graph (base.relabel (Function.update id child parent)) edges := tree.contract_graph fresh base
    let next := RotationSystem.castGraph hmiddle middle
    obtain ⟨last, hlast⟩ := ih (base.relabel (Function.update id child parent)) next
    have hfinal := (contractedBase_snoc base edges child parent).symm
    refine ⟨RotationSystem.castGraph hfinal last, ?_⟩
    exact (RotationSystem.ContractionTrace.cast hfirst r).trans
      ((RotationSystem.ContractionTrace.contract first (child_ne_parent fresh attached)).trans
        ((RotationSystem.ContractionTrace.cast hmiddle middle).trans
          (hlast.trans (RotationSystem.ContractionTrace.cast hfinal last))))

end RootedTreeGrowth
end PushPuzzle.Graph
