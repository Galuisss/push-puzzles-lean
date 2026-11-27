/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.EdgeContractionGenus

/-! A leaf-to-root listed tree grows by attaching each new child to an already listed parent. -/

public section
namespace PushPuzzle.Graph

open Cslib.Complexity.Graph

open Cslib.Complexity

/-- Edges are listed in growth order and directed from each fresh child to its existing parent. -/
inductive RootedTreeGrowth (root : ℕ) : List (ℕ × ℕ) → Prop
  | nil : RootedTreeGrowth root []
  | snoc {edges : List (ℕ × ℕ)} {child parent : ℕ} (tree : RootedTreeGrowth root edges)
      (fresh : child ∉ root :: edges.map Prod.fst) (attached : parent ∈ root :: edges.map Prod.fst) :
      RootedTreeGrowth root (edges ++ [(child, parent)])

namespace RootedTreeGrowth

/-- The literal directed edge word obtained by appending fresh nodes along one simple branch. -/
@[expose] def pathEdges (parent : ℕ) : List ℕ → List (ℕ × ℕ)
  | [] => []
  | child :: nodes => (child, parent) :: pathEdges child nodes

/-- Every path-edge occurrence retains its exact child and preceding parent occurrence. -/
theorem pathEdges_eq_zip (parent : ℕ) (nodes : List ℕ) : pathEdges parent nodes = nodes.zip (parent :: nodes) := by
  induction nodes generalizing parent with
  | nil => rfl
  | cons child nodes ih => simp only [pathEdges, List.zip_cons_cons, ih]

/-- The branch word retains every appended child once, in its original order. -/
theorem pathEdges_children (parent : ℕ) (nodes : List ℕ) : (pathEdges parent nodes).map Prod.fst = nodes := by
  induction nodes generalizing parent with
  | nil => rfl
  | cons child nodes ih => simp only [pathEdges, List.map_cons, ih]

/-- Adjacent actual array entries give exactly the same literal child-to-parent edge word. -/
theorem pathEdges_ofFn {n : ℕ} (nodes : Fin (n + 1) → ℕ) :
    pathEdges (nodes 0) (List.ofFn (fun i : Fin n => nodes i.succ)) =
      List.ofFn (fun i : Fin n => (nodes i.succ, nodes i.castSucc)) := by
  induction n with
  | zero => simp [pathEdges]
  | succ n ih =>
    rw [List.ofFn_succ, pathEdges, List.ofFn_succ]
    congr 1
    exact ih (fun i => nodes i.succ)

/-- A nonempty actual node array retains its exact adjacent child and parent indices. -/
theorem pathEdges_tail_ofFn {n : ℕ} (hn : 0 < n) (nodes : Fin n → ℕ) :
    pathEdges ((List.ofFn nodes).head (by
      intro he
      have h := congrArg List.length he
      simp only [List.length_ofFn, List.length_nil] at h
      omega))
        (List.ofFn nodes).tail =
      List.ofFn (fun i : Fin (n - 1) =>
        (nodes ⟨i.val + 1, by have := i.isLt; omega⟩, nodes ⟨i.val, by have := i.isLt; omega⟩)) := by
  cases n with
  | zero => omega
  | succ n =>
    simp only [List.ofFn_succ, List.head_cons, List.tail_cons]
    rw [pathEdges_ofFn]
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_ofFn]
      rfl

/-- A fresh nonrepeating branch can be attached to any already listed actual tree node. -/
theorem attach_path {root : ℕ} {edges : List (ℕ × ℕ)} (tree : RootedTreeGrowth root edges)
    (parent : ℕ) (hp : parent ∈ root :: edges.map Prod.fst) (nodes : List ℕ)
    (hn : nodes.Nodup) (hd : List.Disjoint nodes (root :: edges.map Prod.fst)) :
    RootedTreeGrowth root (edges ++ pathEdges parent nodes) := by
  induction nodes generalizing parent edges with
  | nil => simpa only [pathEdges, List.append_nil] using tree
  | cons child nodes ih =>
    have hfresh : child ∉ root :: edges.map Prod.fst := fun hc => List.disjoint_left.mp hd (by simp) hc
    have tree' := tree.snoc hfresh hp
    have hchild : child ∈ root :: (edges ++ [(child, parent)]).map Prod.fst := by simp
    have hd' : List.Disjoint nodes (root :: (edges ++ [(child, parent)]).map Prod.fst) := by
      apply List.disjoint_left.mpr
      intro node hnode hmem
      simp only [List.map_append, List.map_cons, List.map_nil, List.mem_cons, List.mem_append,
        List.not_mem_nil, or_false] at hmem
      rcases hmem with hroot | hold | hchild
      · exact List.disjoint_left.mp hd (List.mem_cons_of_mem _ hnode) (List.mem_cons.mpr (Or.inl hroot))
      · exact List.disjoint_left.mp hd (List.mem_cons_of_mem _ hnode) (List.mem_cons_of_mem _ hold)
      · exact (List.nodup_cons.mp hn).1 (hchild ▸ hnode)
    simpa only [pathEdges, List.append_assoc, List.singleton_append] using ih tree' child hchild hn.tail hd'

/-- Disjoint fresh branches can be attached at any nodes of the complete existing tree. -/
theorem attach_paths {root : ℕ} {edges : List (ℕ × ℕ)} (tree : RootedTreeGrowth root edges)
    (branches : List (ℕ × List ℕ))
    (hp : ∀ branch ∈ branches, branch.1 ∈ root :: edges.map Prod.fst)
    (hn : (branches.flatMap Prod.snd).Nodup)
    (hd : List.Disjoint (branches.flatMap Prod.snd) (root :: edges.map Prod.fst)) :
    RootedTreeGrowth root (edges ++ branches.flatMap (fun branch => pathEdges branch.1 branch.2)) := by
  induction branches generalizing edges with
  | nil => simpa only [List.flatMap_nil, List.append_nil] using tree
  | cons branch branches ih =>
    have hn' := List.nodup_append.mp hn
    have hb := tree.attach_path branch.1 (hp branch (by simp)) branch.2 hn'.1 (by
      exact List.disjoint_left.mpr (fun _ hnode hold => List.disjoint_left.mp hd (List.mem_append_left _ hnode) hold))
    have hin {vertex : ℕ} (hv : vertex ∈ root :: edges.map Prod.fst) :
        vertex ∈ root :: (edges ++ pathEdges branch.1 branch.2).map Prod.fst := by
      rw [List.map_append, pathEdges_children]
      rcases List.mem_cons.mp hv with rfl | hv
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ hv)
    have hp' : ∀ next ∈ branches, next.1 ∈ root :: (edges ++ pathEdges branch.1 branch.2).map Prod.fst :=
      fun next hnext => hin (hp next (List.mem_cons_of_mem _ hnext))
    have hd' : List.Disjoint (branches.flatMap Prod.snd) (root :: (edges ++ pathEdges branch.1 branch.2).map Prod.fst) := by
      apply List.disjoint_left.mpr
      intro vertex hv hw
      rw [List.map_append, pathEdges_children] at hw
      rcases List.mem_cons.mp hw with hw | hw
      · exact List.disjoint_left.mp hd (List.mem_append_right _ hv) (List.mem_cons.mpr (Or.inl hw))
      · rcases List.mem_append.mp hw with hw | hw
        · exact List.disjoint_left.mp hd (List.mem_append_right _ hv) (List.mem_cons_of_mem _ hw)
        · exact hn'.2.2 vertex hw vertex hv rfl
    simpa only [List.flatMap_cons, List.append_assoc] using ih hb hp' hn'.2.1 hd'

/-- A nonempty nonrepeating actual array grows into its precise consecutive path. -/
theorem of_nodup_path (nodes : List ℕ) (hn : nodes.Nodup) (hne : nodes ≠ []) :
    RootedTreeGrowth (nodes.head hne) (pathEdges (nodes.head hne) nodes.tail) := by
  cases nodes with
  | nil => exact False.elim (hne rfl)
  | cons root nodes =>
    apply attach_path nil root (by simp) nodes hn.tail
    apply List.disjoint_left.mpr
    intro node hnode hroot
    have he := List.mem_singleton.mp hroot
    change node = root at he
    exact (List.nodup_cons.mp hn).1 (he ▸ hnode)

/-- Both ends of every genuine tree edge are among its root and listed children. -/
theorem endpoints_mem {root : ℕ} {edges : List (ℕ × ℕ)} (tree : RootedTreeGrowth root edges)
    {edge : ℕ × ℕ} (he : edge ∈ edges) :
    edge.1 ∈ root :: edges.map Prod.fst ∧ edge.2 ∈ root :: edges.map Prod.fst := by
  induction tree with
  | nil => simp at he
  | @snoc edges child parent tree fresh attached ih =>
    have hin {vertex : ℕ} (hv : vertex ∈ root :: edges.map Prod.fst) :
        vertex ∈ root :: (edges ++ [(child, parent)]).map Prod.fst := by
      rcases List.mem_cons.mp hv with rfl | hv
      · exact List.mem_cons_self
      · rw [List.map_append]
        exact List.mem_cons_of_mem _ (List.mem_append_left _ hv)
    rcases List.mem_append.mp he with he | he
    · exact ⟨hin (ih he).1, hin (ih he).2⟩
    · have heq := List.mem_singleton.mp he
      subst edge
      exact ⟨by simp, hin attached⟩

/-- Every growth step has a fresh child different from its already listed parent. -/
theorem child_ne_parent {root child parent : ℕ} {edges : List (ℕ × ℕ)}
    (fresh : child ∉ root :: edges.map Prod.fst) (attached : parent ∈ root :: edges.map Prod.fst) :
    child ≠ parent := fun h => fresh (h ▸ attached)

/-- An elimination update fixes every previously listed tree node. -/
theorem update_node {root child parent vertex : ℕ} {edges : List (ℕ × ℕ)}
    (fresh : child ∉ root :: edges.map Prod.fst) (hv : vertex ∈ root :: edges.map Prod.fst) :
    Function.update id child parent vertex = vertex := by
  have hne : vertex ≠ child := by intro h; subst child; exact fresh hv
  exact Function.update_of_ne hne parent id

/-- Contracting the final fresh child leaves the complete earlier tree-edge array unchanged. -/
theorem update_edges {root child parent : ℕ} {edges : List (ℕ × ℕ)} (tree : RootedTreeGrowth root edges)
    (fresh : child ∉ root :: edges.map Prod.fst) :
    edges.map (Prod.map (Function.update id child parent) (Function.update id child parent)) = edges := by
  calc
    _ = edges.map id := by
      apply List.map_congr_left
      intro edge he
      have hm := tree.endpoints_mem he
      exact Prod.ext (update_node fresh hm.1) (update_node fresh hm.2)
    _ = edges := List.map_id edges

/-- The exact contracted graph retains its earlier tree and relabels only the original base graph. -/
theorem contract_graph {root child parent : ℕ} {edges : List (ℕ × ℕ)} (tree : RootedTreeGrowth root edges)
    (fresh : child ∉ root :: edges.map Prod.fst) (base : Graph) :
    RotationSystem.contractLastEdgeGraph ⟨base.vertices, base.edges ++ edges⟩ child parent =
      ⟨(base.relabel (Function.update id child parent)).vertices,
        (base.relabel (Function.update id child parent)).edges ++ edges⟩ := by
  simp only [RotationSystem.contractLastEdgeGraph, relabel, List.map_append, tree.update_edges fresh]

end RootedTreeGrowth
end PushPuzzle.Graph
