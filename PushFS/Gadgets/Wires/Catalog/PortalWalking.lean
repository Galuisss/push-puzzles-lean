/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.ExteriorGeometry

/-! Native guarded-turn corner walks retain foreign boxes outside the true turn rectangle. -/

@[expose] public section

namespace PushPuzzle.PushFS.Gadgets.Wires.Polyline.L

open Reduction
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

variable (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) {W H : ℕ}

/-- Foreign endpoint inventories stay outside the guarded central turn. -/
theorem turn_corners_foreign (goals : Finset (C m n)) (a : Phases)
    (e : GridEmbedding (m+43) (n+44) W H) (B : Board W H)
    (outside : Finset (PushFS.Cell W H)) (hw : e.WallsAgree (board m n hm hn goals) B)
    (hf : Disjoint outside B.walls)
    (hno : ∀p : Turn.C,((turnRect m n hm hn).trans e).cells p∉outside) (i : Fin 4) :
    Reachable B (some 1) (e.extend outside (state m n hm hn a))
      (e.extend outside ⟨(turnRect m n hm hn).cells (Turn.corner i),boxes m n hm hn a⟩) ∧
    Reachable B (some 1) (e.extend outside ⟨(turnRect m n hm hn).cells (Turn.corner i),boxes m n hm hn a⟩)
      (e.extend outside (state m n hm hn a)) := by
  let z:=(turnRect m n hm hn).trans e
  let xs:=(turnExternal m n hm hn a).map e.cells∪outside
  have hz : z.WallsAgree (Turn.template.board ∅) B := by
    intro p
    exact (hw ((turnRect m n hm hn).cells p)).trans (turn_walls_agree m n hm hn goals p)
  have hxs : Disjoint xs B.walls := by
    apply Finset.disjoint_union_left.mpr
    refine ⟨Finset.disjoint_left.mpr ?_,hf⟩
    intro p hp hpw
    obtain ⟨q,hq,rfl⟩:=Finset.mem_map.mp hp
    exact Finset.disjoint_left.mp (external_floor m n hm hn goals a).2.1 hq ((hw q).mp hpw)
  have hreserved : Polyline.Frame.fixed z xs⊆Turn.template.reservedCells := by
    dsimp only [z,xs]
    rw [Polyline.Frame.fixed_trans]
    intro p hp
    rcases Finset.mem_union.mp hp with hp|hp
    · exact turnFixed_reserved m n hm hn a ((mem_turnFixed m n hm hn a p).mpr ((Polyline.Frame.mem_fixed _ _ p).mp hp))
    · exact (hno p ((Polyline.Frame.mem_fixed _ _ p).mp hp)).elim
  have hfw : Disjoint (Polyline.Frame.fixed z xs) Turn.template.walls := by
    apply Finset.disjoint_left.mpr
    intro p hp hpw
    exact Finset.disjoint_left.mp hxs ((Polyline.Frame.mem_fixed z xs p).mp hp) ((hz p).mpr hpw)
  have hr:=Turn.checked.corners_covered (a 1) i (Polyline.Frame.fixed z xs) hreserved hfw z hz
    (fun p hp=>(Polyline.Frame.mem_fixed z xs p).mpr hp)
    (fun p hp=>(Polyline.Frame.mem_fixed z xs p).mp hp) hxs
  change Reachable _ _ (z.extend xs ⟨Turn.hub,Turn.template.boxes (a 1)⟩)
      (z.extend xs ⟨Turn.corner i,Turn.template.boxes (a 1)⟩) ∧
    Reachable _ _ (z.extend xs ⟨Turn.corner i,Turn.template.boxes (a 1)⟩)
      (z.extend xs ⟨Turn.hub,Turn.template.boxes (a 1)⟩) at hr
  simp only [z,xs,Polyline.Frame.extend_trans,place_turn,turn_hub] at hr
  exact hr

end PushPuzzle.PushFS.Gadgets.Wires.Polyline.L

namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog.Out
open Reduction
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

variable (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) {W H : ℕ}

/-- Foreign endpoint inventories stay outside the guarded central turn. -/
theorem turn_corners_foreign (goals : Finset (C m n)) (a : Phases)
    (e : GridEmbedding (m+43) (n+64) W H) (B : Board W H)
    (outside : Finset (PushFS.Cell W H)) (hw : e.WallsAgree (board m n hm hn goals) B)
    (hf : Disjoint outside B.walls)
    (hno : ∀p : Turn.C,((turnRect m n hm hn).trans e).cells p∉outside) (i : Fin 4) :
    Reachable B (some 1) (e.extend outside (state m n hm hn a))
      (e.extend outside ⟨(turnRect m n hm hn).cells (Turn.corner i),boxes m n hm hn a⟩) ∧
    Reachable B (some 1) (e.extend outside ⟨(turnRect m n hm hn).cells (Turn.corner i),boxes m n hm hn a⟩)
      (e.extend outside (state m n hm hn a)) := by
  let z:=(turnRect m n hm hn).trans e
  let xs:=(turnExternal m n hm hn a).map e.cells∪outside
  have hz : z.WallsAgree (Turn.template.board ∅) B := by
    intro p
    exact (hw ((turnRect m n hm hn).cells p)).trans (turn_walls_agree m n hm hn goals p)
  have hxs : Disjoint xs B.walls := by
    apply Finset.disjoint_union_left.mpr
    refine ⟨Finset.disjoint_left.mpr ?_,hf⟩
    intro p hp hpw
    obtain ⟨q,hq,rfl⟩:=Finset.mem_map.mp hp
    exact Finset.disjoint_left.mp (external_floor m n hm hn goals a).2.1 hq ((hw q).mp hpw)
  have hreserved : Polyline.Frame.fixed z xs⊆Turn.template.reservedCells := by
    dsimp only [z,xs]
    rw [Polyline.Frame.fixed_trans]
    intro p hp
    rcases Finset.mem_union.mp hp with hp|hp
    · exact turnFixed_reserved m n hm hn a ((mem_turnFixed m n hm hn a p).mpr ((Polyline.Frame.mem_fixed _ _ p).mp hp))
    · exact (hno p ((Polyline.Frame.mem_fixed _ _ p).mp hp)).elim
  have hfw : Disjoint (Polyline.Frame.fixed z xs) Turn.template.walls := by
    apply Finset.disjoint_left.mpr
    intro p hp hpw
    exact Finset.disjoint_left.mp hxs ((Polyline.Frame.mem_fixed z xs p).mp hp) ((hz p).mpr hpw)
  have hr:=Turn.checked.corners_covered (a 1) i (Polyline.Frame.fixed z xs) hreserved hfw z hz
    (fun p hp=>(Polyline.Frame.mem_fixed z xs p).mpr hp)
    (fun p hp=>(Polyline.Frame.mem_fixed z xs p).mp hp) hxs
  change Reachable _ _ (z.extend xs ⟨Turn.hub,Turn.template.boxes (a 1)⟩)
      (z.extend xs ⟨Turn.corner i,Turn.template.boxes (a 1)⟩) ∧
    Reachable _ _ (z.extend xs ⟨Turn.corner i,Turn.template.boxes (a 1)⟩)
      (z.extend xs ⟨Turn.hub,Turn.template.boxes (a 1)⟩) at hr
  simp only [z,xs,Polyline.Frame.extend_trans,place_turn,turn_hub] at hr
  exact hr

end PushPuzzle.PushFS.Gadgets.Wires.Catalog.Out

namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog.In
open Reduction
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

variable (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) {W H : ℕ}

/-- Foreign endpoint inventories stay outside the guarded central turn. -/
theorem turn_corners_foreign (goals : Finset (C m n)) (a : Phases)
    (e : GridEmbedding (m+63) (n+44) W H) (B : Board W H)
    (outside : Finset (PushFS.Cell W H)) (hw : e.WallsAgree (board m n hm hn goals) B)
    (hf : Disjoint outside B.walls)
    (hno : ∀p : Turn.C,((turnRect m n hm hn).trans e).cells p∉outside) (i : Fin 4) :
    Reachable B (some 1) (e.extend outside (state m n hm hn a))
      (e.extend outside ⟨(turnRect m n hm hn).cells (Turn.corner i),boxes m n hm hn a⟩) ∧
    Reachable B (some 1) (e.extend outside ⟨(turnRect m n hm hn).cells (Turn.corner i),boxes m n hm hn a⟩)
      (e.extend outside (state m n hm hn a)) := by
  let z:=(turnRect m n hm hn).trans e
  let xs:=(turnExternal m n hm hn a).map e.cells∪outside
  have hz : z.WallsAgree (Turn.template.board ∅) B := by
    intro p
    exact (hw ((turnRect m n hm hn).cells p)).trans (turn_walls_agree m n hm hn goals p)
  have hxs : Disjoint xs B.walls := by
    apply Finset.disjoint_union_left.mpr
    refine ⟨Finset.disjoint_left.mpr ?_,hf⟩
    intro p hp hpw
    obtain ⟨q,hq,rfl⟩:=Finset.mem_map.mp hp
    exact Finset.disjoint_left.mp (external_floor m n hm hn goals a).2.1 hq ((hw q).mp hpw)
  have hreserved : Polyline.Frame.fixed z xs⊆Turn.template.reservedCells := by
    dsimp only [z,xs]
    rw [Polyline.Frame.fixed_trans]
    intro p hp
    rcases Finset.mem_union.mp hp with hp|hp
    · exact turnFixed_reserved m n hm hn a ((mem_turnFixed m n hm hn a p).mpr ((Polyline.Frame.mem_fixed _ _ p).mp hp))
    · exact (hno p ((Polyline.Frame.mem_fixed _ _ p).mp hp)).elim
  have hfw : Disjoint (Polyline.Frame.fixed z xs) Turn.template.walls := by
    apply Finset.disjoint_left.mpr
    intro p hp hpw
    exact Finset.disjoint_left.mp hxs ((Polyline.Frame.mem_fixed z xs p).mp hp) ((hz p).mpr hpw)
  have hr:=Turn.checked.corners_covered (a 1) i (Polyline.Frame.fixed z xs) hreserved hfw z hz
    (fun p hp=>(Polyline.Frame.mem_fixed z xs p).mpr hp)
    (fun p hp=>(Polyline.Frame.mem_fixed z xs p).mp hp) hxs
  change Reachable _ _ (z.extend xs ⟨Turn.hub,Turn.template.boxes (a 1)⟩)
      (z.extend xs ⟨Turn.corner i,Turn.template.boxes (a 1)⟩) ∧
    Reachable _ _ (z.extend xs ⟨Turn.corner i,Turn.template.boxes (a 1)⟩)
      (z.extend xs ⟨Turn.hub,Turn.template.boxes (a 1)⟩) at hr
  simp only [z,xs,Polyline.Frame.extend_trans,place_turn,turn_hub] at hr
  exact hr

end PushPuzzle.PushFS.Gadgets.Wires.Catalog.In
