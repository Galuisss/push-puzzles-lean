/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingMeshBands
public import PushS.FiniteRoutingPortBounds

/-! Every actual wall or normal actor reaching a coarse-grid side belongs to that source port. -/

public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction Gadgets.Wires

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

theorem local_wall_collar_port (w : ℕ) (hw : 2 ≤ w) (code : CellPlan.Code) (c : PrimitiveCode)
    (hc : c ∈ FiniteSourceInventory.localCodes w code) (p : Cell (c.instanceOf w hw).width (c.instanceOf w hw).height)
    (hp : p ∈ (c.instanceOf w hw).board.walls) (face : Direction) (hf : InCollar w face (c.world w hw p)) :
    ∃ incoming, LocalPort code face incoming := by
  cases code with
  | none => simp [FiniteSourceInventory.localCodes] at hc
  | some code =>
    cases code with
    | inl g =>
      obtain ⟨role,_,hd⟩ := gate_wall_collar w hw g.2 c hc p hp face hf
      exact ⟨g.2.incoming.get role,role,hd,rfl⟩
    | inr q =>
      change c ∈ (wireSpec w q.2).codes at hc
      obtain ⟨i,hi,hc⟩ := List.mem_flatMap.mp hc
      have hi' := List.mem_range.mp hi
      rcases ((wireSpec w q.2).mem_block i c).mp hc with rfl | ⟨ht,rfl⟩
      · obtain ⟨u,hu,hnear⟩ := (wireSpec w q.2).line_wall_at w hw (wireSpec_geometry w q.2) i hi' p hp
        rcases wire_point_collar_location w q.2.1 i hi' face (w+1) (by unfold padding; omega) hu hnear hf with h | h
        · exact ⟨true,Or.inl ⟨rfl,h.2⟩⟩
        · exact ⟨false,Or.inr ⟨rfl,h.2⟩⟩
      · exact ((interior_not_collar w face (wire_turn_window_interior w hw q.2 i ht p)) hf).elim

theorem local_actor_collar_port (w : ℕ) (hw : 2 ≤ w) (code : CellPlan.Code) (c : PrimitiveCode)
    (hc : c ∈ FiniteSourceInventory.localCodes w code) (goal : Bool) (l : c.Labels w) (face : Direction)
    (hf : InCollar w face (c.actor w hw goal l)) : ∃ incoming, LocalPort code face incoming := by
  cases code with
  | none => simp [FiniteSourceInventory.localCodes] at hc
  | some code =>
    cases code with
    | inl g =>
      obtain ⟨role,hd,_⟩ := gate_actor_collar_bound w hw g.2 c hc goal l face hf
      exact ⟨g.2.incoming.get role,role,hd,rfl⟩
    | inr q =>
      rcases wire_actor_collar_bound w hw q.2 c hc goal l face hf with h | h
      · exact ⟨true,Or.inl ⟨rfl,h.1⟩⟩
      · exact ⟨false,Or.inr ⟨rfl,h.1⟩⟩

theorem local_actor_collar_band (w : ℕ) (hw : 2 ≤ w) (code : CellPlan.Code) (c : PrimitiveCode)
    (hc : c ∈ FiniteSourceInventory.localCodes w code) (goal : Bool) (l : c.Labels w) (face : Direction)
    (hf : InCollar w face (c.actor w hw goal l)) : PortBand w (w+1) face (c.actor w hw goal l) := by
  have h := local_actor_collar_lane w hw code c hc goal l face hf
  cases face <;> dsimp [PortBand,SameLane,Line.along,boundaryPoint] at h ⊢ <;> omega

end PushPuzzle.PushS.FiniteRouting
