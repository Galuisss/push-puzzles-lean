/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingGateHulls
public import PushS.FiniteRoutingPortBounds
public import PushS.FiniteRoutingTurnCenters

/-! Every complete normal-travel interval that reaches a macrocell collar has its actual port owner. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction Gadgets.Wires

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

private theorem hull_port_bound (w : ℕ) (face : Direction) (incoming : Bool) (a b p : ℕ × ℕ)
    (ha : PortOwnedBound w face incoming a) (hb : PortOwnedBound w face incoming b) (hp : Hull a b p) :
    PortOwnedBound w face incoming p := by
  cases face <;> cases incoming <;> dsimp [PortOwnedBound,Hull] at * <;> omega

private theorem gate_hull_collar (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (c : PrimitiveCode)
    (hc : c ∈ gateCodes w g) (l : c.Labels w) (a : ℕ × ℕ) (ha : ActorHull w hw c l a)
    (face : Direction) (hf : InCollar w face a) :
    ∃ role : Fin 3, PortAnnulus.outerDirection (g.pattern,g.rotation,role) = face ∧ PortOwnedBound w face (g.incoming.get role) a := by
  rw [gateCodes_eq_specs] at hc
  rcases List.mem_cons.mp hc with rfl | hc
  · obtain ⟨p,hp⟩ := actor_hull_cell w hw (.core g) l a ha
    exact ((interior_not_collar w face (hp ▸ core_window_interior w hw g p)) hf).elim
  · obtain ⟨role,_,hc⟩ := List.mem_flatMap.mp hc
    let P := armSpec w g role
    have G : P.Geometry w := armSpec_geometry w g role
    obtain ⟨i,hi,hc⟩ := List.mem_flatMap.mp hc
    have hi' := List.mem_range.mp hi
    change i < (armRoute w g role).length at hi'
    rcases (P.mem_block i c).mp hc with rfl | ⟨ht,rfl⟩
    · obtain ⟨u,hu,hnear⟩ := P.line_hull_at w hw G i hi' l a ha
      by_cases hn : i+1 < (armRoute w g role).length
      · exact ((interior_not_collar w face (nearby_interior w 1 (by unfold padding; omega)
          (armRoute_nonlast_interior w g role i hn hu) hnear)) hf).elim
      · have he : i = (armRoute w g role).length-1 := by omega
        subst i
        have hd := arm_last_collar_face w g role face 1 (by unfold padding; omega) hu hnear hf
        refine ⟨role,hd,?_⟩
        have hbound (goal : Bool) := line_finish_owned_bound w hw (gatePortLine w g role) (gatePortLine_good w g role)
          face (g.incoming.get role) ((armSpec_last_direction w g role).trans hd)
          (by simpa only [gatePortLine,←hd] using armSpec_last_finish w g role)
          (gatePortLine_last w g role) goal l
        exact hull_port_bound w face _ _ _ a (hbound false) (hbound true) ha
    · obtain ⟨p,hp⟩ := actor_hull_cell w hw (.turn (P.turn i)) l a ha
      exact ((interior_not_collar w face (hp ▸ arm_turn_window_interior w hw g role i ht p)) hf).elim

private theorem wire_hull_collar (w : ℕ) (hw : 2 ≤ w) (q : Catalog.Bitmap.Args) (c : PrimitiveCode)
    (hc : c ∈ wireCodes w q) (l : c.Labels w) (a : ℕ × ℕ) (ha : ActorHull w hw c l a)
    (face : Direction) (hf : InCollar w face a) :
    (face = (Catalog.sourceDirection q.1).opposite ∧ PortOwnedBound w face true a) ∨
      (face = Catalog.targetDirection q.1 ∧ PortOwnedBound w face false a) := by
  change c ∈ (wireSpec w q).codes at hc
  obtain ⟨i,hi,hc⟩ := List.mem_flatMap.mp hc
  have hi' := List.mem_range.mp hi
  rcases ((wireSpec w q).mem_block i c).mp hc with rfl | ⟨ht,rfl⟩
  · obtain ⟨u,hu,hnear⟩ := (wireSpec w q).line_hull_at w hw (wireSpec_geometry w q) i hi' l a ha
    rcases wire_point_collar_location w q.1 i hi' face 1 (by unfold padding; omega) hu hnear hf with h | h
    · rcases h with ⟨rfl,rfl⟩
      refine Or.inl ⟨rfl,?_⟩
      have hbound (goal : Bool) := line_start_owned_bound w hw _ ((wireSpec w q).line_good w (wireSpec_geometry w q) 0 hi')
        _ (by simpa only [Direction.opposite_opposite] using wire_first_direction w q) (wire_first_start w q) rfl goal l
      exact hull_port_bound w _ true _ _ a (hbound false) (hbound true) ha
    · rcases h with ⟨hlast,rfl⟩
      refine Or.inr ⟨rfl,?_⟩
      have hbound (goal : Bool) := line_finish_owned_bound w hw _ ((wireSpec w q).line_good w (wireSpec_geometry w q) i hi')
        _ false (wire_last_direction w q i hlast)
        (by simpa only [Bool.toNat_false,advance_zero] using wire_last_finish w q i hlast)
        (by simp only [wireSpec,PathSpec.line,lineCodeAt,ownsLast,hlast,ite_true,Bool.not_false]) goal l
      exact hull_port_bound w _ false _ _ a (hbound false) (hbound true) ha
  · obtain ⟨p,hp⟩ := actor_hull_cell w hw (.turn ((wireSpec w q).turn i)) l a ha
    exact ((interior_not_collar w face (hp ▸ wire_turn_window_interior w hw q i ht p)) hf).elim

theorem local_hull_collar (w : ℕ) (hw : 2 ≤ w) (code : CellPlan.Code) (c : PrimitiveCode)
    (hc : c ∈ FiniteSourceInventory.localCodes w code) (l : c.Labels w) (a : ℕ × ℕ) (ha : ActorHull w hw c l a)
    (face : Direction) (hf : InCollar w face a) :
    ∃ incoming, LocalPort code face incoming ∧ PortOwnedBound w face incoming a := by
  cases code with
  | none => simp [FiniteSourceInventory.localCodes] at hc
  | some code =>
    cases code with
    | inl g =>
      obtain ⟨role,hd,hbound⟩ := gate_hull_collar w hw g.2 c hc l a ha face hf
      exact ⟨g.2.incoming.get role,⟨role,hd,rfl⟩,hbound⟩
    | inr q =>
      rcases wire_hull_collar w hw q.2 c hc l a ha face hf with h | h
      · exact ⟨true,Or.inl ⟨rfl,h.1⟩,h.2⟩
      · exact ⟨false,Or.inr ⟨rfl,h.1⟩,h.2⟩

theorem local_hull_collar_lane (w : ℕ) (hw : 2 ≤ w) (code : CellPlan.Code) (c : PrimitiveCode)
    (hc : c ∈ FiniteSourceInventory.localCodes w code) (l : c.Labels w) (a : ℕ × ℕ) (ha : ActorHull w hw c l a)
    (face : Direction) (hf : InCollar w face a) :
    SameLane face (Line.along w face (boundaryPoint w face) 0) a := by
  cases c with
  | line d =>
    obtain ⟨hgood,hfirst⟩ := local_line_good w code d hc
    obtain ⟨n,_,hn,_,he⟩ := line_hull_bounds w hw d hgood hfirst l a ha
    rw [←LineCode.rowWorld_eq w hw d hgood n hn] at he
    rw [he]
    exact local_row_collar_lane w hw code d hc hgood n hn face (he ▸ hf)
  | core g =>
    obtain ⟨p,hp⟩ := actor_hull_cell w hw (.core g) l a ha
    exact ((interior_not_collar w face (hp ▸ core_window_interior w hw g p)) hf).elim
  | turn d =>
    obtain ⟨p,hp⟩ := actor_hull_cell w hw (.turn d) l a ha
    exact ((interior_not_collar w face (hp ▸ local_turn_window_interior w hw code d hc p)) hf).elim

end PushPuzzle.PushS.FiniteRouting
