/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingRowClearance
public import PushS.FiniteRoutingGateCollars
public import PushS.FiniteRoutingWireCollars
public import PushS.FiniteSourceInventory

/-! Actual complete static line rows avoid every local gate or wire wall. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction Gadgets.Wires

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

theorem PathSpec.line_code_origin (P : PathSpec) (c : LineCode) (hc : .line c ∈ P.codes) :
    ∃ i, i < P.segments.length ∧ c = P.line i := by
  obtain ⟨i,hi,hc⟩ := List.mem_flatMap.mp hc
  rcases (P.mem_block i (.line c)).mp hc with he | ⟨_,he⟩
  · exact ⟨i,List.mem_range.mp hi,PrimitiveCode.line.inj he⟩
  · cases he

theorem gate_line_origin (w : ℕ) (g : GateTileState) (c : LineCode) (hc : .line c ∈ gateCodes w g) :
    ∃ (role : Fin 3) (i : ℕ), i < (armRoute w g role).length ∧ c = (armSpec w g role).line i := by
  rw [gateCodes_eq_specs] at hc
  rcases List.mem_cons.mp hc with hc | hc
  · cases hc
  · obtain ⟨role,_,hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨i,hi,he⟩ := (armSpec w g role).line_code_origin c hc
    exact ⟨role,i,hi,he⟩

private theorem gate_row_wall_clear (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (c : LineCode)
    (hc : .line c ∈ gateCodes w g) (hgood : LineGood w c.segment)
    (n : ℕ) (hn : n ≤ segmentLength c.segment+1) (d : PrimitiveCode) (hd : d ∈ gateCodes w g)
    (p : Cell (d.instanceOf w hw).width (d.instanceOf w hw).height) (hp : p ∈ (d.instanceOf w hw).board.walls) :
    c.rowWorld w hw hgood n hn ≠ d.world w hw p := by
  obtain ⟨role,i,hi,rfl⟩ := gate_line_origin w g c hc
  let P := armSpec w g role
  have G : P.Geometry w := armSpec_geometry w g role
  obtain ⟨u,hu,ha⟩ := P.line_row_at w hw G i hi n hn
  rw [gateCodes_eq_specs] at hd
  rcases List.mem_cons.mp hd with rfl | hd
  · by_cases hz : i = 0
    · subst i
      rw [LineCode.rowWorld_eq,armSpec_first_direction,armSpec_first_start]
      exact Ne.symm (core_wall_ne_ray w hw g role n p hp)
    · exact core_tail_ne w hw g role 1 (by unfold FiniteGeometry.origin; omega)
        ⟨_,P.segment_mem_tail i hi (by omega),hu⟩ ha p
  · obtain ⟨other,_,hd⟩ := List.mem_flatMap.mp hd
    by_cases he : role = other
    · subst other
      exact P.row_codes_wall_clear w hw G i hi n hn d hd p hp
    · rcases (armSpec w g other).code_wall_trace w hw (armSpec_geometry w g other) d hd p hp with h | h
      · obtain ⟨v,hv,hb⟩ := h
        apply footprint_ne (w := w) (m := 1) (n := w+1) _ ha hb
        intro hnear
        exact armRoutes_separated_wide w g he ⟨_,P.segment_mem i hi,hu⟩ hv (nearby_of_le (by omega) hnear)
      · obtain ⟨v,hv,hb⟩ := h
        apply Ne.symm
        apply footprint_ne (w := w) (m := FiniteTools.radius w) (n := 1) _ hb ha
        intro hnear
        exact armRoute_tail_separated w g (Ne.symm he) hv ⟨_,P.segment_mem i hi,hu⟩
          (nearby_of_le (by unfold FiniteTools.radius FiniteGeometry.origin; omega) hnear)

private theorem wire_row_wall_clear (w : ℕ) (hw : 2 ≤ w) (q : Catalog.Bitmap.Args) (c : LineCode)
    (hc : .line c ∈ wireCodes w q) (hgood : LineGood w c.segment)
    (n : ℕ) (hn : n ≤ segmentLength c.segment+1) (d : PrimitiveCode) (hd : d ∈ wireCodes w q)
    (p : Cell (d.instanceOf w hw).width (d.instanceOf w hw).height) (hp : p ∈ (d.instanceOf w hw).board.walls) :
    c.rowWorld w hw hgood n hn ≠ d.world w hw p := by
  obtain ⟨i,hi,rfl⟩ := (wireSpec w q).line_code_origin c hc
  exact (wireSpec w q).row_codes_wall_clear w hw (wireSpec_geometry w q) i hi n hn d hd p hp

theorem local_row_wall_clear (w : ℕ) (hw : 2 ≤ w) (code : CellPlan.Code) (c : LineCode)
    (hc : .line c ∈ FiniteSourceInventory.localCodes w code) (hgood : LineGood w c.segment)
    (n : ℕ) (hn : n ≤ segmentLength c.segment+1) (d : PrimitiveCode)
    (hd : d ∈ FiniteSourceInventory.localCodes w code)
    (p : Cell (d.instanceOf w hw).width (d.instanceOf w hw).height) (hp : p ∈ (d.instanceOf w hw).board.walls) :
    c.rowWorld w hw hgood n hn ≠ d.world w hw p := by
  cases code with
  | none => simp [FiniteSourceInventory.localCodes] at hc
  | some code =>
    cases code with
    | inl g => exact gate_row_wall_clear w hw g.2 c hc hgood n hn d hd p hp
    | inr q => exact wire_row_wall_clear w hw q.2 c hc hgood n hn d hd p hp

theorem line_endpoint_row_lane (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (face : Direction) (incoming : Bool) (hd : segmentDirection c.segment = face)
    (he : c.segment.finish = advance face.opposite (boundaryPoint w face) incoming.toNat)
    (n : ℕ) (hn : n ≤ segmentLength c.segment+1) :
    SameLane face (Line.along w face (boundaryPoint w face) 0) (c.rowWorld w hw hc n hn) := by
  rw [LineCode.rowWorld_eq,hd]
  have ht := segment_travels c.segment hc.1
  rw [hd,he] at ht
  cases face <;> dsimp [SameLane,Travels,advance,Line.along,Direction.opposite,boundaryPoint] at * <;> omega

private theorem gate_row_collar_lane (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (c : LineCode)
    (hc : .line c ∈ gateCodes w g) (hgood : LineGood w c.segment) (n : ℕ) (hn : n ≤ segmentLength c.segment+1)
    (face : Direction) (hf : InCollar w face (c.rowWorld w hw hgood n hn)) :
    SameLane face (Line.along w face (boundaryPoint w face) 0) (c.rowWorld w hw hgood n hn) := by
  obtain ⟨role,i,hi,rfl⟩ := gate_line_origin w g c hc
  let P := armSpec w g role
  have G : P.Geometry w := armSpec_geometry w g role
  obtain ⟨u,hu,ha⟩ := P.line_row_at w hw G i hi n hn
  by_cases hnext : i+1 < (armRoute w g role).length
  · have hinner := nearby_interior w 1 (by unfold padding; omega) (armRoute_nonlast_interior w g role i hnext hu) ha
    exact ((interior_not_collar w face hinner) hf).elim
  · have hiz : i = (armRoute w g role).length-1 := by omega
    subst i
    have hface := arm_last_collar_face w g role face 1 (by unfold padding; omega) hu ha hf
    apply line_endpoint_row_lane w hw _ hgood face (g.incoming.get role) _ _ n hn
    · exact (armSpec_last_direction w g role).trans hface
    · simpa only [←hface] using armSpec_last_finish w g role

private theorem centered_row_collar_lane (w : ℕ) (hw : 2 ≤ w) (c : LineCode)
    (hc : LineGood w c.segment)
    (hcenter : CenteredLine w c.segment) (n : ℕ) (hn : n ≤ segmentLength c.segment+1)
    (face : Direction) (hf : InCollar w face (c.rowWorld w hw hc n hn)) :
    SameLane face (Line.along w face (boundaryPoint w face) 0) (c.rowWorld w hw hc n hn) := by
  rw [LineCode.rowWorld_eq] at hf ⊢
  have ht := segment_travels c.segment hc.1
  have hl := hc.2.1
  cases hd : segmentDirection c.segment <;> cases face <;> simp only [hd] at hf ht ⊢ <;>
    dsimp [CenteredLine,SameLane,Line.along,InCollar,Travels,boundaryPoint] at * <;>
    simp only [tileStride,spacing,padding] at * <;> omega

private theorem wire_row_collar_lane (w : ℕ) (hw : 2 ≤ w) (q : Catalog.Bitmap.Args) (c : LineCode)
    (hc : .line c ∈ wireCodes w q) (hgood : LineGood w c.segment) (n : ℕ) (hn : n ≤ segmentLength c.segment+1)
    (face : Direction) (hf : InCollar w face (c.rowWorld w hw hgood n hn)) :
    SameLane face (Line.along w face (boundaryPoint w face) 0) (c.rowWorld w hw hgood n hn) := by
  obtain ⟨i,hi,rfl⟩ := (wireSpec w q).line_code_origin c hc
  exact centered_row_collar_lane w hw _ hgood (wire_line_centered w q i hi) n hn face hf

theorem local_row_collar_lane (w : ℕ) (hw : 2 ≤ w) (code : CellPlan.Code) (c : LineCode)
    (hc : .line c ∈ FiniteSourceInventory.localCodes w code) (hgood : LineGood w c.segment)
    (n : ℕ) (hn : n ≤ segmentLength c.segment+1) (face : Direction)
    (hf : InCollar w face (c.rowWorld w hw hgood n hn)) :
    SameLane face (Line.along w face (boundaryPoint w face) 0) (c.rowWorld w hw hgood n hn) := by
  cases code with
  | none => simp [FiniteSourceInventory.localCodes] at hc
  | some code =>
    cases code with
    | inl g => exact gate_row_collar_lane w hw g.2 c hc hgood n hn face hf
    | inr q => exact wire_row_collar_lane w hw q.2 c hc hgood n hn face hf

theorem local_line_good (w : ℕ) (code : CellPlan.Code) (c : LineCode)
    (hc : .line c ∈ FiniteSourceInventory.localCodes w code) : LineGood w c.segment ∧ c.first = false := by
  cases code with
  | none => simp [FiniteSourceInventory.localCodes] at hc
  | some code =>
    cases code with
    | inl g =>
      obtain ⟨role,i,hi,rfl⟩ := gate_line_origin w g.2 c hc
      exact ⟨(armSpec w g.2 role).line_good w (armSpec_geometry w g.2 role) i hi,rfl⟩
    | inr q =>
      obtain ⟨i,hi,rfl⟩ := (wireSpec w q.2).line_code_origin c hc
      exact ⟨(wireSpec w q.2).line_good w (wireSpec_geometry w q.2) i hi,rfl⟩

end PushPuzzle.PushS.FiniteRouting
