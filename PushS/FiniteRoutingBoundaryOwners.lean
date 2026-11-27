/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingCoreOwners
public import PushS.FiniteRoutingPortBounds

/-! Every actual used source port has a literal low-slot interior chart owner. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction Gadgets.Wires

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

private theorem LineCode.last_low_owner (w : ℕ) (hw : 2 ≤ w) (c : LineCode)
    (hc : LineGood w c.segment)
    (codes : List PrimitiveCode) (hm : .line c ∈ codes) :
    WorldOwner w hw codes (c.lastWorld w hw false) (Line.orientedRailName w (segmentDirection c.segment)).level := by
  have hn0 : 0 < segmentLength c.segment := by have h := hc.2.1; omega
  refine ⟨.line c,hm,c.railPoint w hw hc _ (le_refl _),?_,c.railPoint_owner w hw hc _ hn0 (le_refl _)⟩
  rw [LineCode.railPoint_world,LineCode.lastWorld_eq w hw c hc]
  simpa only [Bool.toNat_false,Nat.add_zero] using along_finish w _ c.segment.start c.segment.finish
    (segmentLength c.segment) false (segment_travels c.segment hc.1)

private theorem LineCode.first_high_owner (w : ℕ) (hw : 2 ≤ w) (c : LineCode)
    (hc : LineGood w c.segment)
    (codes : List PrimitiveCode) (hm : .line c ∈ codes) :
    WorldOwner w hw codes (c.firstWorld w hw true) (Line.orientedRailName w (segmentDirection c.segment)).level := by
  have hn : 1 ≤ segmentLength c.segment := by have h := hc.2.1; omega
  refine ⟨.line c,hm,c.railPoint w hw hc 1 hn,?_,c.railPoint_owner w hw hc 1 (by decide) hn⟩
  rw [LineCode.railPoint_world,LineCode.firstWorld_eq w hw c hc]
  rfl

private theorem gate_boundary_low_owner (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (role : Fin 3) :
    WorldOwner w hw (gateCodes w g)
      (boundarySlot w (PortAnnulus.outerDirection (g.pattern,g.rotation,role)) (g.incoming.get role) false)
      (Line.orientedRailName w (PortAnnulus.outerDirection (g.pattern,g.rotation,role))).level := by
  have hi : (armRoute w g role).length-1 < (armRoute w g role).length := by rw [armRoute_length,route_length]; omega
  have h := LineCode.last_low_owner w hw (gatePortLine w g role) (gatePortLine_good w g role) (gateCodes w g)
    (arm_code_mem_gateCodes w g role _ ((armSpec w g role).line_mem_codes _ hi))
  simpa only [gatePortLine,armSpec_last_slot,armSpec_last_direction] using h

private theorem wire_input_boundary_low_owner (w : ℕ) (hw : 2 ≤ w) (q : Catalog.Bitmap.Args) :
    WorldOwner w hw (wireCodes w q)
      (boundarySlot w (Catalog.sourceDirection q.1).opposite true false)
      (Line.orientedRailName w (Catalog.sourceDirection q.1).opposite).level := by
  have hi : 0 < (wireRoute w q.1).length := by rw [wireRoute_length]; split_ifs <;> decide
  have hc := (wireSpec w q).line_good w (wireSpec_geometry w q) 0 hi
  have hm : .line ((wireSpec w q).line 0) ∈ wireCodes w q := (wireSpec w q).line_mem_codes 0 hi
  have h := LineCode.first_high_owner w hw _ hc (wireCodes w q) hm
  have hworld : ((wireSpec w q).line 0).firstWorld w hw true =
      boundarySlot w (Catalog.sourceDirection q.1).opposite true false := by
    rw [LineCode.firstWorld_eq w hw _ hc,wire_first_direction,wire_first_start]
    simpa only [Direction.opposite_opposite,Bool.not_true] using
      wire_input_slot w (Catalog.sourceDirection q.1).opposite true
  have hlevel : (Line.orientedRailName w (Catalog.sourceDirection q.1)).level =
      (Line.orientedRailName w (Catalog.sourceDirection q.1).opposite).level := by
    cases q.1 <;> rfl
  simpa only [wire_first_direction,hworld,hlevel] using h

private theorem wire_output_boundary_low_owner (w : ℕ) (hw : 2 ≤ w) (q : Catalog.Bitmap.Args) :
    WorldOwner w hw (wireCodes w q) (boundarySlot w (Catalog.targetDirection q.1) false false)
      (Line.orientedRailName w (Catalog.targetDirection q.1)).level := by
  let i := (wireRoute w q.1).length-1
  have hpos : 0 < (wireRoute w q.1).length := by rw [wireRoute_length]; split_ifs <;> decide
  have hi : i < (wireRoute w q.1).length := by dsimp [i]; omega
  have hil : i+1 = (wireRoute w q.1).length := by dsimp [i]; omega
  have hc := (wireSpec w q).line_good w (wireSpec_geometry w q) i hi
  have hm : .line ((wireSpec w q).line i) ∈ wireCodes w q := (wireSpec w q).line_mem_codes i hi
  have h := LineCode.last_low_owner w hw _ hc (wireCodes w q) hm
  have hworld : ((wireSpec w q).line i).lastWorld w hw false = boundarySlot w (Catalog.targetDirection q.1) false false := by
    rw [LineCode.lastWorld_eq w hw _ hc,wire_last_direction w q i hil,wire_last_finish w q i hil]
    rfl
  simpa only [wire_last_direction w q i hil,hworld] using h

theorem local_port_low_owner (w : ℕ) (hw : 2 ≤ w) (code : CellPlan.Code) (face : Direction) (incoming : Bool)
    (hp : LocalPort code face incoming) :
    WorldOwner w hw (FiniteSourceInventory.localCodes w code) (boundarySlot w face incoming false)
      (Line.orientedRailName w face).level := by
  cases code with
  | none => exact hp.elim
  | some code =>
    cases code with
    | inl g =>
      obtain ⟨role,hd,hi⟩ := hp
      rw [←hd,←hi]
      exact gate_boundary_low_owner w hw g.2 role
    | inr q =>
      rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact wire_input_boundary_low_owner w hw q.2
      · exact wire_output_boundary_low_owner w hw q.2

end PushPuzzle.PushS.FiniteRouting
