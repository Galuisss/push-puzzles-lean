/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingGateRows
public import PushS.FiniteRoutingPortBounds
public import PushS.FiniteRoutingMacroContacts
public import PushS.FiniteRoutingCoreOwners

/-! Source-port support caps agree with actual interior working-row cells of the adjacent tile. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction Gadgets.Wires

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

def boundaryCap (w : ℕ) (d : Direction) (incoming : Bool) : ℕ × ℕ :=
  Line.along w d (if incoming then advance d.opposite (boundaryPoint w d) 1 else boundaryPoint w d) 2

def boundaryInnerSupport (w : ℕ) (d : Direction) (incoming : Bool) : ℕ × ℕ :=
  Line.along w d.opposite (boundaryPoint w d) (incoming.toNat+1)

theorem boundary_cap_seam (w : ℕ) (d : Direction) (p r : ℕ × ℕ) (incoming : Bool)
    (hn : PushFS.Reduction.neighbor d p = some r) :
    macroShift w p (boundaryCap w d incoming) =
      macroShift w r (boundaryInnerSupport w d.opposite (!incoming)) := by
  have ht := macro_neighbor_travels w d p r hn
  cases d <;> cases incoming <;> apply Prod.ext <;>
    dsimp [macroShift,boundaryCap,boundaryInnerSupport,Line.along,boundaryPoint,advance,
      Direction.opposite,Travels] at * <;> (try simp only [Bool.not_false,Bool.not_true,Bool.toNat_false,Bool.toNat_true] at *) <;>
    unfold tileStride spacing padding at * <;> omega

private theorem LineCode.row_before_finish (w : ℕ) (hw : 2 ≤ w) (c : LineCode)
    (hc : LineGood w c.segment) :
    c.rowWorld w hw hc (segmentLength c.segment-1) (by omega) =
      Line.along w (segmentDirection c.segment).opposite c.segment.finish 1 := by
  rw [LineCode.rowWorld_eq]
  have ht := segment_travels c.segment hc.1
  have hl := hc.2.1
  cases hd : segmentDirection c.segment <;> simp only [hd] at ht ⊢ <;>
    dsimp [Travels,Line.along,Direction.opposite] at ht ⊢ <;>
    apply Prod.ext <;> unfold padding <;> omega

private theorem gate_inner_support_row (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (role : Fin 3) :
    ∃ (c : LineCode) (_hc : .line c ∈ gateCodes w g) (hgood : LineGood w c.segment)
      (n : ℕ) (hn : n ≤ segmentLength c.segment+1),
      c.rowWorld w hw hgood n hn =
        boundaryInnerSupport w (PortAnnulus.outerDirection (g.pattern,g.rotation,role)) (g.incoming.get role) := by
  let c := gatePortLine w g role
  have hi : (armRoute w g role).length-1 < (armRoute w g role).length := by rw [armRoute_length,route_length]; omega
  have hc : .line c ∈ gateCodes w g := arm_code_mem_gateCodes w g role _ ((armSpec w g role).line_mem_codes _ hi)
  refine ⟨c,hc,gatePortLine_good w g role,segmentLength c.segment-1,by omega,?_⟩
  rw [LineCode.row_before_finish]
  change Line.along w (segmentDirection ((armSpec w g role).line ((armRoute w g role).length-1)).segment).opposite
    ((armSpec w g role).line ((armRoute w g role).length-1)).segment.finish 1 = _
  rw [armSpec_last_direction,armSpec_last_finish]
  cases hd : PortAnnulus.outerDirection (g.pattern,g.rotation,role) <;> cases hb : g.incoming.get role <;>
    dsimp [boundaryInnerSupport,Line.along,advance,Direction.opposite,boundaryPoint] <;>
    apply Prod.ext <;> unfold tileStride spacing padding <;> omega

private theorem wire_input_inner_support_row (w : ℕ) (hw : 2 ≤ w) (q : Catalog.Bitmap.Args) :
    ∃ (c : LineCode) (_hc : .line c ∈ wireCodes w q) (hgood : LineGood w c.segment)
      (n : ℕ) (hn : n ≤ segmentLength c.segment+1),
      c.rowWorld w hw hgood n hn = boundaryInnerSupport w (Catalog.sourceDirection q.1).opposite true := by
  have hi : 0 < (wireRoute w q.1).length := by rw [wireRoute_length]; split_ifs <;> decide
  let c := (wireSpec w q).line 0
  have hg : LineGood w c.segment := (wireSpec w q).line_good w (wireSpec_geometry w q) 0 hi
  refine ⟨c,(wireSpec w q).line_mem_codes 0 hi,hg,2,by have h := hg.2.1; omega,?_⟩
  rw [LineCode.rowWorld_eq,wire_first_direction,wire_first_start]
  simp [boundaryInnerSupport]

private theorem wire_output_inner_support_row (w : ℕ) (hw : 2 ≤ w) (q : Catalog.Bitmap.Args) :
    ∃ (c : LineCode) (_hc : .line c ∈ wireCodes w q) (hgood : LineGood w c.segment)
      (n : ℕ) (hn : n ≤ segmentLength c.segment+1),
      c.rowWorld w hw hgood n hn = boundaryInnerSupport w (Catalog.targetDirection q.1) false := by
  let i := (wireRoute w q.1).length-1
  have hpos : 0 < (wireRoute w q.1).length := by rw [wireRoute_length]; split_ifs <;> decide
  have hi : i < (wireRoute w q.1).length := by dsimp [i]; omega
  have hil : i+1 = (wireRoute w q.1).length := by dsimp [i]; omega
  let c := (wireSpec w q).line i
  have hg : LineGood w c.segment := (wireSpec w q).line_good w (wireSpec_geometry w q) i hi
  refine ⟨c,(wireSpec w q).line_mem_codes i hi,hg,segmentLength c.segment-1,by omega,?_⟩
  rw [LineCode.row_before_finish,wire_last_direction w q i hil,wire_last_finish w q i hil]
  rfl

theorem local_port_inner_support_row (w : ℕ) (hw : 2 ≤ w) (code : CellPlan.Code) (face : Direction) (incoming : Bool)
    (hp : LocalPort code face incoming) :
    ∃ (c : LineCode) (_hc : .line c ∈ FiniteSourceInventory.localCodes w code) (hgood : LineGood w c.segment)
      (n : ℕ) (hn : n ≤ segmentLength c.segment+1),
      c.rowWorld w hw hgood n hn = boundaryInnerSupport w face incoming := by
  cases code with
  | none => exact hp.elim
  | some code =>
    cases code with
    | inl g =>
      obtain ⟨role,hd,hi⟩ := hp
      rw [←hd,←hi]
      exact gate_inner_support_row w hw g.2 role
    | inr q =>
      rcases hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact wire_input_inner_support_row w hw q.2
      · exact wire_output_inner_support_row w hw q.2

end PushPuzzle.PushS.FiniteRouting
