/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourcePathPortSlots
public import PushS.FiniteSourceGateBoundarySlots
public import PushS.FiniteRoutingPortExclusion

/-! Literal first and final readout ports of the actual emitted wire and arm programs. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting Gadgets.Wires
open PushFS.Gadgets.Wires.Soundness

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source}

attribute [local irreducible] codes width height InventoryAssembly.board InventoryAssembly.walls

namespace PathSite

variable {P : PathSpec} (s : PathSite w hw v P) (G : P.Geometry w) (E : s.Endpoints)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])

/-- The final actual line index of a nonempty source path. -/
@[expose]
def readoutLastIndex (hne : 0 < P.segments.length) : Fin P.segments.length :=
  ⟨P.segments.length-1,Nat.sub_lt hne (by decide)⟩

/-- The actual physical input port of the first emitted line. -/
@[expose]
noncomputable def firstPort (hne : 0 < P.segments.length) :
    PhysicalPort (I := checkedPuzzle w hw v hP hT) (GlobalLabel := (inventory w hw v).PhysicalLabel) :=
  ((s.actualReadout G E hP hT).line ⟨0,hne⟩).input

/-- The actual physical output port of the last emitted line. -/
@[expose]
noncomputable def lastPort (hne : 0 < P.segments.length) :
    PhysicalPort (I := checkedPuzzle w hw v hP hT) (GlobalLabel := (inventory w hw v).PhysicalLabel) :=
  ((s.actualReadout G E hP hT).line (readoutLastIndex hne)).output

theorem ports_signal (hne : 0 < P.segments.length)
    {S final : LabelledState (inventory w hw v).PhysicalLabel (width w v) (height w v)}
    (h : Successful (slotMatching w hw v hP hT) S final) (hin : (s.firstPort G E hP hT hne).High S) :
    (s.lastPort G E hP hT hne).High S := s.actual_signal G E hP hT hne h hin _

private theorem lastPort_owned_label (hk : P.keepEndpoint = true) (hne : 0 < P.segments.length) :
    (s.lastPort G E hP hT hne).label = s.finalIdentity (readoutLastIndex hne) (by dsimp [readoutLastIndex]; omega) hk := by
  apply (admissible w hw v hP hT).source_injective
  apply boundaryCell_ext
  have hl := (s.actualReadout G E hP hT).line_source_output (readoutLastIndex hne)
  have hr := congrArg (@coordinates (width w v) (height w v))
    ((s.line (readoutLastIndex hne)).source_finalLabel (s.final_owned _ (by dsimp [readoutLastIndex]; omega) hk))
  rw [(s.line (readoutLastIndex hne)).actual_last_coordinates,s.line_location] at hr
  exact hl.trans hr.symm

end PathSite

namespace WireBoundary

variable {a : Catalog.Bitmap.Args} (s : PathSite w hw v (wireSpec w a)) (E : s.Endpoints)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])

theorem firstPort_label : (s.firstPort (wireSpec_geometry w a) E hP hT length_pos).label = E.first :=
  s.actual_input_label (wireSpec_geometry w a) E hP hT length_pos

theorem lastPort_label : (s.lastPort (wireSpec_geometry w a) E hP hT length_pos).label = outputIdentity s :=
  s.lastPort_owned_label (wireSpec_geometry w a) E hP hT rfl length_pos

theorem firstPort_slot : coordinates (s.firstPort (wireSpec_geometry w a) E hP hT length_pos).slot =
    macroShift w s.location (boundarySlot w (Catalog.sourceDirection a.1).opposite true false) := by
  have hl := (s.actualReadout (wireSpec_geometry w a) E hP hT).line_input_slot ⟨0,length_pos⟩ true
  have hr := (s.line ⟨0,length_pos⟩).actual_first_coordinates true
  rw [s.line_location] at hr
  exact hl.trans (hr.symm.trans (first_coordinates s true length_pos))

theorem lastPort_slot : coordinates (s.lastPort (wireSpec_geometry w a) E hP hT length_pos).slot =
    macroShift w s.location (boundarySlot w (Catalog.targetDirection a.1) false true) := by
  have hl := (s.actualReadout (wireSpec_geometry w a) E hP hT).line_output_slot lastIndex true
  refine hl.trans (congrArg (macroShift w s.location) ?_)
  rw [LineCode.lastWorld_eq w hw _ ((wireSpec w a).line_good w (wireSpec_geometry w a) _ lastIndex.isLt),
    wire_last_direction w a _ lastIndex_final,wire_last_finish w a _ lastIndex_final]
  rfl

theorem firstPort_direction : (s.firstPort (wireSpec_geometry w a) E hP hT length_pos).direction = Catalog.sourceDirection a.1 :=
  ((s.actualReadout (wireSpec_geometry w a) E hP hT).line_direction ⟨0,length_pos⟩).trans (wire_first_direction w a)

theorem lastPort_direction : (s.lastPort (wireSpec_geometry w a) E hP hT length_pos).direction = Catalog.targetDirection a.1 :=
  ((s.actualReadout (wireSpec_geometry w a) E hP hT).line_direction lastIndex).trans (wire_last_direction w a _ lastIndex_final)

end WireBoundary

namespace ArmBoundary

variable {g : GateTileState} {role : Fin 3} (s : PathSite w hw v (armSpec w g role)) (E : s.Endpoints)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])

theorem lastPort_slot : coordinates (s.lastPort (armSpec_geometry w g role) E hP hT length_pos).slot =
    macroShift w s.location (boundarySlot w (PortAnnulus.outerDirection (g.pattern,g.rotation,role))
      (g.incoming.get role) true) := by
  have hl := (s.actualReadout (armSpec_geometry w g role) E hP hT).line_output_slot lastIndex true
  have hr := (s.line lastIndex).actual_last_coordinates true
  rw [s.line_location] at hr
  exact hl.trans (hr.symm.trans (last_coordinates s _ lastIndex_final true))

theorem lastPort_direction : (s.lastPort (armSpec_geometry w g role) E hP hT length_pos).direction =
    PortAnnulus.outerDirection (g.pattern,g.rotation,role) :=
  ((s.actualReadout (armSpec_geometry w g role) E hP hT).line_direction lastIndex).trans (armSpec_last_direction w g role)

theorem lastPort_output_label (hin : g.incoming.get role = false) :
    (s.lastPort (armSpec_geometry w g role) E hP hT length_pos).label = outputIdentity s hin :=
  s.lastPort_owned_label (armSpec_geometry w g role) E hP hT (by simp only [armSpec,hin,Bool.not_false]) length_pos

theorem lastPort_input_label (hin : g.incoming.get role = true) :
    (s.lastPort (armSpec_geometry w g role) E hP hT length_pos).label = E.final (by simp only [armSpec,hin,Bool.not_true]) :=
  s.actual_output_label (armSpec_geometry w g role) E hP hT (by simp only [armSpec,hin,Bool.not_true]) lastIndex lastIndex_final

end ArmBoundary
end PushPuzzle.PushS.FiniteSourceInventory
