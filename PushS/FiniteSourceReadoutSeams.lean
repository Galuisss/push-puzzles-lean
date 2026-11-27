/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceBoundaryReadout

/-! Actual neighboring source tiles share their physical label and literal high slot. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting Gadgets.Wires
open PushFS.Gadgets.Wires.Soundness

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source}

private theorem wire_wire_readout_seam {a b : Catalog.Bitmap.Args}
    (s : PathSite w hw v (wireSpec w a)) (t : PathSite w hw v (wireSpec w b))
    (E : s.Endpoints) (F : t.Endpoints) (hfirst : F.first = WireBoundary.outputIdentity s)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (hn : neighbor (Catalog.targetDirection a.1) s.location = some t.location)
    (hd : Catalog.sourceDirection b.1 = Catalog.targetDirection a.1) :
    s.lastPort (wireSpec_geometry w a) E hP hT WireBoundary.length_pos =
      t.firstPort (wireSpec_geometry w b) F hP hT WireBoundary.length_pos := by
  apply PhysicalPort.ext_coordinates
  · exact (WireBoundary.lastPort_label s E hP hT).trans
      (hfirst.symm.trans (WireBoundary.firstPort_label t F hP hT).symm)
  · rw [WireBoundary.lastPort_slot,WireBoundary.firstPort_slot,hd]
    exact macro_boundary_phase _ _ _ true hn
  · rw [WireBoundary.lastPort_direction,WireBoundary.firstPort_direction,hd]

theorem gate_wire_readout_seam {g : GateTileState} {role : Fin 3} {a : Catalog.Bitmap.Args}
    (s : PathSite w hw v (armSpec w g role)) (t : PathSite w hw v (wireSpec w a))
    (E : s.Endpoints) (F : t.Endpoints) (hin : g.incoming.get role = false)
    (hfirst : F.first = ArmBoundary.outputIdentity s hin)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (hn : neighbor (PortAnnulus.outerDirection (g.pattern,g.rotation,role)) s.location = some t.location)
    (hd : Catalog.sourceDirection a.1 = PortAnnulus.outerDirection (g.pattern,g.rotation,role)) :
    s.lastPort (armSpec_geometry w g role) E hP hT ArmBoundary.length_pos =
      t.firstPort (wireSpec_geometry w a) F hP hT WireBoundary.length_pos := by
  apply PhysicalPort.ext_coordinates
  · exact (ArmBoundary.lastPort_output_label s E hP hT hin).trans
      (hfirst.symm.trans (WireBoundary.firstPort_label t F hP hT).symm)
  · rw [ArmBoundary.lastPort_slot,WireBoundary.firstPort_slot,hin,hd]
    exact macro_boundary_phase _ _ _ true hn
  · rw [ArmBoundary.lastPort_direction,WireBoundary.firstPort_direction,hd]

private theorem boundary_high_adjacent {W H : ℕ} (w : ℕ) (pos : ℕ × ℕ) (d : Direction)
    (low high : Cell W H)
    (hl : coordinates low = macroShift w pos (boundarySlot w d false false))
    (hh : coordinates high = macroShift w pos (boundarySlot w d false true)) : Adjacent d low high := by
  have hxl := congrArg Prod.fst hl
  have hyl := congrArg Prod.snd hl
  have hxh := congrArg Prod.fst hh
  have hyh := congrArg Prod.snd hh
  have hpad : 0 < padding w := by unfold padding; omega
  cases d <;> simp only [Adjacent,Fin.ext_iff]
  all_goals
    dsimp [coordinates,macroShift,boundarySlot,boundaryPoint,Line.along] at hxl hyl hxh hyh
    constructor <;> omega

/-- At a consuming seam the two literal high slots are neighboring, with opposite route directions. -/
theorem wire_gate_ports_exclusive {g : GateTileState} {role : Fin 3} {a : Catalog.Bitmap.Args}
    (s : PathSite w hw v (wireSpec w a)) (t : PathSite w hw v (armSpec w g role))
    (E : s.Endpoints) (F : t.Endpoints) (hin : g.incoming.get role = true)
    (hfinal : ∀ hk, F.final hk = WireBoundary.outputIdentity s)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (hn : neighbor (Catalog.targetDirection a.1) s.location = some t.location)
    (hd : PortAnnulus.outerDirection (g.pattern,g.rotation,role) = (Catalog.targetDirection a.1).opposite)
    (S : LabelledState (inventory w hw v).PhysicalLabel (width w v) (height w v)) :
    ¬((s.lastPort (wireSpec_geometry w a) E hP hT WireBoundary.length_pos).High S ∧
      (t.lastPort (armSpec_geometry w g role) F hP hT ArmBoundary.length_pos).High S) := by
  apply PhysicalPort.exclusive_of_opposite
  · exact (WireBoundary.lastPort_label s E hP hT).trans
      ((ArmBoundary.lastPort_input_label t F hP hT hin).trans (hfinal _)).symm
  · rw [WireBoundary.lastPort_direction,ArmBoundary.lastPort_direction,hd]
  · rw [WireBoundary.lastPort_direction]
    apply boundary_high_adjacent w s.location (Catalog.targetDirection a.1)
    · rw [ArmBoundary.lastPort_slot,hin,hd]
      exact (macro_boundary_phase _ _ _ false hn).symm
    · exact WireBoundary.lastPort_slot s E hP hT

theorem wire_wire_readout_signal {a b : Catalog.Bitmap.Args}
    (s : PathSite w hw v (wireSpec w a)) (t : PathSite w hw v (wireSpec w b))
    (E : s.Endpoints) (F : t.Endpoints) (hfirst : F.first = WireBoundary.outputIdentity s)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (hn : neighbor (Catalog.targetDirection a.1) s.location = some t.location)
    (hd : Catalog.sourceDirection b.1 = Catalog.targetDirection a.1)
    {S final : LabelledState (inventory w hw v).PhysicalLabel (width w v) (height w v)}
    (h : Successful (slotMatching w hw v hP hT) S final)
    (hin : (s.firstPort (wireSpec_geometry w a) E hP hT WireBoundary.length_pos).High S) :
    (t.firstPort (wireSpec_geometry w b) F hP hT WireBoundary.length_pos).High S := by
  have hs := s.ports_signal (wireSpec_geometry w a) E hP hT WireBoundary.length_pos h hin
  exact wire_wire_readout_seam s t E F hfirst hP hT hn hd ▸ hs

end PushPuzzle.PushS.FiniteSourceInventory
