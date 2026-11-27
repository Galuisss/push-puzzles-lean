/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceLineActualReadout
public import PushS.FiniteSourceTurnActualReadout
public import PushS.FiniteSourcePathSelections
public import PushS.FiniteSourceOrder

/-! The complete actual source path reader has no supplied normalized classifier or tool-correctness field. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory.PathSite

open PushFS PushFS.Reduction FiniteRouting
open PushFS.Gadgets.Wires.Soundness

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} {P : PathSpec}
    (s : PathSite w hw v P) (G : P.Geometry w) (E : s.Endpoints)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])

noncomputable def actualReadout : PathGlyph (slotMatching w hw v hP hT) w hw P :=
  s.readout G (admissible w hw v hP hT) (connected w hw v hP hT)
    (fun i => (s.line i).actualReadout (s.selection G E i) hP hT)
    (fun i hi => (s.turn G i hi).actualReadout hP hT)

theorem actual_signal (hne : 0 < P.segments.length)
    {S final : LabelledState (inventory w hw v).PhysicalLabel (width w v) (height w v)}
    (h : Successful (slotMatching w hw v hP hT) S final)
    (hin : ((s.actualReadout G E hP hT).line ⟨0,hne⟩).input.High S) (i : Fin P.segments.length) :
    ((s.actualReadout G E hP hT).line i).output.High S :=
  (s.actualReadout G E hP hT).signal G hne h (certificate w hw v hP hT) (ordered w hw v hP hT) hin i

end PushPuzzle.PushS.FiniteSourceInventory.PathSite
