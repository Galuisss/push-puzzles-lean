/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalRephase
public import PushFS.Reduction.PhysicalInventory

/-! Actual complete canonical states for intermediate source orientations, retaining the fixed target assignment. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory


open Cslib.Complexity.NCL PhysicalBitmap

def assignment (v : CellPlan.Source) (bits : List Bool) : CellPlan.Source := (v.1,(bits,v.2.2))

/-- The actual complete physical box set at an intermediate source orientation, with the same exterior player. -/
noncomputable def canonical (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (bits : List Bool) : State (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7) :=
  (puzzle (assignment v bits) hP hT).initial

theorem canonical_initial (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] []) :
    canonical v hP hT v.2.1=(puzzle v hP hT).initial := by
  rcases v with ⟨word,initial,target⟩
  rfl

end PushPuzzle.PushFS.Reduction.PhysicalInventory
