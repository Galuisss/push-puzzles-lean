/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateAtomLocalFrames
public import PushS.FiniteSourceGateSweepFrames

/-! Actual global frames of the selected core trigger actions. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory.CoreSite

open PushFS PushFS.Reduction FiniteRouting FiniteGeometry FiniteGateState FiniteGateTools
open FiniteGateMacros FiniteGateCore FiniteGateAAmbient FiniteGateActiveRegion FiniteGateAtomLocalFrames
open Cslib.Complexity.NCL
open scoped Classical

attribute [local irreducible] codes width height FiniteGeometry.side

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (c : CoreSite w hw v)

/-- The actual A-closing mouth frame preserves the complete global remaining inventory. -/
theorem and_A_forward_trigger_frame (hg : c.gate.core.isAND = true)
    (p : PathSite w hw v (armSpec w c.gate 0)) (hloc : p.location = ((codes w v).get c.index).1)
    (ha : (inventory w hw v).Admissible) (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (hb : (armSpec w c.gate 0).target = !(armSpec w c.gate 0).initial)
    (b : Bool) (B : Board (width w v) (height w v)) (hB : B.walls = (inventory w hw v).walls) :
    FiniteWireFrame.Frame (triggerForwardActive w) c.embedding B
      (((andBoxes w true b false).erase (point w 2 0)).map c.embedding.cells ∪
        c.remaining (c.corePhase 0 p (tilePhases phase))) := by
  apply c.and_region_frame hg 0 p hloc ha phase fresh hb _ _ _ (and_A_forward_frame w hw b)
  · intro q hq
    have hs := a_forward_shape w q hq
    change Region w true 0 q
    apply region_of_safeBounds
    apply cavity_safe w hw
    all_goals dsimp [AForwardShape] at hs; unfold origin at *; omega
  · intro q hq
    exact and_normal_image_envelope w hw true b false _ q (Finset.mem_of_mem_erase hq)
  · exact hB

/-- The actual A-release three-cell and upper-lane frame preserves all real foreign stock. -/
theorem and_A_backward_trigger_frame (hg : c.gate.core.isAND = true)
    (p : PathSite w hw v (armSpec w c.gate 0)) (hloc : p.location = ((codes w v).get c.index).1)
    (ha : (inventory w hw v).Admissible) (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (hb : (armSpec w c.gate 0).target = !(armSpec w c.gate 0).initial)
    (b d : Bool) (B : Board (width w v) (height w v)) (hB : B.walls = (inventory w hw v).walls) :
    FiniteWireFrame.Frame (triggerBackwardActive w) c.embedding B
      (((andBoxes w true b d).erase (point w 2 0)).map c.embedding.cells ∪
        c.remaining (c.corePhase 0 p (tilePhases phase))) := by
  apply c.and_region_frame hg 0 p hloc ha phase fresh hb _ _ _ (and_A_backward_frame w hw b d)
  · intro q hq
    have hs := a_backward_shape w q hq
    change Region w true 0 q
    apply region_of_safeBounds
    apply cavity_safe w hw
    all_goals dsimp [ABackwardShape] at hs; unfold origin at *; omega
  · intro q hq
    exact and_normal_image_envelope w hw true b d _ q (Finset.mem_of_mem_erase hq)
  · exact hB

end PushPuzzle.PushS.FiniteSourceInventory.CoreSite
