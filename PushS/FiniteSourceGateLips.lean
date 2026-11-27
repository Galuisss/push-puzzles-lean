/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceGatePhysicalContext

/-! The actual open-B lip completes the two right-output return mouths. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory.GatePhysicalContext

open PushFS PushFS.Reduction FiniteRouting FiniteGeometry FiniteGateState FiniteGateTools
open FiniteGateMacros FiniteGateCore FiniteGateActiveRegion FiniteGateFaceGeometry
open FiniteGateOutputs
open scoped Classical

attribute [local irreducible] codes width height FiniteGeometry.side

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} {c : CoreSite w hw v}
  {p : PathSite w hw v (armSpec w c.gate 2)} {B : Board (width w v) (height w v)}

/-- The AND return crosses its two actual B-lip cells with every global identity fixed. -/
theorem and_output_lip (C : GatePhysicalContext c 2 p B) (hg : c.gate.core.isAND = true) :
    FiniteWireFrame.Frame (FiniteAtomFrames.walkActive (point w 2 1) (point w 3 1)) c.embedding B
      ((andOutputBoxes w true true false).map c.embedding.cells ∪ C.outside) := by
  have hr (q : Cell (FiniteGeometry.side w) (FiniteGeometry.side w))
      (hq : q ∈ FiniteAtomFrames.walkActive (point w 2 1) (point w 3 1)) :
      SafeBounds w true 2 (coordinates q) := by
    have hs := (FiniteAtomFrames.mem_walkActive _ _ _).mp hq
    apply cavity_safe w hw
    all_goals dsimp [point] at hs; unfold origin at *; omega
  have hf (q : Cell (FiniteGeometry.side w) (FiniteGeometry.side w))
      (hq : q ∈ FiniteAtomFrames.walkActive (point w 2 1) (point w 3 1)) :
      Free (andBoard w ∅) (andMixedBoxes w (andOutputPhases w true true false)) q := by
    have hs := (FiniteAtomFrames.mem_walkActive _ _ _).mp hq
    constructor
    · apply and_core_floor w hw q
      all_goals dsimp [point] at hs; unfold origin at *; omega
    · intro hm
      obtain ⟨l,_,he⟩ := Finset.mem_image.mp hm
      have hx := congrArg (fun z => z.1.val) he
      have hy := congrArg (fun z => z.2.val) he
      rw [andMixedCell_output] at hx hy
      cases l <;> dsimp [andOutputCell,andCell,andPoint,point,origin] at hx hy hs <;> omega
  simpa only [andMixedBoxes_output,outside] using
    c.and_mixed_frame hg 2 p C.location C.admissible C.phase C.fresh C.reversed
      (andOutputPhases w true true false) _ hr hf B C.walls

/-- The OR return's final two cells cross the real open-B lip. -/
theorem or_output_lip (C : GatePhysicalContext c 2 p B) (hg : c.gate.core.isAND = false) :
    FiniteWireFrame.Frame (FiniteAtomFrames.walkActive (point w 3 1) (point w 4 1)) c.embedding B
      ((orOutputBoxes w false true false).map c.embedding.cells ∪ C.outside) := by
  have hr (q : Cell (FiniteGeometry.side w) (FiniteGeometry.side w))
      (hq : q ∈ FiniteAtomFrames.walkActive (point w 3 1) (point w 4 1)) :
      SafeBounds w false 2 (coordinates q) := by
    have hs := (FiniteAtomFrames.mem_walkActive _ _ _).mp hq
    apply cavity_safe w hw
    all_goals dsimp [point] at hs; unfold origin at *; omega
  have hf (q : Cell (FiniteGeometry.side w) (FiniteGeometry.side w))
      (hq : q ∈ FiniteAtomFrames.walkActive (point w 3 1) (point w 4 1)) :
      Free (orBoard w ∅) (orMixedBoxes w (orOutputPhases w false true false)) q := by
    have hs := (FiniteAtomFrames.mem_walkActive _ _ _).mp hq
    constructor
    · apply or_core_floor w hw q
      all_goals dsimp [point] at hs; unfold origin at *; omega
    · intro hm
      obtain ⟨l,_,he⟩ := Finset.mem_image.mp hm
      have hx := congrArg (fun z => z.1.val) he
      have hy := congrArg (fun z => z.2.val) he
      rw [orMixedCell_output] at hx hy
      cases l <;> dsimp [orOutputCell,orCell,orPoint,point,origin] at hx hy hs <;> omega
  simpa only [orMixedBoxes_output,outside] using
    c.or_mixed_frame hg 2 p C.location C.admissible C.phase C.fresh C.reversed
      (orOutputPhases w false true false) _ hr hf B C.walls

end PushPuzzle.PushS.FiniteSourceInventory.GatePhysicalContext
