/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.RotatedChainSignal
public import PushFS.Gadgets.Wires.Catalog.Signal

/-! Ordinary wire threshold predicates use the actual true-phase physical endpoint anchors. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog

set_option maxRecDepth 65536
variable {I : Instance} {L : Type} [Fintype L] {M : SlotMatching I L} {k : Kind} {a b : Bool}

theorem sourceHigh_travel (image : StorageImage M (slotMatching k a b)) (p : PushFS.Cell I.width I.height) :
    sourceHigh k image.dx image.dy p ↔TravelHigh (sourceDirection k)
      ((image.point (firstPoint k true)).1.val,(image.point (firstPoint k true)).2.val) (p.1.val,p.2.val) := by
  cases k <;> simp [sourceHigh,sourceDirection,TravelHigh,StorageImage.point,GridEmbedding.translate,firstPoint,width,height]

theorem targetHigh_travel (image : StorageImage M (slotMatching k a b)) (p : PushFS.Cell I.width I.height) :
    targetHigh k image.dx image.dy p ↔TravelHigh (targetDirection k)
      ((image.point (lastPoint k true)).1.val,(image.point (lastPoint k true)).2.val) (p.1.val,p.2.val) := by
  cases k <;> simp [targetHigh,targetDirection,TravelHigh,StorageImage.point,GridEmbedding.translate,lastPoint,width,height]

end PushPuzzle.PushFS.Gadgets.Wires.Catalog
