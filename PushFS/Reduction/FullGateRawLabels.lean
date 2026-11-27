/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGatePrimitivePlacement
public import PushFS.Reduction.FullGateSlots
public import PushFS.SlotRelabel

/-! Full gate identities named by their genuine primitive inventory and primitive box label. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateTileRouting


set_option maxRecDepth 65536

abbrev RawLabel (g : GateTileState) := (i : Inventory.Index g)×Inventory.Labels g i

noncomputable def rawLabelEquiv (g : GateTileState) : RawLabel g≃FullLabel g :=
  Equiv.sigmaCongrLeft' (Inventory.numbering g)

noncomputable def rawSlotMatching (g : GateTileState) : SlotMatching (fullPuzzle g) (RawLabel g) :=
  (fullSlotMatching g).relabel (rawLabelEquiv g)

def rawSource (g : GateTileState) (l : RawLabel g) : C :=
  (primitiveEmbedding g l.1).cells ((Inventory.matching g l.1).source l.2)

def rawTarget (g : GateTileState) (l : RawLabel g) : C :=
  (primitiveEmbedding g l.1).cells ((Inventory.matching g l.1).target l.2)

theorem raw_source (g : GateTileState) (i : Inventory.Index g) (l : Inventory.Labels g i) :
    (rawSlotMatching g).source ⟨i,l⟩=(primitiveEmbedding g i).cells ((Inventory.matching g i).source l) := by
  change rawSource g ((rawLabelEquiv g).symm ((rawLabelEquiv g) ⟨i,l⟩))=rawSource g ⟨i,l⟩
  rw [Equiv.symm_apply_apply]

theorem raw_target (g : GateTileState) (i : Inventory.Index g) (l : Inventory.Labels g i) :
    (rawSlotMatching g).target ⟨i,l⟩=(primitiveEmbedding g i).cells ((Inventory.matching g i).target l) := by
  change rawTarget g ((rawLabelEquiv g).symm ((rawLabelEquiv g) ⟨i,l⟩))=rawTarget g ⟨i,l⟩
  rw [Equiv.symm_apply_apply]

end PushPuzzle.PushFS.Reduction.GateTileRouting
