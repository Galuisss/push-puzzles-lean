/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateStatics.Classifier
public import PushFS.Reduction.FullGateStatics.Source
public import PushFS.Reduction.FullGateStatics.Linear
public import PushFS.Reduction.FullGateRawCanonical

/-! Every actual initial physical box of the complete gate has a straight wall-only SCC. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics

set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] Mosaic.name chart rawSource StorageAtlas.initial StorageAtlas.board

theorem initial_active (g : GateTileState) (p : C) (hp : p∈(fullAtlas g).initial.boxes) :
    (classifier g).name p≠.outside := by
  obtain ⟨l,hl⟩:=(full_initial_mem g p).mp hp
  have hwitness : ∃c,LocatedActive g c (rawSource g l) := raw_source_active g l
  obtain ⟨c,hc⟩ := hwitness
  obtain ⟨q,hq,he⟩ := hc
  have hh := (mosaic g).source_active c q hq
  change (mosaic g).name ((chart g c).embedding.cells q)≠.outside at hh
  rw [he,hl] at hh
  exact hh

/-- C2 for every actual initial auxiliary or port box, with all complete annular wires present. -/
theorem linear (g : GateTileState) (p : C) (hp : p∈(fullAtlas g).initial.boxes) :
    ComponentLinear (component (fullPuzzle g).board p) :=
  active_linear (classifier g) p (initial_active g p hp)

end PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics
