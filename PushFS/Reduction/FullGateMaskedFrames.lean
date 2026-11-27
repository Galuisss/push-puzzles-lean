/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateExternalMask
public import PushFS.Reduction.FullGateBufferProfileWalking
public import PushFS.Reduction.GateLeadAmbientWalking

/-! Actual mixed full-gate frames with arbitrary fixed endpoint-neighbor boxes. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting

open Gadgets Gadgets.Wires
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] StorageAtlas.initial StorageAtlas.board profile profileOutside annularProfileBoxes annularBoxes cornerKind cornerOrientation

noncomputable def maskedProfile (g : GateTileState) (f : Inventory.Index g→Bool) (fixed : Finset C) (player : C) : State 200007 198068 :=
  ⟨player,(profile g f (fullAtlas g).player).boxes∪fixed⟩

private theorem mask_floor (g : GateTileState) (fixed : Finset C) (hm : ∀p∈fixed,OuterMask g p) :
    Disjoint fixed (fullPuzzle g).board.walls :=
  Finset.disjoint_left.mpr (fun p hp hw=>outer_mask_floor g p (hm p hp) hw)

theorem masked_outside_floor (g : GateTileState) (f : Inventory.Index g→Bool) (fixed : Finset C)
    (hm : ∀p∈fixed,OuterMask g p) (i : Inventory.Index g) :
    Disjoint (profileOutside g f i∪fixed) (fullPuzzle g).board.walls :=
  Finset.disjoint_union_left.mpr ⟨profileOutside_floor g f i,mask_floor g fixed hm⟩

theorem masked_line_collar (g : GateTileState) (f : Inventory.Index g→Bool) (fixed : Finset C)
    (hm : ∀p∈fixed,OuterMask g p) (r : Fin 3) (j : Fin (curve (key g r)).length) :
    Polyline.Frame.fixed (lineEmbedding g r j) (profileOutside g f (lineIndex g r j)∪fixed)⊆
      lineAllNeighbors (fillerFlip (key g r) j.val) (fillerSpan (key g r) j.val) (filler_shape _ _ j.isLt).2.1
        (Inventory.initialPhase g r) (Inventory.targetPhase g r) := by
  intro p hp
  rcases Finset.mem_union.mp ((Polyline.Frame.mem_fixed _ _ p).mp hp) with hp|hp
  · exact line_profile_collar g f r j ((Polyline.Frame.mem_fixed _ _ p).mpr hp)
  · exact outer_mask_line_collar g r j p (hm _ hp)

theorem masked_line_place (g : GateTileState) (f : Inventory.Index g→Bool) (fixed : Finset C)
    (r : Fin 3) (j : Fin (curve (key g r)).length) (p : Cell (lineInput g r j).width (lineInput g r j).height) :
    (lineEmbedding g r j).extend (profileOutside g f (lineIndex g r j)∪fixed)
      ⟨p,if f (lineIndex g r j) then (lineInput g r j).board.goals else (lineInput g r j).initial.boxes⟩=
      maskedProfile g f fixed ((lineEmbedding g r j).cells p) := by
  apply State.ext
  · rfl
  · exact (Finset.union_assoc _ _ _).symm.trans (congrArg (fun s=>s∪fixed)
      (profile_line_split g f r j (fullAtlas g).player).symm)

theorem masked_corner_frame (g : GateTileState) (f : Inventory.Index g→Bool) (fixed : Finset C)
    (hm : ∀p∈fixed,OuterMask g p) (r : Fin 3) (j : Fin ((curve (key g r)).length-1)) :
    ShortCorners.TransitFrame (cornerKind (key g r) j.val) (armCornerEmbedding g r j)
      (fullPuzzle g).board (profileOutside g f (cornerIndex g r j)∪fixed) where
  walls:=arm_corner_walls g r j
  outside_floor:=masked_outside_floor g f fixed hm _
  collar:=by
    intro p hp
    rcases Finset.mem_union.mp ((Polyline.Frame.mem_fixed _ _ p).mp hp) with hp|hp
    · exact corner_profile_collar g f r j ((Polyline.Frame.mem_fixed _ _ p).mpr hp)
    · exact (outer_mask_corner_empty g r j p (hm _ hp)).elim

theorem masked_corner_place (g : GateTileState) (f : Inventory.Index g→Bool) (fixed : Finset C)
    (r : Fin 3) (j : Fin ((curve (key g r)).length-1))
    (p : Cell (ShortCorners.width (cornerKind (key g r) j.val)) (ShortCorners.height (cornerKind (key g r) j.val))) :
    (armCornerEmbedding g r j).extend (profileOutside g f (cornerIndex g r j)∪fixed)
      ⟨p,(ShortCorners.template (cornerKind (key g r) j.val)).boxes (armPhase g f r (cornerIndex g r j))⟩=
      maskedProfile g f fixed ((armCornerEmbedding g r j).cells p) := by
  apply State.ext
  · rfl
  · exact (Finset.union_assoc _ _ _).symm.trans (congrArg (fun s=>s∪fixed)
      (profile_corner_split g f r j (fullAtlas g).player).symm)

private theorem mask_buffer_lead_empty (g : GateTileState) (fixed : Finset C) (hm : ∀p∈fixed,OuterMask g p)
    (r : Fin 3) (p : Chain.C 2301) : (bufferLeadEmbedding g r).cells p∉fixed := by
  intro hp
  have hh:=hm _ hp
  rw [←buffer_lead_placement] at hh
  exact outer_mask_buffer_empty g (frontierBufferIndex r) ((bufferLeadIso g r).cells p) hh

theorem masked_buffer_collar (g : GateTileState) (f : Inventory.Index g→Bool) (fixed : Finset C)
    (hm : ∀p∈fixed,OuterMask g p) (r : Fin 3) :
    GateLead.fixed (bufferLeadEmbedding g r) (annularProfileBoxes g f∪fixed)⊆Chain.allNeighbors 2301 := by
  intro p hp
  rcases Finset.mem_union.mp ((GateLead.mem_fixed _ _ p).mp hp) with hp|hp
  · exact buffer_profile_collar g f r ((GateLead.mem_fixed _ _ p).mpr hp)
  · exact (mask_buffer_lead_empty g fixed hm r p hp).elim

theorem maskedBufferShell (g : GateTileState) (f : Inventory.Index g→Bool) (fixed : Finset C)
    (hm : ∀p∈fixed,OuterMask g p) :
    GateLead.ThinShell g.core.isAND 2301 (by omega) (bufferRect g.core.isAND) (fullPuzzle g).board
      (annularProfileBoxes g f∪fixed) where
  gate:=(bufferProfileShell g f).gate
  west:=(bufferProfileShell g f).west
  north:=(bufferProfileShell g f).north
  east:=(bufferProfileShell g f).east
  outside_floor:=Finset.disjoint_union_left.mpr ⟨annularProfileBoxes_floor g f,mask_floor g fixed hm⟩
  gate_empty p:=by
    intro hp
    rcases Finset.mem_union.mp hp with hp|hp
    · exact (bufferProfileShell g f).gate_empty p hp
    · have he:=(GateLead.atlas g.core.isAND 2301 (by omega) g.core.initial g.core.target).translate_embedding
        (bufferOffset g.core.isAND).1 (bufferOffset g.core.isAND).2
        (buffer_fitX g.core.isAND) (buffer_fitY g.core.isAND) 0 p
      change (coreEmbedding g).cells p=((GateLead.gate 2301).trans (bufferRect g.core.isAND)).cells p at he
      have hh:=hm _ hp
      rw [←he] at hh
      exact outer_mask_buffer_empty g 0 p hh

theorem masked_buffer_place (g : GateTileState) (f : Inventory.Index g→Bool) (fixed : Finset C)
    (p : Cell 4703 4739) :
    (bufferRect g.core.isAND).extend (annularProfileBoxes g f∪fixed)
      ⟨p,GateLead.boxes g.core.isAND 2301 (by omega) (bufferCoreSignals g f) (bufferLeadSignals g f)⟩=
      maskedProfile g f fixed ((bufferRect g.core.isAND).cells p) := by
  apply State.ext
  · rfl
  · exact (Finset.union_assoc _ _ _).symm.trans (congrArg (fun s=>s∪fixed)
      (congrArg State.boxes (full_buffer_profile g f)))

theorem masked_buffer_state (g : GateTileState) (f : Inventory.Index g→Bool) (fixed : Finset C) :
    (bufferRect g.core.isAND).extend (annularProfileBoxes g f∪fixed)
      (GateLead.state g.core.isAND 2301 (by omega) (bufferCoreSignals g f) (bufferLeadSignals g f))=
      maskedProfile g f fixed (fullAtlas g).player := by
  have he:=masked_buffer_place g f fixed
    (GateLead.state g.core.isAND 2301 (by omega) (bufferCoreSignals g f) (bufferLeadSignals g f)).player
  exact he

end PushPuzzle.PushFS.Reduction.GateTileRouting
