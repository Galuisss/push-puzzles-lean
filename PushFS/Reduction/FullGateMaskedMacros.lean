/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateMaskedConnected
public import PushFS.Reduction.FullGateLineMacros
public import PushFS.Reduction.FullGateCornerMacros
public import PushFS.Reduction.FullGateBufferProfileMacros

/-! Complete native primitive updates with every real exterior neighbor box retained. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting

open Gadgets Gadgets.Wires
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] StorageAtlas.initial StorageAtlas.board StorageAtlas.profileBoxes profile profileOutside selectedMarks cornerKind cornerOrientation annularProfileBoxes annularBoxes

/-- A released exterior port has only the strict far-end neighbor cells in each actual raw line. -/
def ExternalReady (g : GateTileState) (fixed : Finset C) (r : Fin 3) : Prop :=
  ∀j : Fin (curve (key g r)).length,∀p : Cell (lineInput g r j).width (lineInput g r j).height,
    (lineEmbedding g r j).cells p∈fixed →p∈lineNeighbors (fillerFlip (key g r) j.val)
      (fillerSpan (key g r) j.val) (filler_shape _ _ j.isLt).2.1 (Inventory.initialPhase g r) (Inventory.targetPhase g r)

private theorem masked_line_update_at (g : GateTileState) (f : Inventory.Index g→Bool)
    (fixed : Finset C)
    (hm : ∀p∈fixed,OuterMask g p) (r : Fin 3) (ready : ExternalReady g fixed r)
    (j : Fin (curve (key g r)).length) (hj : f (lineIndex g r j)=false) (prepared : LinePrepared g f r j) :
    Reachable (fullPuzzle g).board (some 1) (maskedProfile g f fixed ((lineEmbedding g r j).cells (lineHub g r j)))
      (maskedProfile g (advance g f (lineIndex g r j)) fixed ((lineEmbedding g r j).cells (lineHub g r j))) := by
  have collar : Polyline.Frame.fixed (lineEmbedding g r j) (profileOutside g f (lineIndex g r j)∪fixed)⊆
      lineNeighbors (fillerFlip (key g r) j.val) (fillerSpan (key g r) j.val) (filler_shape _ _ j.isLt).2.1
        (Inventory.initialPhase g r) (Inventory.targetPhase g r):=by
    intro p hp
    rcases Finset.mem_union.mp ((Polyline.Frame.mem_fixed _ _ p).mp hp) with hp|hp
    · exact line_macro_collar g f r j prepared ((Polyline.Frame.mem_fixed _ _ p).mpr hp)
    · exact ready j p hp
  have hh:=raw_line_transition (fillerFlip (key g r) j.val) (fillerSpan (key g r) j.val)
    (filler_shape (key g r) j.val j.isLt).2.1 (Inventory.initialPhase g r) (Inventory.targetPhase g r)
    (lineEmbedding g r j) (line_walls g r j) (masked_outside_floor g f fixed hm _) collar
  have hs:=masked_line_place g f fixed r j (lineHub g r j)
  simp only [hj,Bool.false_eq_true,ite_false] at hs
  have ht:=masked_line_place g (advance g f (lineIndex g r j)) fixed r j (lineHub g r j)
  simp only [profileOutside_advance,advance_self,ite_true] at ht
  change Reachable (fullPuzzle g).board (some 1)
    ((lineEmbedding g r j).extend (profileOutside g f (lineIndex g r j)∪fixed) ⟨lineHub g r j,(lineInput g r j).initial.boxes⟩)
    ((lineEmbedding g r j).extend (profileOutside g f (lineIndex g r j)∪fixed) ⟨lineHub g r j,(lineInput g r j).board.goals⟩) at hh
  rw [hs,ht] at hh
  exact hh

theorem masked_line_update (g : GateTileState) (f : Inventory.Index g→Bool) (fixed : Finset C)
    (hm : ∀p∈fixed,OuterMask g p) (r : Fin 3) (ready : ExternalReady g fixed r)
    (j : Fin (curve (key g r)).length) (hj : f (lineIndex g r j)=false) (prepared : LinePrepared g f r j) :
    Reachable (fullPuzzle g).board (some 1) (maskedProfile g f fixed (fullAtlas g).player)
      (maskedProfile g (advance g f (lineIndex g r j)) fixed (fullAtlas g).player) :=
  (masked_line_hubs g f fixed hm r j).1.trans ((masked_line_update_at g f fixed hm r ready j hj prepared).trans
    (masked_line_hubs g (advance g f (lineIndex g r j)) fixed hm r j).2)

private theorem masked_corner_update_at (g : GateTileState) (f : Inventory.Index g→Bool)
    (fixed : Finset C)
    (hm : ∀p∈fixed,OuterMask g p) (r : Fin 3)
    (k : Fin ((curve (key g r)).length-1)) (hk : f (cornerIndex g r k)=false) (prepared : CornerPrepared g f r k) :
    Reachable (fullPuzzle g).board (some 1)
      (maskedProfile g f fixed ((armCornerEmbedding g r k).cells (ShortCorners.template (cornerKind (key g r) k.val)).hub))
      (maskedProfile g (advance g f (cornerIndex g r k)) fixed
        ((armCornerEmbedding g r k).cells (ShortCorners.template (cornerKind (key g r) k.val)).hub)) := by
  let frame : ShortCorners.ThinFrame (cornerKind (key g r) k.val) (armCornerEmbedding g r k)
      (fullPuzzle g).board (profileOutside g f (cornerIndex g r k)∪fixed):={
    walls:=arm_corner_walls g r k
    outside_floor:=masked_outside_floor g f fixed hm _
    collar:=by
      intro p hp
      rcases Finset.mem_union.mp ((Polyline.Frame.mem_fixed _ _ p).mp hp) with hp|hp
      · exact corner_macro_collar g f r k prepared ((Polyline.Frame.mem_fixed _ _ p).mpr hp)
      · exact (outer_mask_corner_empty g r k p (hm _ hp)).elim }
  have hh:=frame.transition (Inventory.initialPhase g r) (Inventory.targetPhase g r)
  have hs:=masked_corner_place g f fixed r k (ShortCorners.template (cornerKind (key g r) k.val)).hub
  rw [armPhase_source g f r _ hk] at hs
  have ht:=masked_corner_place g (advance g f (cornerIndex g r k)) fixed r k (ShortCorners.template (cornerKind (key g r) k.val)).hub
  rw [profileOutside_advance,armPhase_advance_self] at ht
  change Reachable (fullPuzzle g).board (some 1)
    ((armCornerEmbedding g r k).extend (profileOutside g f (cornerIndex g r k)∪fixed)
      ⟨(ShortCorners.template (cornerKind (key g r) k.val)).hub,(ShortCorners.template (cornerKind (key g r) k.val)).boxes (Inventory.initialPhase g r)⟩)
    ((armCornerEmbedding g r k).extend (profileOutside g f (cornerIndex g r k)∪fixed)
      ⟨(ShortCorners.template (cornerKind (key g r) k.val)).hub,(ShortCorners.template (cornerKind (key g r) k.val)).boxes (Inventory.targetPhase g r)⟩) at hh
  rw [hs,ht] at hh
  exact hh

theorem masked_corner_update (g : GateTileState) (f : Inventory.Index g→Bool) (fixed : Finset C)
    (hm : ∀p∈fixed,OuterMask g p) (r : Fin 3)
    (k : Fin ((curve (key g r)).length-1)) (hk : f (cornerIndex g r k)=false) (prepared : CornerPrepared g f r k) :
    Reachable (fullPuzzle g).board (some 1) (maskedProfile g f fixed (fullAtlas g).player)
      (maskedProfile g (advance g f (cornerIndex g r k)) fixed (fullAtlas g).player) :=
  (masked_corner_hubs g f fixed hm r k).1.trans ((masked_corner_update_at g f fixed hm r k hk prepared).trans
    (masked_corner_hubs g (advance g f (cornerIndex g r k)) fixed hm r k).2)

private theorem annular_committed (g : GateTileState) (f : Inventory.Index g→Bool) :
    @Eq (Finset C) (annularProfileBoxes g (commitBuffer g f)) (annularProfileBoxes g f) := by
  ext p
  rw [mem_annularProfileBoxes,mem_annularProfileBoxes]
  constructor
  all_goals
    rintro ⟨i,hi,q,hq,he⟩
    cases i with
    | inl i=>cases hi
    | inr i=>exact ⟨.inr i,rfl,q,hq,he⟩

theorem masked_buffer_transition (g : GateTileState) (f : Inventory.Index g→Bool) (fixed : Finset C)
    (hm : ∀p∈fixed,OuterMask g p) (hf : ∀i : Fin 4,f (.inl i)=false)
    (ha : Gates.legal g.core.isAND g.core.initial) (hb : Gates.legal g.core.isAND g.core.target)
    (hs : Gates.singleChange g.core.initial g.core.target)
    (hr : armPhase g f (Gates.changingPort g.core.initial g.core.target)
      (lineIndex g (Gates.changingPort g.core.initial g.core.target) (firstLineIndex g (Gates.changingPort g.core.initial g.core.target)))=true) :
    Reachable (fullPuzzle g).board (some 1) (maskedProfile g f fixed (fullAtlas g).player)
      (maskedProfile g (commitBuffer g f) fixed (fullAtlas g).player) := by
  have hmask : bufferMask g f=(fun _=>false):=funext hf
  have hmask' : bufferMask g (commitBuffer g f)=(fun _=>true):=rfl
  have hcore : bufferCoreSignals g f=g.core.initial:=by rw [bufferCoreSignals,hmask]; rfl
  have hlead : bufferLeadSignals g f=g.core.initial:=by rw [bufferLeadSignals,hmask]; rfl
  have hcore' : bufferCoreSignals g (commitBuffer g f)=g.core.target:=by rw [bufferCoreSignals,hmask']; rfl
  have hlead' : bufferLeadSignals g (commitBuffer g f)=g.core.target:=by rw [bufferLeadSignals,hmask']; rfl
  have hin:=masked_buffer_state g f fixed
  rw [hcore,hlead] at hin
  have hout:=masked_buffer_state g (commitBuffer g f) fixed
  rw [hcore',hlead',annular_committed] at hout
  have hc : GateLead.portCollar g.core.isAND 2301 (bufferRect g.core.isAND) (annularProfileBoxes g f∪fixed)
      (Gates.changingPort g.core.initial g.core.target):=by
    have hh : GateLead.fixed (bufferLeadEmbedding g (Gates.changingPort g.core.initial g.core.target))
        (annularProfileBoxes g f∪fixed)⊆Chain.neighbors 2301:=by
      intro p hp
      rcases Finset.mem_union.mp ((GateLead.mem_fixed _ _ p).mp hp) with hp|hp
      · exact buffer_profile_strict_collar g f _ hr ((GateLead.mem_fixed _ _ p).mpr hp)
      · have hh:=hm _ hp
        rw [←buffer_lead_placement] at hh
        exact (outer_mask_buffer_empty g _ _ hh).elim
    generalize he : Gates.changingPort g.core.initial g.core.target=r at hh ⊢
    fin_cases r <;> exact hh
  have hh:=(maskedBufferShell g f fixed hm).canonical_transition g.core.initial g.core.target ha hb hs hc
  rw [hin,hout] at hh
  exact hh

end PushPuzzle.PushFS.Reduction.GateTileRouting
