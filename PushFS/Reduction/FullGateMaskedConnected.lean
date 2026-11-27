/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateMaskedWalking
public import PushFS.Reduction.FullGateExitGeometry

/-! Complete actual gate connectivity with every fixed adjacent endpoint box present. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting

open Gadgets.Wires FullGateBoundary
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] StorageAtlas.initial StorageAtlas.board profile profileOutside annularProfileBoxes annularBoxes

private theorem masked_first_line_hub (g : GateTileState) (f : Inventory.Index g→Bool)
    (fixed : Finset C)
    (hm : ∀p∈fixed,OuterMask g p) (r : Fin 3) :
    Reachable (fullPuzzle g).board (some 1) (maskedProfile g f fixed (fullAtlas g).player)
      (maskedProfile g f fixed ((lineEmbedding g r (firstLineIndex g r)).cells (lineHub g r (firstLineIndex g r)))) ∧
    Reachable (fullPuzzle g).board (some 1)
      (maskedProfile g f fixed ((lineEmbedding g r (firstLineIndex g r)).cells (lineHub g r (firstLineIndex g r))))
      (maskedProfile g f fixed (fullAtlas g).player) := by
  have hb:=masked_buffer_corners g f fixed hm r 1
  rw [frontier_seam_cell] at hb
  have hp:=masked_first_line_portal_walk g f fixed hm r
  have hl:=masked_line_corners g f fixed hm r (firstLineIndex g r) 0
  exact ⟨hb.1.trans (hp.2.trans hl.2),hl.1.trans (hp.1.trans hb.2)⟩

private theorem masked_incoming_hub_bridge (g : GateTileState) (f : Inventory.Index g→Bool)
    (fixed : Finset C)
    (hm : ∀p∈fixed,OuterMask g p) (r : Fin 3)
    (j : Fin ((curve (key g r)).length-1)) :
    Reachable (fullPuzzle g).board (some 1)
      (maskedProfile g f fixed ((lineEmbedding g r (previousLine g r j)).cells (lineHub g r (previousLine g r j))))
      (maskedProfile g f fixed ((armCornerEmbedding g r j).cells (ShortCorners.template (cornerKind (key g r) j.val)).hub)) ∧
    Reachable (fullPuzzle g).board (some 1)
      (maskedProfile g f fixed ((armCornerEmbedding g r j).cells (ShortCorners.template (cornerKind (key g r) j.val)).hub))
      (maskedProfile g f fixed ((lineEmbedding g r (previousLine g r j)).cells (lineHub g r (previousLine g r j)))) := by
  have hl:=masked_line_corners g f fixed hm r (previousLine g r j) (incomingSeamCorner g r j)
  rw [incoming_seam_cell] at hl
  have hc:=masked_corner_near g f fixed hm r j
  exact ⟨hl.1.trans hc.2,hc.1.trans hl.2⟩

/-- The actual following long-filler hub and the actual protected-corner hub communicate in every fixed mixed inventory. -/
private theorem masked_outgoing_hub_bridge (g : GateTileState) (f : Inventory.Index g→Bool)
    (fixed : Finset C)
    (hm : ∀p∈fixed,OuterMask g p) (r : Fin 3)
    (j : Fin ((curve (key g r)).length-1)) :
    Reachable (fullPuzzle g).board (some 1)
      (maskedProfile g f fixed ((lineEmbedding g r (followingLine g r j)).cells (lineHub g r (followingLine g r j))))
      (maskedProfile g f fixed ((armCornerEmbedding g r j).cells (ShortCorners.template (cornerKind (key g r) j.val)).hub)) ∧
    Reachable (fullPuzzle g).board (some 1)
      (maskedProfile g f fixed ((armCornerEmbedding g r j).cells (ShortCorners.template (cornerKind (key g r) j.val)).hub))
      (maskedProfile g f fixed ((lineEmbedding g r (followingLine g r j)).cells (lineHub g r (followingLine g r j)))) := by
  have hl:=masked_line_corners g f fixed hm r (followingLine g r j) (outgoingSeamCorner g r j)
  rw [outgoing_seam_cell] at hl
  have hc:=masked_corner_far g f fixed hm r j
  exact ⟨hl.1.trans hc.2,hc.1.trans hl.2⟩

theorem masked_line_hubs (g : GateTileState) (f : Inventory.Index g→Bool) (fixed : Finset C)
    (hm : ∀p∈fixed,OuterMask g p) (r : Fin 3)
    (j : Fin (curve (key g r)).length) :
    Reachable (fullPuzzle g).board (some 1) (maskedProfile g f fixed (fullAtlas g).player)
      (maskedProfile g f fixed ((lineEmbedding g r j).cells (lineHub g r j))) ∧
    Reachable (fullPuzzle g).board (some 1) (maskedProfile g f fixed ((lineEmbedding g r j).cells (lineHub g r j)))
      (maskedProfile g f fixed (fullAtlas g).player) := by
  have all_hubs (t : ℕ) : ∀ht : t<(curve (key g r)).length,
      Reachable (fullPuzzle g).board (some 1) (maskedProfile g f fixed (fullAtlas g).player)
        (maskedProfile g f fixed ((lineEmbedding g r ⟨t,ht⟩).cells (lineHub g r ⟨t,ht⟩))) ∧
      Reachable (fullPuzzle g).board (some 1) (maskedProfile g f fixed ((lineEmbedding g r ⟨t,ht⟩).cells (lineHub g r ⟨t,ht⟩)))
        (maskedProfile g f fixed (fullAtlas g).player) := by
    induction t with
    | zero=>
      intro ht
      exact masked_first_line_hub g f fixed hm r
    | succ t ih=>
      intro ht
      let k : Fin ((curve (key g r)).length-1):=⟨t,by omega⟩
      have hp:=ih (by omega)
      have hn:=masked_incoming_hub_bridge g f fixed hm r k
      have hf:=masked_outgoing_hub_bridge g f fixed hm r k
      exact ⟨hp.1.trans (hn.1.trans hf.2),hf.1.trans (hn.2.trans hp.2)⟩
  exact all_hubs j.val j.isLt

/-- Every actual protected-turn hub communicates with the one core player in the full mixed inventory. -/
theorem masked_corner_hubs (g : GateTileState) (f : Inventory.Index g→Bool) (fixed : Finset C)
    (hm : ∀p∈fixed,OuterMask g p) (r : Fin 3)
    (j : Fin ((curve (key g r)).length-1)) :
    Reachable (fullPuzzle g).board (some 1) (maskedProfile g f fixed (fullAtlas g).player)
      (maskedProfile g f fixed ((armCornerEmbedding g r j).cells (ShortCorners.template (cornerKind (key g r) j.val)).hub)) ∧
    Reachable (fullPuzzle g).board (some 1)
      (maskedProfile g f fixed ((armCornerEmbedding g r j).cells (ShortCorners.template (cornerKind (key g r) j.val)).hub))
      (maskedProfile g f fixed (fullAtlas g).player) := by
  have hl:=masked_line_hubs g f fixed hm r (previousLine g r j)
  have hc:=masked_incoming_hub_bridge g f fixed hm r j
  exact ⟨hl.1.trans hc.1,hc.2.trans hl.2⟩

/-- All four literal corners of every full long filler are reachable from and return to the actual core player. -/
private theorem masked_annular_line_corners (g : GateTileState) (f : Inventory.Index g→Bool)
    (fixed : Finset C)
    (hm : ∀p∈fixed,OuterMask g p) (r : Fin 3)
    (j : Fin (curve (key g r)).length) (i : Fin 4) :
    Reachable (fullPuzzle g).board (some 1) (maskedProfile g f fixed (fullAtlas g).player)
      (maskedProfile g f fixed ((lineEmbedding g r j).cells (lineCorner g r j i))) ∧
    Reachable (fullPuzzle g).board (some 1) (maskedProfile g f fixed ((lineEmbedding g r j).cells (lineCorner g r j i)))
      (maskedProfile g f fixed (fullAtlas g).player) := by
  have hh:=masked_line_hubs g f fixed hm r j
  have hc:=masked_line_corners g f fixed hm r j i
  exact ⟨hh.1.trans hc.1,hc.2.trans hh.2⟩

/-- The actual core hub reaches each complete macrocell corner and returns while every real neighboring endpoint box remains fixed. -/
theorem masked_exterior_corners (g : GateTileState) (f : Inventory.Index g→Bool) (fixed : Finset C)
    (hm : ∀p∈fixed,OuterMask g p) (i : Fin 4) :
    Reachable (fullPuzzle g).board (some 1) (maskedProfile g f fixed (fullAtlas g).player)
      (maskedProfile g f fixed (outerCorner i)) ∧
    Reachable (fullPuzzle g).board (some 1) (maskedProfile g f fixed (outerCorner i))
      (maskedProfile g f fixed (fullAtlas g).player) := by
  obtain ⟨r,hi⟩:=used_corner_face g i
  let d:=PortAnnulus.outerDirection (g.key r).2
  let c:=exitCorner d i
  let p:=(lineEmbedding g r (lastLineIndex g r)).cells (lineCorner g r (lastLineIndex g r) c)
  have hh:=masked_annular_line_corners g f fixed hm r (lastLineIndex g r) c
  have hg:=last_line_exit_geometry g r i hi
  have hw:=outer_frame_walk g f fixed (fun p hp=>outer_mask_rail g p (hm p hp)) d p (outerCorner i) hg.1 hi hg.2
  exact ⟨hh.1.trans hw.1,hw.2.trans hh.2⟩

end PushPuzzle.PushFS.Reduction.GateTileRouting
