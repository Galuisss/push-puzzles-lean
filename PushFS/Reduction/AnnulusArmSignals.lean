/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.AnnulusImageSignals

/-! The actual full annular arm transmits through every real long-line and protected-corner seam. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting

open Inventory Gadgets.Wires Catalog Soundness
set_option maxRecDepth 65536
set_option maxHeartbeats 100000
attribute [local irreducible] curve original cornerKind cornerOrientation cornerIso lineOrientation

variable {I : Instance} {L : Type} [Fintype L] {M : SlotMatching I L} {g : GateTileState}

private theorem matching_source (g : GateTileState) (l : RawLabel g) : (rawSlotMatching g).source l=rawSource g l := by
  rcases l with ⟨i,l⟩
  exact raw_source g i l

private theorem line_to_corner (f : StorageImage M (rawSlotMatching g)) (r : Fin 3)
    (j : Fin ((curve (key g r)).length-1)) {S T : LabelledState L I.width I.height}
    (hs : Successful M S T) (cert : Certificate I)
    (hin : LineHigh f S r ⟨j.val,by have:=j.isLt; omega⟩ true) : CornerHigh f S r j false := by
  let line : Fin (curve (key g r)).length:=⟨j.val,by have:=j.isLt; omega⟩
  let i:=lineEndpointLabel g r line true
  let k:=cornerEndpointLabel g r j false
  have hlocal : SameComponent (fullPuzzle g).board ((rawSlotMatching g).source i) ((rawSlotMatching g).source k) := by
    rw [matching_source,matching_source]
    exact component_eq_iff.mp (line_corner_component g r j)
  have ho : DirectionalOrder (original (key g r) j.val).travel
      (((rawSlotMatching g).source i).1.val,((rawSlotMatching g).source i).2.val)
      (((rawSlotMatching g).source k).1.val,((rawSlotMatching g).source k).2.val) := by
    rw [matching_source,matching_source]
    exact line_corner_order g r j
  have hgap:=directional_gap (original (key g r) j.val).travel hs cert (f.labels i) (f.labels k)
    (f.source_component i k hlocal) (f.source_directional_order _ i k ho)
  have href:=f.directional_step (original (key g r) j.val).travel
    (lineReference (key g r) j.val line.isLt (initialPhase g r) (targetPhase g r) true)
    (cornerReference (key g r) j.val (by have:=j.isLt; omega) false) (line_corner_reference_step g r j)
  exact travelHigh_join _ _ _ _ _ href hgap hin

private theorem corner_to_line (f : StorageImage M (rawSlotMatching g)) (r : Fin 3)
    (j : Fin ((curve (key g r)).length-1)) {S T : LabelledState L I.width I.height}
    (hs : Successful M S T) (cert : Certificate I)
    (hin : CornerHigh f S r j true) : LineHigh f S r ⟨j.val+1,by have:=j.isLt; omega⟩ false := by
  let line : Fin (curve (key g r)).length:=⟨j.val+1,by have:=j.isLt; omega⟩
  let i:=cornerEndpointLabel g r j true
  let k:=lineEndpointLabel g r line false
  have hlocal : SameComponent (fullPuzzle g).board ((rawSlotMatching g).source i) ((rawSlotMatching g).source k) := by
    rw [matching_source,matching_source]
    exact component_eq_iff.mp (corner_line_component g r j)
  have ho : DirectionalOrder (original (key g r) (j.val+1)).travel
      (((rawSlotMatching g).source i).1.val,((rawSlotMatching g).source i).2.val)
      (((rawSlotMatching g).source k).1.val,((rawSlotMatching g).source k).2.val) := by
    rw [matching_source,matching_source]
    exact corner_line_order g r j
  have hgap:=directional_gap (original (key g r) (j.val+1)).travel hs cert (f.labels i) (f.labels k)
    (f.source_component i k hlocal) (f.source_directional_order _ i k ho)
  have href:=f.directional_step (original (key g r) (j.val+1)).travel
    (cornerReference (key g r) j.val (by have:=j.isLt; omega) true)
    (lineReference (key g r) (j.val+1) line.isLt (initialPhase g r) (targetPhase g r) false) (corner_line_reference_step g r j)
  exact travelHigh_join _ _ _ _ _ href hgap hin

private theorem arm_line_inputs (f : StorageImage M (rawSlotMatching g)) (r : Fin 3)
    {S T : LabelledState L I.width I.height} (hs : Successful M S T) (cert : Certificate I) (ordered : M.Ordered)
    (hin : LineHigh f S r ⟨0,frontier_first_valid _⟩ false) :
    ∀j : Fin (curve (key g r)).length,LineHigh f S r j false := by
  suffices h : ∀n (hn : n<(curve (key g r)).length),LineHigh f S r ⟨n,hn⟩ false from fun j=>h j.val j.isLt
  intro n
  induction n with
  | zero=>intro hn; exact hin
  | succ n ih=>
    intro hn
    have hp:n<(curve (key g r)).length:=by omega
    let j : Fin ((curve (key g r)).length-1):=⟨n,by omega⟩
    exact corner_to_line f r j hs cert
      (corner_image_signal f r j hs cert ordered
        (line_to_corner f r j hs cert (line_image_signal f r ⟨n,hp⟩ hs cert ordered (ih hp))))

/-- From the actual first line's near threshold to the actual final line's far threshold, with every owned auxiliary box present. -/
theorem arm_signal (f : StorageImage M (rawSlotMatching g)) (r : Fin 3)
    {S T : LabelledState L I.width I.height} (hs : Successful M S T) (cert : Certificate I) (ordered : M.Ordered)
    (hin : LineHigh f S r ⟨0,frontier_first_valid _⟩ false) :
    LineHigh f S r ⟨(curve (key g r)).length-1,by have:=frontier_first_valid (key g r); omega⟩ true :=
  line_image_signal f r _ hs cert ordered (arm_line_inputs f r hs cert ordered hin _)

end PushPuzzle.PushFS.Reduction.GateTileRouting
