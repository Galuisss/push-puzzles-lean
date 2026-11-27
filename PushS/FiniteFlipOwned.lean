/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteFlipMacros

/-! Flip propagation when the right interface is owned by the following routing atom. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteTools

open PushFS

/-- The successor has already moved J; the flip now updates exactly its owned H and I. -/
private theorem flip_forward_owned (w : ℕ) (hw : 2 ≤ w) :
    Reachable (flipMacroBoard w) (some 1)
      ⟨flipNode w .right0, flipMixedBoxes w false 0 true⟩
      ⟨flipNode w .left0, flipBoxes w true⟩ := by
  have h0 := flip_segment_walk w hw false .rightOuter
  have h1 := h0.trans (flip_segment_walk w hw false .lowerOuter)
  have h2 := h1.trans (flip_segment_walk w hw false .lowerMouth)
  have h3 := h2.trans (flip_segment_walk w hw false .crossing)
  have h4 := h3.trans (flip_segment_walk w hw false .upperMouth)
  have h5 := h4.trans (flip_segment_walk w hw false .upperLeft)
  have h6 := h5.trans (flip_segment_walk w hw false .leftOuter)
  have h7 := h6.trans (flip_segment_walk w hw false .leftGap)
  have h8 := h7.tail ⟨.east, flip_push w hw .forwardMiddle0⟩
  have h9 := h8.tail ⟨.east, flip_push w hw .forwardMiddle1⟩
  have h10 := h9.tail ⟨.east, flip_push w hw .forwardMiddle2⟩
  have h11 := h10.trans (flip_segment_walk w hw true .upperMouth)
  have h12 := h11.trans (flip_segment_walk w hw true .upperSupport)
  have h13 := h12.trans (flip_segment_walk w hw true .leftSupport)
  exact h13.tail ⟨.east, flip_push w hw .forwardLeft⟩

/-- The flip returns H and I while leaving the shared J in its old high slot. -/
private theorem flip_backward_owned (w : ℕ) (hw : 2 ≤ w) :
    Reachable (flipMacroBoard w) (some 1)
      ⟨flipNode w .leftReverseSupport, flipBoxes w true⟩
      ⟨flipNode w .lowerMouth, flipMixedBoxes w false 0 true⟩ := by
  have h0 : Reachable (flipMacroBoard w) (some 1)
      ⟨flipNode w .leftReverseSupport, flipMixedBoxes w true 3 true⟩
      ⟨flipNode w .left1, flipMixedBoxes w false 3 true⟩ :=
    .single ⟨.west, flip_push w hw .backwardLeft⟩
  have h1 := h0.trans (flip_segment_walk_reverse w hw true .leftOuter)
  have h2 := h1.trans (flip_segment_walk_reverse w hw true .upperLeft)
  have h3 := h2.trans (flip_segment_walk_reverse w hw true .upperMouth)
  have h4 := h3.trans (flip_segment_walk_reverse w hw true .crossing)
  have h5 := h4.trans (flip_segment_walk_reverse w hw true .lowerMouth)
  have h6 := h5.trans (flip_segment_walk_reverse w hw true .lowerOuter)
  have h7 := h6.trans (flip_segment_walk_reverse w hw true .rightOuter)
  have h8 := h7.trans (flip_segment_walk w hw true .rightGap)
  have h9 := h8.tail ⟨.west, flip_push w hw .backwardMiddle3⟩
  have h10 := h9.tail ⟨.west, flip_push w hw .backwardMiddle2⟩
  exact h10.tail ⟨.west, flip_push w hw .backwardMiddle1⟩

theorem flip_forward_owned_placed (w : ℕ) (hw : 2 ≤ w) {W H : ℕ}
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H} {fixed : Finset (Cell W H)}
    (frame : FiniteWireFrame.Frame (flipActive w) e B fixed) :
    Reachable B (some 1)
      (e.extend fixed ⟨flipNode w .right0, flipMixedBoxes w false 0 true⟩)
      (e.extend fixed ⟨flipNode w .left0, flipBoxes w true⟩) :=
  frame.replay (flip_forward_owned w hw)

theorem flip_backward_owned_placed (w : ℕ) (hw : 2 ≤ w) {W H : ℕ}
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H} {fixed : Finset (Cell W H)}
    (frame : FiniteWireFrame.Frame (flipActive w) e B fixed) :
    Reachable B (some 1)
      (e.extend fixed ⟨flipNode w .leftReverseSupport, flipBoxes w true⟩)
      (e.extend fixed ⟨flipNode w .lowerMouth, flipMixedBoxes w false 0 true⟩) :=
  frame.replay (flip_backward_owned w hw)

end PushPuzzle.PushS.FiniteTools
