/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateTools
public import PushS.FiniteFrameComposition

/-! Ambient replay of all placed AND tools with the complete gate inventory preserved. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGateTools

open PushFS FiniteGeometry FiniteGateState

variable {W H : ℕ}

/-- Replay the protection forward macro using only its narrow active cells. -/
theorem protection_forward_ambient (w : ℕ) (X : AndPhases w)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (FiniteTools.turnActive w) ((protectionEmbedding w).trans e) B
      ((outside w X (protectionLabel w)).map e.cells ∪ extra)) :
    Reachable B (some 1)
      (e.extend extra ⟨(protectionEmbedding w).cells (FiniteTools.turnNode w .corner),
        andMixedBoxes w (protectionPhases w X false)⟩)
      (e.extend extra ⟨(protectionEmbedding w).cells (FiniteTools.turnNode w .horizontal0),
        andMixedBoxes w (protectionPhases w X true)⟩) := by
  have hh := F.replay_nested (FiniteTools.turn_forward w)
  simpa only [GridEmbedding.extend, protection_inventory] using hh

/-- Replay the protection backward macro using only its narrow active cells. -/
theorem protection_backward_ambient (w : ℕ) (X : AndPhases w)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (FiniteTools.turnActive w) ((protectionEmbedding w).trans e) B
      ((outside w X (protectionLabel w)).map e.cells ∪ extra)) :
    Reachable B (some 1)
      (e.extend extra ⟨(protectionEmbedding w).cells (FiniteTools.turnNode w .corner),
        andMixedBoxes w (protectionPhases w X true)⟩)
      (e.extend extra ⟨(protectionEmbedding w).cells (FiniteTools.turnNode w .vertical1),
        andMixedBoxes w (protectionPhases w X false)⟩) := by
  have hh := F.replay_nested (FiniteTools.turn_backward w)
  simpa only [GridEmbedding.extend, protection_inventory] using hh

/-- Replay an entry or exit walk through the actual protection tool inventory. -/
theorem protection_walk_ambient (w : ℕ) (X : AndPhases w) (q : Bool)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (FiniteTools.turnActive w) ((protectionEmbedding w).trans e) B
      ((outside w X (protectionLabel w)).map e.cells ∪ extra))
    {p r : Cell (FiniteTools.side w) (FiniteTools.side w)}
    (hr : Reachable (FiniteTools.turnMacroBoard w) (some 1)
      ⟨p, FiniteTools.turnBoxes w q⟩ ⟨r, FiniteTools.turnBoxes w q⟩) :
    Reachable B (some 1)
      (e.extend extra ⟨(protectionEmbedding w).cells p, andMixedBoxes w (protectionPhases w X q)⟩)
      (e.extend extra ⟨(protectionEmbedding w).cells r, andMixedBoxes w (protectionPhases w X q)⟩) := by
  have hh := F.replay_nested hr
  simpa only [GridEmbedding.extend, protection_inventory] using hh

/-- Replay the upper forward macro using only its narrow active cells. -/
theorem upper_forward_ambient (w : ℕ) (X : AndPhases w)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (FiniteTools.turnActive w) ((upperEmbedding w).trans e) B
      ((outside w X (upperLabel w)).map e.cells ∪ extra)) :
    Reachable B (some 1)
      (e.extend extra ⟨(upperEmbedding w).cells (FiniteTools.turnNode w .corner),
        andMixedBoxes w (upperPhases w X false)⟩)
      (e.extend extra ⟨(upperEmbedding w).cells (FiniteTools.turnNode w .horizontal0),
        andMixedBoxes w (upperPhases w X true)⟩) := by
  have hh := F.replay_nested (FiniteTools.turn_forward w)
  simpa only [GridEmbedding.extend, upper_inventory] using hh

/-- Replay the upper backward macro using only its narrow active cells. -/
theorem upper_backward_ambient (w : ℕ) (X : AndPhases w)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (FiniteTools.turnActive w) ((upperEmbedding w).trans e) B
      ((outside w X (upperLabel w)).map e.cells ∪ extra)) :
    Reachable B (some 1)
      (e.extend extra ⟨(upperEmbedding w).cells (FiniteTools.turnNode w .corner),
        andMixedBoxes w (upperPhases w X true)⟩)
      (e.extend extra ⟨(upperEmbedding w).cells (FiniteTools.turnNode w .vertical1),
        andMixedBoxes w (upperPhases w X false)⟩) := by
  have hh := F.replay_nested (FiniteTools.turn_backward w)
  simpa only [GridEmbedding.extend, upper_inventory] using hh

/-- Replay an entry or exit walk through the actual upper tool inventory. -/
theorem upper_walk_ambient (w : ℕ) (X : AndPhases w) (q : Bool)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (FiniteTools.turnActive w) ((upperEmbedding w).trans e) B
      ((outside w X (upperLabel w)).map e.cells ∪ extra))
    {p r : Cell (FiniteTools.side w) (FiniteTools.side w)}
    (hr : Reachable (FiniteTools.turnMacroBoard w) (some 1)
      ⟨p, FiniteTools.turnBoxes w q⟩ ⟨r, FiniteTools.turnBoxes w q⟩) :
    Reachable B (some 1)
      (e.extend extra ⟨(upperEmbedding w).cells p, andMixedBoxes w (upperPhases w X q)⟩)
      (e.extend extra ⟨(upperEmbedding w).cells r, andMixedBoxes w (upperPhases w X q)⟩) := by
  have hh := F.replay_nested hr
  simpa only [GridEmbedding.extend, upper_inventory] using hh

/-- Replay the flip forward macro using only its narrow active cells. -/
theorem flip_forward_ambient (w : ℕ) (hw : 2 ≤ w) (X : AndPhases w)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (FiniteTools.flipActive w) ((flipEmbedding w).trans e) B
      ((outside w X (flipLabel w)).map e.cells ∪ extra)) :
    Reachable B (some 1)
      (e.extend extra ⟨(flipEmbedding w).cells (FiniteTools.flipNode w .rightSupport),
        andMixedBoxes w (flipPhases w X false)⟩)
      (e.extend extra ⟨(flipEmbedding w).cells (FiniteTools.flipNode w .left0),
        andMixedBoxes w (flipPhases w X true)⟩) := by
  have hh := F.replay_nested (FiniteTools.flip_forward w hw)
  simpa only [GridEmbedding.extend, flip_inventory] using hh

/-- Replay the flip backward macro using only its narrow active cells. -/
theorem flip_backward_ambient (w : ℕ) (hw : 2 ≤ w) (X : AndPhases w)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (FiniteTools.flipActive w) ((flipEmbedding w).trans e) B
      ((outside w X (flipLabel w)).map e.cells ∪ extra)) :
    Reachable B (some 1)
      (e.extend extra ⟨(flipEmbedding w).cells (FiniteTools.flipNode w .leftReverseSupport),
        andMixedBoxes w (flipPhases w X true)⟩)
      (e.extend extra ⟨(flipEmbedding w).cells (FiniteTools.flipNode w .right1),
        andMixedBoxes w (flipPhases w X false)⟩) := by
  have hh := F.replay_nested (FiniteTools.flip_backward w hw)
  simpa only [GridEmbedding.extend, flip_inventory] using hh

/-- Replay an entry or exit walk through the actual flip tool inventory. -/
theorem flip_walk_ambient (w : ℕ) (X : AndPhases w) (q : Bool)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H}
    {extra : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (FiniteTools.flipActive w) ((flipEmbedding w).trans e) B
      ((outside w X (flipLabel w)).map e.cells ∪ extra))
    {p r : Cell (FiniteTools.side w) (FiniteTools.side w)}
    (hr : Reachable (FiniteTools.flipMacroBoard w) (some 1)
      ⟨p, FiniteTools.flipBoxes w q⟩ ⟨r, FiniteTools.flipBoxes w q⟩) :
    Reachable B (some 1)
      (e.extend extra ⟨(flipEmbedding w).cells p, andMixedBoxes w (flipPhases w X q)⟩)
      (e.extend extra ⟨(flipEmbedding w).cells r, andMixedBoxes w (flipPhases w X q)⟩) := by
  have hh := F.replay_nested hr
  simpa only [GridEmbedding.extend, flip_inventory] using hh

end PushPuzzle.PushS.FiniteGateTools
