/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateCanonicalAccess
public import PushS.FiniteGateNormalSeparation

/-! Legal single-bit updates with complete physical inventories and one actual canonical player position. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGateCanonical

open PushFS PushFS.Gadgets FiniteGeometry FiniteGatePlacedContract FiniteGateCanonicalAccess
open FiniteGateNormalSeparation FiniteGateFaceGeometry FiniteGateFaceBridge

variable {W H : ℕ}

private theorem singleChange_ne {i f : Gates.Signals} (h : Gates.singleChange i f) : i ≠ f := by
  intro he
  subst f
  rcases h with h | h | h
  · exact h.1 rfl
  · exact h.2.1 rfl
  · exact h.2.2 rfl

/-- Every legal AND single change updates all physical gate boxes and returns the player to the same B-line hub. -/
theorem and_singleChange (w : ℕ) (hw : 2 ≤ w)
    (e : GridEmbedding (side w) (side w) W H) (B : Board W H) (extra : Finset (Cell W H))
    (F : AndFrames w e B extra) (C : AndFaces w e B extra)
    (A : ∀ s : Gates.Signals, AndAccess w e B
      ((andBoxes w s.left s.upper s.right).map e.cells ∪ extra))
    (i f : Gates.Signals) (hi : Gates.legal true i) (hf : Gates.legal true f) (hs : Gates.singleChange i f) :
    Reachable B (some 1)
      (e.extend extra ⟨dock w true true,andBoxes w i.left i.upper i.right⟩)
      (e.extend extra ⟨dock w true true,andBoxes w f.left f.upper f.right⟩) := by
  apply and_canonical_step w hw e B extra (andContract w hw e B extra F C) A i f hi hf hs
  exact fun he => singleChange_ne hs (and_frames_normal_injective w hw e F he)

/-- Every legal OR single change updates all physical gate boxes and returns the player to the same B-line hub. -/
theorem or_singleChange (w : ℕ) (hw : 2 ≤ w)
    (e : GridEmbedding (side w) (side w) W H) (B : Board W H) (extra : Finset (Cell W H))
    (F : OrFrames w e B extra) (C : OrFaces w e B extra)
    (A : ∀ s : Gates.Signals, Access w false e B
      ((orBoxes w s.left s.upper s.right).map e.cells ∪ extra))
    (i f : Gates.Signals) (hi : Gates.legal false i) (hf : Gates.legal false f) (hs : Gates.singleChange i f) :
    Reachable B (some 1)
      (e.extend extra ⟨dock w false true,orBoxes w i.left i.upper i.right⟩)
      (e.extend extra ⟨dock w false true,orBoxes w f.left f.upper f.right⟩) := by
  apply or_canonical_step w hw e B extra (orContract w hw e B extra F C) A i f hi hf hs
  exact fun he => singleChange_ne hs (or_frames_normal_injective w hw e F he)

end PushPuzzle.PushS.FiniteGateCanonical
