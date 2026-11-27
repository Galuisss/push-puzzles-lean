/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.FlippedChain.Movement

/-! Exact ambient replay with the complete actual foreign collar inventory. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.FlippedChain


variable {W H : ℕ} (n : ℕ) (hn : 2301≤n)

/-- Both full phase changes retain every real external box, including either permitted endpoint neighbor. -/
theorem transition_placed (a b : Bool) (fixed : Finset (C n)) (hf : fixed⊆neighbors n)
    (e : GridEmbedding (n+25) 21 W H) {B : Board W H} {outside : Finset (Cell W H)}
    (hw : e.WallsAgree (board n hn ∅) B)
    (hinside : ∀p,e.cells p∈outside → p∈fixed) (hfixed : ∀p∈fixed,e.cells p∈outside)
    (he : Disjoint outside B.walls) :
    Reachable B (some 1) (e.extend outside (state n hn (uniform a))) (e.extend outside (state n hn (uniform b))) :=
  e.reachable_withFixed hw hinside hfixed he (Frame.transition n hn fixed hf ∅ a b)

end PushPuzzle.PushFS.Gadgets.Wires.FlippedChain
