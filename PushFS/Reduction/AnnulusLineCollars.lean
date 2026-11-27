/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.AnnulusLines

/-! Exact full near/far protective wall collars of the actual annular long-line family. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateTileRouting


open Gadgets Gadgets.Wires

set_option maxRecDepth 65536

private theorem flip_right7 : ∀ p : Flip.C,18≤p.1.val →
    Flip.wallTest p=decide (p.2.val=8 ∨ p.2.val=9) := by decide +kernel

/-- The last seven actual columns of a chain-plus-flip have the complete upper protective wall. -/
private theorem flipped_right7 (n : ℕ) (hn : 2301≤n) (p : FlippedChain.C n) (hp : n+18≤p.1.val) :
    p∈FlippedChain.walls n hn ↔ p.2.val=8 ∨ p.2.val=9 := by
  let q : Flip.C := (⟨p.1.val-n,by have := p.1.isLt; omega⟩,p.2)
  have he : (FlippedChain.flipPlacement n).cells q=p := by
    apply Prod.ext <;> apply Fin.ext
    · change n+(p.1.val-n)=p.1.val
      omega
    · exact FlippedChain.flip_y n q
  rw [←he,FlippedChain.flip_y]
  have hw : q∈Flip.template.walls ↔ q.2.val=8 ∨ q.2.val=9 := by
    rw [Template.mem_walls]
    change Flip.wallTest q=true↔_
    rw [flip_right7 q (by change 18≤p.1.val-n; omega),decide_eq_true_eq]
  exact (FlippedChain.flip_walls n hn ∅ q).trans hw

theorem line_near_walls (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool)
    (p : Cell (lineBase flip n hn a b).width (lineBase flip n hn a b).height) (hp : p.1.val<5) :
    p∈(lineBase flip n hn a b).board.walls ↔ p.2.val=11 ∨ p.2.val=12 := by
  cases flip
  · exact Polyline.chain_left5 n hn p hp
  · change p∈(FlippedChain.atlas n hn (FlippedChain.uniform a) (FlippedChain.uniform b)).walls↔_
    rw [FlippedChain.atlas_walls]
    exact FlippedChain.left_collar n hn p hp

theorem line_far_walls (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool)
    (p : Cell (lineBase flip n hn a b).width (lineBase flip n hn a b).height)
    (hp : n+(if flip then 20 else 0)≤p.1.val+2) :
    p∈(lineBase flip n hn a b).board.walls ↔
      if flip then p.2.val=8 ∨ p.2.val=9 else p.2.val=11 ∨ p.2.val=12 := by
  cases flip
  · exact Polyline.chain_right7 n hn p (by simpa using hp)
  · change p∈(FlippedChain.atlas n hn (FlippedChain.uniform a) (FlippedChain.uniform b)).walls↔_
    rw [FlippedChain.atlas_walls]
    exact flipped_right7 n hn p (by simpa using hp)

end PushPuzzle.PushFS.Reduction.GateTileRouting
