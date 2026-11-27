/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteCavity
public import PushFS.AxisStencil

/-! Protecting cavity walls survive placement inside an arbitrary larger wall union. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteCavity

open PushFS

/-- Translate an actual cavity using only inclusion of its source wall cells. -/
theorem Walls.translate {w h W H j r y : ℕ} {B : Board w h} {ambient : Board W H}
    (C : Walls B j r y) (hr : r ≤ w) (hy0 : 0 < y) (hy1 : y+1 < h)
    (dx dy : ℕ) (hx : dx+w ≤ W) (hy : dy+h ≤ H)
    (hw : ∀ p, p ∈ B.walls → (GridEmbedding.translate dx dy hx hy).cells p ∈ ambient.walls) :
    Walls ambient (dx+j) (dx+r) (dy+y) := by
  constructor
  · intro p hpy hpx hpx'
    obtain ⟨q, he⟩ := (GridEmbedding.translate_image_iff dx dy hx hy p).mpr
      ⟨by omega, by omega, by omega, by omega⟩
    have hqx := congrArg (fun p : Cell W H => p.1.val) he
    have hqy := congrArg (fun p : Cell W H => p.2.val) he
    change dx+q.1.val = p.1.val at hqx
    change dy+q.2.val = p.2.val at hqy
    rw [← he]
    apply hw q
    exact C.below q (by omega) (by omega) (by omega)
  · intro p hpy hpx
    obtain ⟨q, he⟩ := (GridEmbedding.translate_image_iff dx dy hx hy p).mpr
      ⟨by omega, by omega, by omega, by omega⟩
    have hqx := congrArg (fun p : Cell W H => p.1.val) he
    have hqy := congrArg (fun p : Cell W H => p.2.val) he
    change dx+q.1.val = p.1.val at hqx
    change dy+q.2.val = p.2.val at hqy
    rw [← he]
    apply hw q
    exact C.roof q (by omega) ⟨by omega, by omega⟩

end PushPuzzle.PushS.FiniteCavity
