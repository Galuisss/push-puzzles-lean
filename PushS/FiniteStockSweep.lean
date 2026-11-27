/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteLaneFrames

/-! Exact complete-inventory endpoints for an ambient straight sweep. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSquareLine.Sweep

open PushFS

variable {N W H : ℕ}

private theorem stock_extend (S : Sweep N) (fixed : Finset (Cell N N))
    (stock : Bool → Finset (Cell N N))
    (hstock : ∀ q, S.boxes fixed (if q then S.line.count else 0) = stock q)
    (e : GridEmbedding N N W H) (extra : Finset (Cell W H)) (q : Bool) (p : Cell N N) :
    e.extend (fixed.map e.cells ∪ extra)
      ⟨p, Finset.univ.image (S.position (if q then S.line.count else 0))⟩ =
    e.extend extra ⟨p, stock q⟩ := by
  apply State.ext
  · rfl
  · rw [← hstock q]
    simp only [GridEmbedding.extend, boxes, Finset.map_union]
    ac_rfl

/-- A narrow sweep frame updates its entire represented source stock to its represented target stock. -/
theorem stock_forward (S : Sweep N) (fixed : Finset (Cell N N))
    (stock : Bool → Finset (Cell N N))
    (hstock : ∀ q, S.boxes fixed (if q then S.line.count else 0) = stock q)
    (e : GridEmbedding N N W H) {B : Board W H} {extra : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame S.active e B (fixed.map e.cells ∪ extra)) :
    Reachable B (some 1) (e.extend extra ⟨S.hub,stock false⟩)
      (e.extend extra ⟨S.hub,stock true⟩) := by
  have hr := S.forward_placed e F
  simpa only [← stock_extend S fixed stock hstock e extra false,
    ← stock_extend S fixed stock hstock e extra true, Bool.false_eq_true, ite_false, ite_true] using hr

/-- The same concrete sweep frame reverses the entire represented stock. -/
theorem stock_backward (S : Sweep N) (fixed : Finset (Cell N N))
    (stock : Bool → Finset (Cell N N))
    (hstock : ∀ q, S.boxes fixed (if q then S.line.count else 0) = stock q)
    (e : GridEmbedding N N W H) {B : Board W H} {extra : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame S.active e B (fixed.map e.cells ∪ extra)) :
    Reachable B (some 1) (e.extend extra ⟨S.hub,stock true⟩)
      (e.extend extra ⟨S.hub,stock false⟩) := by
  have hr := S.backward_placed e F
  simpa only [← stock_extend S fixed stock hstock e extra false,
    ← stock_extend S fixed stock hstock e extra true, Bool.false_eq_true, ite_false, ite_true] using hr

end PushPuzzle.PushS.FiniteSquareLine.Sweep
