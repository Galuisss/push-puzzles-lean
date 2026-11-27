/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.BitmapIsometry

/-! Exact semantic markers of one translated complete-instance bitmap. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.Bitmap


/-- A full semantic glyph serialized at its actual unary translation. -/
def instancePatch (I : Instance) (dx dy : ℕ) : Patch := ⟨dx, dy, Encoding.data I⟩

/-- The concrete bitmap lookup denotes exactly the translated semantic cell markers. -/
theorem instancePatch_truth (I : Instance) {W H : ℕ} (dx dy : ℕ)
    (hx : dx + I.width ≤ W) (hy : dy + I.height ≤ H) (p : Cell W H)
    (select : Encoding.Tile → Bool) (hempty : select emptyTile = false) :
    select (localTile (instancePatch I dx dy, p.1.val, p.2.val)) = true ↔
      ∃ q : Cell I.width I.height,
        (GridEmbedding.translate dx dy hx hy).cells q = p ∧
          select (Encoding.tile I.board I.initial q) = true := by
  let inside : Prop := dx ≤ p.1.val ∧ dy ≤ p.2.val ∧
    p.1.val - dx < I.width ∧ p.2.val - dy < I.height
  let : Decidable inside := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))
  by_cases hp : inside
  · let q : Cell I.width I.height := ⟨⟨p.1.val - dx, hp.2.2.1⟩, ⟨p.2.val - dy, hp.2.2.2⟩⟩
    have he : (GridEmbedding.translate dx dy hx hy).cells q = p := by
      apply Prod.ext <;> apply Fin.ext <;> dsimp [GridEmbedding.translate, q] <;> omega
    have ht : localTile (instancePatch I dx dy, p.1.val, p.2.val) =
        Encoding.tile I.board I.initial q := by
      change (if inside then
        ((Encoding.rows I.board I.initial).getD (p.2.val - dy) []).getD (p.1.val - dx) emptyTile
        else emptyTile) = Encoding.tile I.board I.initial q
      rw [ite_eq_left hp]
      exact Encoding.lookup_rows _ _ _ _ hp.2.2.1 hp.2.2.2
    rw [ht]
    constructor
    · intro hh
      exact ⟨q, he, hh⟩
    · rintro ⟨q', he', hh⟩
      have heq : q' = q := (GridEmbedding.translate dx dy hx hy).cells.injective (he'.trans he.symm)
      simpa only [heq] using hh
  · have ht : localTile (instancePatch I dx dy, p.1.val, p.2.val) = emptyTile := by
      change (if inside then _ else emptyTile) = emptyTile
      exact ite_eq_right hp
    rw [ht, hempty]
    constructor
    · intro hh; cases hh
    · rintro ⟨q, he, _⟩
      have hxp := congrArg (fun p : Cell W H => p.1.val) he
      have hyp := congrArg (fun p : Cell W H => p.2.val) he
      change dx + q.1.val = p.1.val at hxp
      change dy + q.2.val = p.2.val at hyp
      have hqx := q.1.isLt
      have hqy := q.2.isLt
      have hi : inside := by dsimp [inside]; omega
      exact False.elim (hp hi)

end PushPuzzle.PushFS.Reduction.Bitmap
