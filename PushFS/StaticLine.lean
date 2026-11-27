/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushFS.Components

/-! Bidirectional wall-only motion along a straight floor segment with support at both ends. -/

@[expose] public section
namespace PushPuzzle.PushFS

/-- Interior points of a directed floor line lie in one displacement SCC. -/
theorem sameComponent_line {w h n : ℕ} {B : Board w h} {d : Direction}
    (cell : Fin (n+3) → Cell w h) (hf : ∀ i, cell i ∉ B.walls)
    (hadj : ∀ i : Fin (n+2), Adjacent d (cell i.castSucc) (cell i.succ))
    (a b : Fin (n+3)) (ha : 0 < a.val ∧ a.val ≤ n+1)
    (hb : 0 < b.val ∧ b.val ≤ n+1) : SameComponent B (cell a) (cell b) := by
  let position (i : Fin (n+1)) := cell ⟨i.val+1, by omega⟩
  have he (i : Fin (n+1)) : component B (position 0) = component B (position i) := by
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih =>
      have hi := i.isLt
      have h0 := hadj ⟨i.val, by omega⟩
      have h1 := hadj ⟨i.val+1, by omega⟩
      have h2 := hadj ⟨i.val+2, by omega⟩
      have hfwd : Displacement B (position i.castSucc) (position i.succ) :=
        ⟨hf _, d, cell ⟨i.val, by omega⟩, h0, h1, hf _, hf _⟩
      have hback : Displacement B (position i.succ) (position i.castSucc) :=
        ⟨hf _, d.opposite, cell ⟨i.val+3, by omega⟩, h2.reverse, h1.reverse, hf _, hf _⟩
      exact ih.trans (component_eq_iff.mpr ⟨.single hfwd, .single hback⟩)
  have ha' := he ⟨a.val-1, by omega⟩
  have hb' := he ⟨b.val-1, by omega⟩
  have hea : position ⟨a.val-1, by omega⟩ = cell a := by
    apply congrArg cell
    apply Fin.ext
    dsimp [position]
    omega
  have heb : position ⟨b.val-1, by omega⟩ = cell b := by
    apply congrArg cell
    apply Fin.ext
    dsimp [position]
    omega
  exact component_eq_iff.mp (by simpa only [hea, heb] using ha'.symm.trans hb')

/-- The same line theorem with its complete number of cells as the index. -/
theorem sameComponent_segment {w h count : ℕ} {B : Board w h} {d : Direction}
    (hc : 3 ≤ count) (cell : Fin count → Cell w h) (hf : ∀ i, cell i ∉ B.walls)
    (hadj : ∀ i : Fin (count-1),
      Adjacent d (cell ⟨i.val, by omega⟩) (cell ⟨i.val+1, by omega⟩))
    (a b : Fin count) (ha : 0 < a.val ∧ a.val+1 < count)
    (hb : 0 < b.val ∧ b.val+1 < count) : SameComponent B (cell a) (cell b) := by
  obtain ⟨n, rfl⟩ : ∃ n, count = n+3 := ⟨count-3, by omega⟩
  exact sameComponent_line cell hf hadj a b ⟨ha.1, by omega⟩ ⟨hb.1, by omega⟩

end PushPuzzle.PushFS
