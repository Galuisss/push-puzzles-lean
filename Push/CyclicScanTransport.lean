/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.Cyclic
public import Push.ScanEmbedding

/-! Exact ordered scan transport under the cyclic quarter turn. -/

public section
namespace PushPuzzle.Push.Cyclic

open PushFS Scan

/-- The actual cell embedding underlying one cyclic quarter turn. -/
@[expose] def turnEmbedding (w h : ℕ) : Cell w h ↪ Cell h w := (turnGeometry w h).cells.toEmbedding

/-- An old west-to-east row enumeration becomes a new bottom-to-top column enumeration. -/
private theorem west_line_turn (w h lane : ℕ) :
    (Scan.lineCells (w := w) (h := h) .west lane).map (turnEmbedding w h) =
      Scan.lineCells (w := h) (h := w) .south lane := by
  by_cases hlane : lane < h
  · simp only [Scan.lineCells, dite_eq_left hlane, List.map_ofFn]
    apply List.ext_getElem (by simp only [List.length_ofFn, List.length_reverse])
    intro i hi _
    simp only [List.getElem_ofFn, List.getElem_reverse, List.length_ofFn]
    apply Prod.ext <;> apply Fin.ext
    · rfl
    · change w - (i + 1) = w - 1 - i
      omega
  · simp only [Scan.lineCells, dite_eq_right hlane, List.map_nil]

/-- An old north-to-south column enumeration becomes a new west-to-east row enumeration. -/
private theorem north_line_turn (w h lane : ℕ) (hlane : lane < w) :
    (Scan.lineCells (w := w) (h := h) .north lane).map (turnEmbedding w h) =
      Scan.lineCells (w := h) (h := w) .west (w - (lane + 1)) := by
  have hrow : w - (lane + 1) < w := by omega
  simp only [Scan.lineCells, dite_eq_left hlane, dite_eq_left hrow, List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  apply Prod.ext <;> apply Fin.ext <;> rfl

/-- The reverse traversal transports to the reverse of the same physical line. -/
private theorem south_line_turn (w h lane : ℕ) (hlane : lane < w) :
    (Scan.lineCells (w := w) (h := h) .south lane).map (turnEmbedding w h) =
      Scan.lineCells (w := h) (h := w) .east (w - (lane + 1)) := by
  have hrow : w - (lane + 1) < w := by omega
  simp only [Scan.lineCells, dite_eq_left hlane, dite_eq_left hrow, List.map_reverse, List.map_ofFn]
  congr 1

/-- The old east-to-west row order becomes the new top-to-bottom column order. -/
private theorem east_line_turn (w h lane : ℕ) :
    (Scan.lineCells (w := w) (h := h) .east lane).map (turnEmbedding w h) =
      Scan.lineCells (w := h) (h := w) .north lane := by
  have he := congrArg List.reverse (west_line_turn w h lane)
  by_cases hlane : lane < h
  · simpa only [Scan.lineCells, dite_eq_left hlane, List.map_ofFn, List.map_reverse,
      List.reverse_reverse] using he
  · simp only [Scan.lineCells, dite_eq_right hlane, List.map_nil]

/-- A westward row read and the corresponding next southward column read have identical remainders. -/
theorem west_read_turn {w h : ℕ} (lane quota : ℕ) (E : Finset (Cell w h)) :
    (Scan.Instruction.read .south lane quota).eval (E.map (turnEmbedding w h)) =
      ((Scan.Instruction.read .west lane quota).eval E).map (Finset.map (turnEmbedding w h)) := by
  change Scan.consume (Scan.lineCells .south lane) quota (E.map _) = _
  rw [← west_line_turn]
  exact consume_map _ _ _ _

/-- A northward column read becomes the corresponding westward row read. -/
theorem north_read_turn {w h : ℕ} (lane quota : ℕ) (hlane : lane < w) (E : Finset (Cell w h)) :
    (Scan.Instruction.read .west (w - (lane + 1)) quota).eval (E.map (turnEmbedding w h)) =
      ((Scan.Instruction.read .north lane quota).eval E).map (Finset.map (turnEmbedding w h)) := by
  change Scan.consume (Scan.lineCells .west (w - (lane + 1))) quota (E.map _) = _
  rw [← north_line_turn w h lane hlane]
  exact consume_map _ _ _ _

/-- A southward column read becomes the corresponding eastward row read. -/
theorem south_read_turn {w h : ℕ} (lane quota : ℕ) (hlane : lane < w) (E : Finset (Cell w h)) :
    (Scan.Instruction.read .east (w - (lane + 1)) quota).eval (E.map (turnEmbedding w h)) =
      ((Scan.Instruction.read .south lane quota).eval E).map (Finset.map (turnEmbedding w h)) := by
  change Scan.consume (Scan.lineCells .east (w - (lane + 1))) quota (E.map _) = _
  rw [← south_line_turn w h lane hlane]
  exact consume_map _ _ _ _

/-- An eastward row read becomes the corresponding northward column read. -/
theorem east_read_turn {w h : ℕ} (lane quota : ℕ) (E : Finset (Cell w h)) :
    (Scan.Instruction.read .north lane quota).eval (E.map (turnEmbedding w h)) =
      ((Scan.Instruction.read .east lane quota).eval E).map (Finset.map (turnEmbedding w h)) := by
  change Scan.consume (Scan.lineCells .north lane) quota (E.map _) = _
  rw [← east_line_turn]
  exact consume_map _ _ _ _

end PushPuzzle.Push.Cyclic
