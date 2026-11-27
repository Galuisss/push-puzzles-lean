/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ScanColumns
public import Push.ScanComposition
public import Mathlib.Data.List.Indexes

/-! Dense quota vectors, offsets, and semantically empty zero rounds. -/

public section
namespace PushPuzzle.Push.Scan

open PushFS

/-- Literal lane enumeration is the usual indexed map. -/
private theorem ofQuotas_eq_mapIdx (qs : List ℕ) :
    ofQuotas qs = qs.mapIdx (fun lane quota => (lane, quota)) := by
  rw [List.mapIdx_eq_ofFn]
  rfl

/-- Concatenating quota vectors offsets every lane of the second vector. -/
theorem ofQuotas_append (qs rs : List ℕ) :
    ofQuotas (qs ++ rs) = ofQuotas qs ++
      rs.mapIdx (fun lane quota => (qs.length + lane, quota)) := by
  simp only [ofQuotas_eq_mapIdx, List.mapIdx_append, Nat.add_comm]

/-- Any family of zero reads leaves the complete current bitmap unchanged. -/
private theorem eval_zero_lines {w h : ℕ} (side : Direction) (requests : List (ℕ × ℕ))
    (hz : ∀ a ∈ requests, a.2 = 0) (E : Finset (Cell w h)) :
    eval (lines side requests) E = some E := by
  induction requests with
  | nil => rfl
  | cons a rest ih =>
    simp only [lines, List.map_cons, eval, Instruction.eval, hz a (List.mem_cons_self ..),
      consume, Option.bind_some]
    exact ih (fun b hb => hz b (List.mem_cons_of_mem a hb))

/-- A padded zero suffix in a dense column vector has no effect. -/
theorem eval_columns_zero_pad {w h : ℕ} (qs : List ℕ) (n : ℕ) (E : Finset (Cell w h)) :
    eval (columns (ofQuotas (qs ++ List.replicate n 0))) E =
      eval (columns (ofQuotas qs)) E := by
  rw [ofQuotas_append]
  simp only [columns, lines, List.map_append, eval_append]
  have hz : ∀ a ∈ (List.replicate n 0).mapIdx (fun lane quota => (qs.length + lane, quota)), a.2 = 0 := by
    simp only [List.mapIdx_replicate, List.mem_map]
    rintro a ⟨lane, _, rfl⟩
    rfl
  have hh := eval_zero_lines (w := w) (h := h) .south _ hz
  cases he : eval (List.map (fun (lane, q) => Instruction.read .south lane q) (ofQuotas qs)) E with
  | none => rfl
  | some F => exact hh F

end PushPuzzle.Push.Scan
