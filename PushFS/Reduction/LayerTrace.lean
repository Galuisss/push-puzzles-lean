/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.LayerStrands
public import PushFS.Reduction.EdgeTrace

/-! Every actual connection pixel belongs to its correctly numbered upper, middle or lower fragment. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.Plan


open Cslib.Complexity.NCL

/-- A correctly named pixel of the actual upper, middle or lower source-layer band. -/
inductive Layer.TracePart (l : Layer) (edge : ℕ) (p : GridRouting.Point) : Prop
  | upper (i : Fin l.before.wires.length) (named : l.before.wires.getD i.val 0 = edge)
      (trace : ∃ s ∈ Band.curve (l.upperBand, i.val), s.Contains p)
  | middle (strand : l.Strand) (named : (l.strandRoute strand).edge = edge)
      (trace : ∃ s ∈ (l.strandRoute strand).path, s.Contains p)
  | lower (i : Fin l.after.wires.length) (named : l.after.wires.getD i.val 0 = edge)
      (trace : ∃ s ∈ l.bottomPath i.val, s.Contains p)

/-- The emitted complete connections use exactly the real names on all three geometric bands. -/
theorem Layer.trace_classified {l : Layer} (h : l.HasDrawing) {edge : ℕ} {p : GridRouting.Point}
    (hp : Route.Trace l.connections edge p) : l.TracePart edge p := by
  obtain ⟨r, hr, he, hp⟩ := hp
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    let ix : Fin l.before.wires.length := ⟨i, List.mem_range.mp hi⟩
    change l.before.wires.getD i 0 = edge at he
    rw [l.incoming_decompose ix] at hp
    simp only [List.mem_append, or_and_right, exists_or] at hp
    rcases hp with (hu | hm) | hb
    · exact .upper ix he hu
    · exact .middle (l.topStrand ix) ((l.topStrand_edge ix).trans he) hm
    · change ∃ s ∈ (l.exitIndex i).elim [] l.bottomPath, s.Contains p at hb
      cases hx : l.exitIndex i with
      | none => simp only [hx, Option.elim_none, List.not_mem_nil, false_and, exists_false] at hb
      | some j =>
        exact .lower ⟨j, l.exitIndex_lt h ix.isLt hx⟩ ((l.exitIndex_edge h hx).trans he)
          (by simpa only [hx, Option.elim_some] using hb)
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    let ix : Fin l.instruction.data.outputs.length := ⟨i, List.mem_range.mp hi⟩
    change l.before.next + i = edge at he
    change ∃ s ∈ (l.outputRoutes.getD i ⟨0, []⟩).path ++
      l.bottomPath (l.instruction.data.offset + i), s.Contains p at hp
    simp only [List.mem_append, or_and_right, exists_or] at hp
    rcases hp with hm | hb
    · refine .middle (.inr (.inl (.inr ix))) ?_ hm
      have hh : (l.strandRoute (.inr (.inl (.inr ix)))).edge = l.before.next + i := by
        simp [Layer.strandRoute, Layer.outputRoutes, Layer.outputPort, List.getD_eq_getElem?_getD, ix.isLt, ix]
      exact hh.trans he
    · exact .lower ⟨l.instruction.data.offset + i, l.outputIndex_lt h ix⟩
        ((l.after_output h ix).trans he) hb

/-- Middle data agree with the upstream lattice star after shifting to the actual layer row. -/
theorem Layer.middle_trace_iff (l : Layer) (e : l.Strand) (p : GridRouting.Point) :
    (∃ s ∈ (l.strandRoute e).path, s.Contains p) ↔
      l.middleY ≤ p.2 ∧ GridLayout.MiddleContains e (p.1, p.2 - l.middleY) := by
  rw [l.strandRoute_path, mem_segments_iff]
  simp only [Layer.strandPath, GridRouting.Path.contains_translate, Nat.zero_le,
    Nat.sub_zero, true_and, GridLayout.middlePath_contains_iff]

/-- No actual connection pixel exceeds its source layer's computed final row. -/
theorem Layer.TracePart.row_le {l : Layer} (h : l.HasDrawing) {edge : ℕ} {p : GridRouting.Point}
    (hp : l.TracePart edge p) : p.2 ≤ l.height := by
  cases hp with
  | upper i _ ht =>
    have hh := (l.upper_connects i).row_bounds ht
    unfold Layer.height Layer.middleY at *
    omega
  | middle e _ ht =>
    have hh := l.middle_row_bounds h e ht
    unfold Layer.height Layer.middleY at *
    omega
  | lower i _ ht => exact ((l.lower_connects i).row_bounds ht).2

/-- The top boundary records exactly one real position of the actual incoming wire cut. -/
theorem Layer.TracePart.top {l : Layer} (h : l.HasDrawing) {edge : ℕ} {p : GridRouting.Point}
    (hp : l.TracePart edge p) (hy : p.2 = 0) :
    ∃ i : Fin l.before.wires.length, p.1 = 4 * i.val ∧ l.before.wires.getD i.val 0 = edge := by
  cases hp with
  | upper i hn ht =>
    have hi : i.val < l.upperBand.source.length := by simpa only [Layer.upperBand, List.length_map, List.length_range] using i.isLt
    have hh := l.upperBand.curve_top ⟨i.val, hi⟩ p hy ht
    exact ⟨i, by simpa [Layer.upperBand, List.getD_eq_getElem?_getD, i.isLt] using hh, hn⟩
  | middle e _ ht =>
    have hh := (l.middle_row_bounds h e ht).1
    unfold Layer.middleY at hh
    omega
  | lower i _ ht =>
    have hh := ((l.lower_connects i).row_bounds ht).1
    omega

/-- The bottom boundary records exactly one real position of the actual outgoing wire cut. -/
theorem Layer.TracePart.bottom {l : Layer} (h : l.HasDrawing) {edge : ℕ} {p : GridRouting.Point}
    (hp : l.TracePart edge p) (hy : p.2 = l.height) :
    ∃ i : Fin l.after.wires.length, p.1 = 4 * i.val ∧ l.after.wires.getD i.val 0 = edge := by
  cases hp with
  | upper i _ ht =>
    have hh := (l.upper_connects i).row_bounds ht
    unfold Layer.height Layer.middleY at *
    omega
  | middle e _ ht =>
    have hh := l.middle_row_bounds h e ht
    unfold Layer.height Layer.middleY at *
    omega
  | lower i hn ht =>
    have hp' := (Segment.mem_translate_iff (Band.curve (l.lowerBand, i.val)) 0 (l.middleY + 2) p).mp ht
    have hi : i.val < l.lowerBand.source.length := by simpa only [Layer.lowerBand, List.length_map, List.length_range] using i.isLt
    have hry : p.2 - (l.middleY + 2) = 2 * (l.lowerBand.source.length + 1) := by
      simp only [Layer.lowerBand, List.length_map, List.length_range]
      unfold Layer.height Layer.middleY at *
      omega
    have hh := l.lowerBand.curve_bottom ⟨i.val, hi⟩ (p.1, p.2 - (l.middleY + 2)) hry hp'.2.2
    exact ⟨i, by simpa [Layer.lowerBand, List.getD_eq_getElem?_getD, i.isLt] using hh, hn⟩

end PushPuzzle.PushFS.Reduction.Plan
