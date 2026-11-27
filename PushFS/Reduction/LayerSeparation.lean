/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.LayerTrace

/-! Different actual source edges in one emitted layer meet only at its logical vertex. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.Plan


open Cslib.Complexity.NCL

private theorem upper_middle_edge {l : Layer} (h : l.HasDrawing)
    (i : Fin l.before.wires.length) (e : l.Strand) (p : GridRouting.Point)
    (hu : ∃ s ∈ Band.curve (l.upperBand, i.val), s.Contains p)
    (hm : ∃ s ∈ (l.strandRoute e).path, s.Contains p) :
    l.before.wires.getD i.val 0 = (l.strandRoute e).edge := by
  have huRows := (l.upper_connects i).row_bounds hu
  have hmRows := l.middle_row_bounds h e hm
  have hy : p.2 = l.middleY := by omega
  have hi : i.val < l.upperBand.source.length := by
    simpa only [Layer.upperBand, List.length_map, List.length_range] using i.isLt
  have hrow : p.2 = 2 * (l.upperBand.source.length + 1) := by
    simpa [Layer.upperBand, Layer.middleY] using hy
  have hx : p.1 = expanded l.instruction.data.offset l.instruction.data.inputs.length i.val := by
    have hh := l.upperBand.curve_bottom ⟨i.val, hi⟩ p hrow hu
    simpa [Layer.upperBand, List.getD_eq_getElem?_getD, i.isLt] using hh
  have hm0 : GridLayout.MiddleContains e (p.1, 0) := by
    have hh := (l.middle_trace_iff e p).mp hm
    simpa only [hy, Nat.sub_self] using hh.2
  have hc := (GridLayout.middlePath_contains_iff (l.topStrand i) _).mp
    (GridLayout.middlePath (l.topStrand i)).source_mem
  rw [l.topStrand_start i, ← hx] at hc
  have he := GridLayout.middle_boundary_unique h.constraints.2.1 (Or.inl rfl) hm0 hc
  rw [he]
  exact (l.topStrand_edge i).symm

private theorem middle_lower_edge {l : Layer} (h : l.HasDrawing)
    (e : l.Strand) (i : Fin l.after.wires.length) (p : GridRouting.Point)
    (hm : ∃ s ∈ (l.strandRoute e).path, s.Contains p)
    (hl : ∃ s ∈ l.bottomPath i.val, s.Contains p) :
    (l.strandRoute e).edge = l.after.wires.getD i.val 0 := by
  have hmRows := l.middle_row_bounds h e hm
  have hlRows := (l.lower_connects i).row_bounds hl
  have hy : p.2 = l.middleY + 2 := by omega
  have hp := (Segment.mem_translate_iff (Band.curve (l.lowerBand, i.val)) 0 (l.middleY + 2) p).mp hl
  have hp0 : ∃ s ∈ Band.curve (l.lowerBand, i.val), s.Contains (p.1, 0) := by
    simpa only [hy, Nat.sub_zero, Nat.sub_self] using hp.2.2
  have hi : i.val < l.lowerBand.source.length := by
    simpa only [Layer.lowerBand, List.length_map, List.length_range] using i.isLt
  have hx : p.1 = expanded l.instruction.data.offset l.instruction.data.outputs.length i.val := by
    have hh := l.lowerBand.curve_top ⟨i.val, hi⟩ (p.1, 0) rfl hp0
    simpa [Layer.lowerBand, List.getD_eq_getElem?_getD, i.isLt] using hh
  have hm2 : GridLayout.MiddleContains e (p.1, 2) := by
    have hh := (l.middle_trace_iff e p).mp hm
    have hr : p.2 - l.middleY = 2 := by omega
    simpa only [hr] using hh.2
  have hc := (GridLayout.middlePath_contains_iff (l.bottomStrand h i) _).mp
    (GridLayout.middlePath (l.bottomStrand h i)).target_mem
  rw [l.bottomStrand_end h i, ← hx] at hc
  have he := GridLayout.middle_boundary_unique h.constraints.2.1 (Or.inr rfl) hm2 hc
  rw [he]
  exact l.bottomStrand_edge h i

private theorem upper_lower_false (l : Layer) (i : Fin l.before.wires.length)
    (j : Fin l.after.wires.length) (p : GridRouting.Point)
    (hu : ∃ s ∈ Band.curve (l.upperBand, i.val), s.Contains p)
    (hl : ∃ s ∈ l.bottomPath j.val, s.Contains p) : False := by
  have hh := (l.upper_connects i).row_bounds hu
  have ht := (l.lower_connects j).row_bounds hl
  omega

private theorem lower_lower_false {l : Layer} (h : l.HasDrawing)
    {i j : Fin l.after.wires.length} (hij : i ≠ j) (p : GridRouting.Point)
    (hi : ∃ s ∈ l.bottomPath i.val, s.Contains p)
    (hj : ∃ s ∈ l.bottomPath j.val, s.Contains p) : False := by
  have hi' := (Segment.mem_translate_iff (Band.curve (l.lowerBand, i.val)) 0 (l.middleY + 2) p).mp hi
  have hj' := (Segment.mem_translate_iff (Band.curve (l.lowerBand, j.val)) 0 (l.middleY + 2) p).mp hj
  exact (l.lower_disjoint h hij (p.1 - 0, p.2 - (l.middleY + 2))) ⟨hi'.2.2, hj'.2.2⟩

/-- The complete labelled source layer has no intersection between different edges away from its one vertex. -/
private theorem Layer.TracePart.separated {l : Layer} (h : l.HasDrawing) {e f : ℕ} (hef : e ≠ f)
    {p : GridRouting.Point} (he : l.TracePart e p) (hf : l.TracePart f p) : p = l.vertexPoint := by
  cases he with
  | upper i hi hpi =>
    cases hf with
    | upper j hj hpj =>
      have hij : i ≠ j := by intro hh; subst j; exact hef (hi.symm.trans hj)
      exact False.elim ((l.upper_disjoint h hij p) ⟨hpi, hpj⟩)
    | middle strand hj hpj =>
      exact False.elim (hef (hi.symm.trans ((upper_middle_edge h i strand p hpi hpj).trans hj)))
    | lower j _ hpj => exact False.elim (upper_lower_false l i j p hpi hpj)
  | middle strand hi hpi =>
    cases hf with
    | upper j hj hpj =>
      exact False.elim (hef (hi.symm.trans ((upper_middle_edge h j strand p hpj hpi).symm.trans hj)))
    | middle strand' hj hpj =>
      by_cases hh : strand = strand'
      · subst strand'
        exact False.elim (hef (hi.symm.trans hj))
      · exact (l.middle_intersection h hh hpi hpj).1
    | lower j hj hpj =>
      exact False.elim (hef (hi.symm.trans ((middle_lower_edge h strand j p hpi hpj).trans hj)))
  | lower i hi hpi =>
    cases hf with
    | upper j _ hpj => exact False.elim (upper_lower_false l j i p hpj hpi)
    | middle strand hj hpj =>
      exact False.elim (hef (hi.symm.trans ((middle_lower_edge h strand i p hpj hpi).symm.trans hj)))
    | lower j hj hpj =>
      have hij : i ≠ j := by intro hh; subst j; exact hef (hi.symm.trans hj)
      exact False.elim (lower_lower_false h hij p hpi hpj)

/-- Apply the source-layer separation theorem to the actual polynomial-time emitted connection list. -/
theorem Layer.trace_separated {l : Layer} (h : l.HasDrawing) {e f : ℕ} (hef : e ≠ f)
    {p : GridRouting.Point} (he : Route.Trace l.connections e p) (hf : Route.Trace l.connections f p) :
    p = l.vertexPoint :=
  Layer.TracePart.separated h hef (l.trace_classified h he) (l.trace_classified h hf)

end PushPuzzle.PushFS.Reduction.Plan
