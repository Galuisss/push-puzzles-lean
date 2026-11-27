/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.Plan
public import PushFS.Reduction.RoutingData
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word.Orthogonal

/-!
# Executable routing bands for source layers

Every checked plane layer expands its three ports inside two disjoint ordered
routing bands. The raw column tables and layer height are computed from the
actual numbered source state. The upstream typed drawing witnesses establish
their arity and boundary sizes.
-/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.Plan


open Cslib.Complexity.NCL Turing.MultiTapeTM ComputableInPolyTime
open scoped NCL PushPuzzle.PushFS.Reduction

/-- The exact source compiler state after this layer. -/
def Layer.after (l : Layer) : Word.State := l.instruction.run l.before

/-- Expand the adjacent gate ports while preserving the surrounding wire order. -/
def expanded (k a i : ℕ) : ℕ :=
  if i < k then 4 * i
  else if i < k + a then 4 * k + (i - k)
  else 4 * k + 4 + 4 * (i - (k + a))

/-- Top standard columns to expanded input columns. -/
def Layer.upperBand (l : Layer) : Band :=
  ⟨(List.range l.before.wires.length).map (4 * ·),
    (List.range l.before.wires.length).map (expanded l.instruction.data.offset l.instruction.data.inputs.length)⟩

/-- Expanded output columns back to the standard bottom columns. -/
def Layer.lowerBand (l : Layer) : Band :=
  ⟨(List.range l.after.wires.length).map (expanded l.instruction.data.offset l.instruction.data.outputs.length),
    (List.range l.after.wires.length).map (4 * ·)⟩

/-- Two routing bands and the intervening three-port cell band. -/
def Layer.height (l : Layer) : ℕ :=
  2 * (l.before.wires.length + 1) + 2 + 2 * (l.after.wires.length + 1)

/-- A source layer has the actual typed drawing supplied by the checked plane word. -/
def Layer.HasDrawing (l : Layer) : Prop :=
  ∃ source target : List Color, ∃ _D : l.instruction.OrthogonalDrawing source target,
    l.before.wires.length = source.length

private theorem run_wires_length {sl : Slice} {source target : List Color}
    (D : sl.OrthogonalDrawing source target) (st : Word.State)
    (hlen : st.wires.length = source.length) : (sl.run st).wires.length = target.length := by
  rw [D.layer_eq]
  have hs := congrArg List.length D.source_eq
  have ht := congrArg List.length D.target_eq
  simp only [List.length_append] at hs ht
  simp only [Slice.run, List.length_append, List.length_take, List.length_ofFn, List.length_drop]
  omega

private theorem annotateFrom_hasDrawing {w : Word} {a b : List Color}
    (D : w.OrthogonalDrawing a b) (st : Word.State) (hlen : st.wires.length = a.length) :
    ∀ l ∈ annotateFrom w st, l.HasDrawing := by
  induction D generalizing st with
  | nil a => intro l hl; cases hl
  | cons layer rest ih =>
    intro l hl
    rcases List.mem_cons.mp hl with rfl | hl
    · exact ⟨_, _, layer, hlen⟩
    · exact ih _ (run_wires_length layer st hlen) l hl

/-- Every actual planned layer of a checked closed plane word has the required geometry. -/
theorem layer_hasDrawing {w : Word} (hP : w.checkPlane = true) (hT : w.WellTyped [] [])
    {l : Layer} (hl : l ∈ annotate w) : l.HasDrawing := by
  obtain ⟨D⟩ := Word.orthogonalDrawing hP hT
  exact annotateFrom_hasDrawing D ⟨[], 0, []⟩ rfl l hl

/-- The raw structural metadata specify a single three-port cell inside the current wire stack. -/
theorem Layer.HasDrawing.constraints {l : Layer} (h : l.HasDrawing) :
    l.instruction.data.isSwap = false ∧
      l.instruction.data.inputs.length + l.instruction.data.outputs.length = 3 ∧
      l.instruction.data.offset + l.instruction.data.inputs.length ≤ l.before.wires.length ∧
      l.after.wires.length = l.before.wires.length - l.instruction.data.inputs.length +
        l.instruction.data.outputs.length := by
  obtain ⟨source, target, D, hlen⟩ := h
  have hs := congrArg List.length D.source_eq
  have htlen := congrArg List.length D.target_eq
  simp only [List.length_append] at hs htlen
  have ht := run_wires_length D l.before hlen
  rw [D.layer_eq]
  dsimp only [Slice.data]
  refine ⟨rfl, D.layout.arity, by omega, ?_⟩
  change (l.instruction.run l.before).wires.length = _
  omega

private theorem ofFn_nat_eq_map_range {α : Type} (n : ℕ) (f : ℕ → α) :
    List.ofFn (fun i : Fin n => f i.val) = (List.range n).map f := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_map, List.length_range]
  · intro i _ _
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]

private theorem expanded_strictMono (k a n : ℕ) (ha : a ≤ 3) :
    StrictMono (fun i : Fin n => expanded k a i.val) := by
  intro i j hij
  unfold expanded
  dsimp only
  split_ifs <;> omega

private theorem upperBand_eq (l : Layer) : l.upperBand = Band.ofFunctions
    (fun i : Fin l.before.wires.length => 4 * i.val)
    (fun i => expanded l.instruction.data.offset l.instruction.data.inputs.length i.val) := by
  simp only [Layer.upperBand, Band.ofFunctions, ofFn_nat_eq_map_range]

private theorem lowerBand_eq (l : Layer) : l.lowerBand = Band.ofFunctions
    (fun i : Fin l.after.wires.length => expanded l.instruction.data.offset l.instruction.data.outputs.length i.val)
    (fun i => 4 * i.val) := by
  simp only [Layer.lowerBand, Band.ofFunctions, ofFn_nat_eq_map_range]

/-- Distinct raw top routes of a source layer have disjoint traces. -/
theorem Layer.upper_disjoint (l : Layer) (h : l.HasDrawing)
    {i j : Fin l.before.wires.length} (hij : i ≠ j) (p : NCL.GridRouting.Point) :
    ¬((∃ s ∈ Band.curve (l.upperBand, i.val), s.Contains p) ∧
      (∃ s ∈ Band.curve (l.upperBand, j.val), s.Contains p)) := by
  rw [upperBand_eq]
  exact Band.curves_disjoint _ _ (by intro i j hij; change 4 * i.val < 4 * j.val; omega)
    (expanded_strictMono _ _ _ (by have := h.constraints.2.1; omega)) hij p

/-- Distinct raw bottom routes of a source layer have disjoint traces. -/
theorem Layer.lower_disjoint (l : Layer) (h : l.HasDrawing)
    {i j : Fin l.after.wires.length} (hij : i ≠ j) (p : NCL.GridRouting.Point) :
    ¬((∃ s ∈ Band.curve (l.lowerBand, i.val), s.Contains p) ∧
      (∃ s ∈ Band.curve (l.lowerBand, j.val), s.Contains p)) := by
  rw [lowerBand_eq]
  exact Band.curves_disjoint _ _
    (expanded_strictMono _ _ _ (by have := h.constraints.2.1; omega))
    (by intro i j hij; change 4 * i.val < 4 * j.val; omega) hij p

@[fun_prop] theorem expanded_polyTime :
    ComputableInPolyTime (fun q : ℕ × ℕ × ℕ => expanded q.1 q.2.1 q.2.2)
      (encPair encUnary (encPair encUnary encUnary)) encUnary := by
  unfold expanded
  fun_prop

@[fun_prop] theorem Layer.after_polyTime :
    ComputableInPolyTime Layer.after encLayer Word.encState := by
  unfold Layer.after
  fun_prop

@[fun_prop] theorem Layer.upperBand_polyTime :
    ComputableInPolyTime Layer.upperBand encLayer encBand := by
  unfold Layer.upperBand
  fun_prop

@[fun_prop] theorem Layer.lowerBand_polyTime :
    ComputableInPolyTime Layer.lowerBand encLayer encBand := by
  unfold Layer.lowerBand
  fun_prop

@[fun_prop] theorem Layer.height_polyTime :
    ComputableInPolyTime Layer.height encLayer encUnary := by
  unfold Layer.height
  fun_prop

end PushPuzzle.PushFS.Reduction.Plan
