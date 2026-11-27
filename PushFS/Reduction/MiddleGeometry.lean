/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PathData
import Mathlib.Data.List.GetD

/-!
# The actual three-port middle-band programs

Each emitted middle route is exactly an upstream grid-star or bypass path.
Different strands meet only at the declared vertex and only when both are
gate arms. Thus all bypass wires are separated from the logical gate.
-/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.Plan


open Cslib.Complexity.NCL

/-- The finite strands crossing the actual middle band of a numbered layer. -/
abbrev Layer.Strand (l : Layer) := GridLayout.Strand l.instruction.data.offset
  l.instruction.data.inputs.length l.instruction.data.outputs.length
  (l.before.wires.length - (l.instruction.data.offset + l.instruction.data.inputs.length))

/-- Read a middle fragment from the exact lists emitted by the compiler. -/
def Layer.strandRoute (l : Layer) : l.Strand → Route
  | .inl i => l.prefixRoutes.getD i.val ⟨0, []⟩
  | .inr (.inl (.inl i)) => l.inputRoutes.getD i.val ⟨0, []⟩
  | .inr (.inl (.inr i)) => l.outputRoutes.getD i.val ⟨0, []⟩
  | .inr (.inr i) => l.suffixRoutes.getD i.val ⟨0, []⟩

/-- The corresponding endpoint-typed orthogonal path in its actual layer row. -/
def Layer.strandPath (l : Layer) (e : l.Strand) :=
  (GridLayout.middlePath e).translate 0 l.middleY

/-- Every raw middle fragment is exactly the complete geometric path serialization. -/
theorem Layer.strandRoute_path (l : Layer) (e : l.Strand) :
    (l.strandRoute e).path = segments (l.strandPath e) := by
  rcases e with i | ((i | i) | i)
  all_goals
    simp [Layer.strandRoute, Layer.strandPath, Layer.prefixRoutes, Layer.inputRoutes,
      Layer.outputRoutes, Layer.suffixRoutes, Layer.vertexPoint,
      GridLayout.middlePath, GridStar.path, GridRouting.Path.translate, segments, List.getD_eq_getElem?_getD, i.isLt,
      Nat.add_left_comm, Nat.add_comm]

private theorem middle_trace_iff (l : Layer) (e : l.Strand) (p : GridRouting.Point) :
    (∃ s ∈ (l.strandRoute e).path, s.Contains p) ↔
      l.middleY ≤ p.2 ∧ GridLayout.MiddleContains e (p.1, p.2 - l.middleY) := by
  rw [l.strandRoute_path, mem_segments_iff]
  simp only [Layer.strandPath, GridRouting.Path.contains_translate, Nat.zero_le,
    Nat.sub_zero, true_and, GridLayout.middlePath_contains_iff]

/-- Different actual middle routes meet only at their common source vertex. -/
theorem Layer.middle_intersection {l : Layer} (h : l.HasDrawing)
    {e f : l.Strand} (hef : e ≠ f) {p : GridRouting.Point}
    (he : ∃ s ∈ (l.strandRoute e).path, s.Contains p)
    (hf : ∃ s ∈ (l.strandRoute f).path, s.Contains p) :
    p = l.vertexPoint ∧ (∃ q, e = .inr (.inl q)) ∧ (∃ q, f = .inr (.inl q)) := by
  obtain ⟨hye, he⟩ := (middle_trace_iff l e p).mp he
  obtain ⟨_, hf⟩ := (middle_trace_iff l f p).mp hf
  obtain ⟨hp, he, hf⟩ := GridLayout.middle_intersection h.constraints.2.1 hef he hf
  refine ⟨?_, he, hf⟩
  have hx := congrArg Prod.fst hp
  have hy := congrArg Prod.snd hp
  apply Prod.ext
  · exact hx
  · change p.2 = l.middleY + 1
    dsimp only at hy
    omega

/-- All emitted middle pixels lie inside the two-row middle band. -/
theorem Layer.middle_row_bounds {l : Layer} (h : l.HasDrawing) (e : l.Strand)
    {p : GridRouting.Point} (hp : ∃ s ∈ (l.strandRoute e).path, s.Contains p) :
    l.middleY ≤ p.2 ∧ p.2 ≤ l.middleY + 2 := by
  obtain ⟨hlo, hp⟩ := (middle_trace_iff l e p).mp hp
  have hhi := GridLayout.middle_row_le h.constraints.2.1 hp
  exact ⟨hlo, by omega⟩

end PushPuzzle.PushFS.Reduction.Plan
