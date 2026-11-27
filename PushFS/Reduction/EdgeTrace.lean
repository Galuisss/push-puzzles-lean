/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.CutConnections
import Mathlib.Data.List.GetD

/-!
# Edge ownership of the emitted route pixels

The named trace is computable from the concrete segment table. Fresh numbering
makes each active or newly created edge select exactly one complete connection
in a layer. Allocated edges absent from the cut produce no later decoration.
-/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction


open Turing.MultiTapeTM ComputableInPolyTime
open scoped NCL PushPuzzle.PushFS.Reduction

/-- All represented pixels of one numbered edge. -/
def Route.Trace (rs : List Route) (edge : ℕ) (p : NCL.GridRouting.Point) : Prop :=
  ∃ r ∈ rs, r.edge = edge ∧ ∃ s ∈ r.path, s.Contains p

/-- The trace of concatenated fragment tables is their union. -/
theorem Route.trace_append (rs ss : List Route) (e : ℕ) (p : NCL.GridRouting.Point) :
    Route.Trace (rs ++ ss) e p ↔ Route.Trace rs e p ∨ Route.Trace ss e p := by
  simp only [Trace, List.mem_append, or_and_right, exists_or]

/-- Translating the fragment table transports its entire named trace. -/
theorem Route.trace_translate (rs : List Route) (e dx dy : ℕ) (p : NCL.GridRouting.Point) :
    Route.Trace (rs.map (fun r => r.translate dx dy)) e p ↔
      dx ≤ p.1 ∧ dy ≤ p.2 ∧ Route.Trace rs e (p.1 - dx, p.2 - dy) := by
  simp only [Trace, List.mem_map, exists_exists_and_eq_and, Route.translate,
    Segment.contains_translate]
  constructor
  · rintro ⟨r, hr, he, s, hs, hx, hy, hp⟩
    exact ⟨hx, hy, r, hr, he, s, hs, hp⟩
  · rintro ⟨hx, hy, r, hr, he, s, hs, hp⟩
    exact ⟨r, hr, he, s, hs, hx, hy, hp⟩

instance (s : Segment) (p : NCL.GridRouting.Point) : Decidable (s.Contains p) := by
  unfold Segment.Contains
  infer_instance

/-- Executable membership in a segment's complete closed trace. -/
def Segment.containsTest (q : Segment × ℕ × ℕ) : Bool :=
  decide (q.1.Contains q.2)

/-- Executable edge ownership in the emitted route table. -/
def Route.traceTest (q : List Route × ℕ × ℕ × ℕ) : Bool :=
  q.1.any fun r => (r.edge == q.2.1) &&
    r.path.any (fun s => Segment.containsTest (s, q.2.2))

@[fun_prop] theorem Segment.containsTest_polyTime :
    ComputableInPolyTime Segment.containsTest (encPair encSegment Bitmap.encPoint) encBool := by
  unfold Segment.containsTest Segment.Contains Bitmap.encPoint
  fun_prop

@[fun_prop] theorem Route.traceTest_polyTime :
    ComputableInPolyTime Route.traceTest
      (encPair (encList encRoute) (encPair encUnary Bitmap.encPoint)) encBool := by
  unfold Route.traceTest
  fun_prop

namespace Plan

/-- The current layer allocates precisely its declared output arity. -/
theorem Layer.after_next {l : Layer} (h : l.HasDrawing) :
    l.after.next = l.before.next + l.instruction.data.outputs.length := by
  obtain ⟨source, target, D, _⟩ := h
  unfold Layer.after
  rw [D.layer_eq]
  rfl

/-- The complete new cut is numbered by the same fresh-edge invariant. -/
theorem Layer.after_numbered {l : Layer} (hn : Numbered l.before) (h : l.HasDrawing) :
    Numbered l.after := hn.step h.constraints.1

/-- A previously allocated number absent from the cut stays absent after the gate. -/
theorem Layer.absent_after {l : Layer} (h : l.HasDrawing) {e : ℕ}
    (he : e < l.before.next) (ha : e ∉ l.before.wires) : e ∉ l.after.wires := by
  rw [l.after_wires h]
  intro hm
  rcases List.mem_append.mp hm with hm | hm
  · rcases List.mem_append.mp hm with hm | hm
    · exact ha (List.mem_of_mem_take hm)
    · obtain ⟨i, hi⟩ := List.mem_ofFn.mp hm
      omega
  · exact ha (List.mem_of_mem_drop hm)

/-- An incoming edge consumed at this vertex disappears from the next live cut. -/
theorem Layer.consumed_absent {l : Layer} (hn : Numbered l.before) (h : l.HasDrawing)
    (i : Fin l.before.wires.length) (hx : l.exitIndex i.val = none) :
    l.before.wires.getD i.val 0 ∉ l.after.wires := by
  have hinput : l.instruction.data.offset ≤ i.val ∧
      i.val < l.instruction.data.offset + l.instruction.data.inputs.length := by
    unfold Layer.exitIndex at hx
    split_ifs at hx; simp_all
  rw [l.after_wires h]
  intro hm
  rcases List.mem_append.mp hm with hm | hm
  · rcases List.mem_append.mp hm with hm | hm
    · have := hn.index_lt_of_mem_take i.isLt hm
      omega
    · obtain ⟨j, hj⟩ := List.mem_ofFn.mp hm
      have := hn.getD_lt i.isLt
      omega
  · have := hn.le_index_of_mem_drop i.isLt hm
    omega

/-- Every connection uses a number allocated by the end of the actual layer. -/
theorem Layer.connection_edge_lt {l : Layer} (hn : Numbered l.before) (h : l.HasDrawing)
    {r : Route} (hr : r ∈ l.connections) : r.edge < l.after.next := by
  rw [l.after_next h]
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    have hi' := List.mem_range.mp hi
    exact (hn.getD_lt hi').trans_le (Nat.le_add_right ..)
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    have hi' := List.mem_range.mp hi
    change l.before.next + i < l.before.next + l.instruction.data.outputs.length
    omega

/-- An absent allocated edge has no pixels anywhere in this layer's output. -/
theorem Layer.trace_absent {l : Layer} {e : ℕ} (he : e < l.before.next)
    (ha : e ∉ l.before.wires) (p : NCL.GridRouting.Point) : ¬Route.Trace l.connections e p := by
  rintro ⟨r, hr, heq, _⟩
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
    have hj' := List.mem_range.mp hj
    change l.before.wires.getD j 0 = e at heq
    rw [List.getD_eq_getElem _ _ hj'] at heq
    exact ha (heq ▸ List.getElem_mem hj')
  · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
    change l.before.next + j = e at heq
    omega

end Plan
end PushPuzzle.PushFS.Reduction
