/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombSubdivisionAxes
import all PushS.CombAxisVisits
import all PushS.CombConfiguration

/-! The actual emitter is the standard repeated native direction, with alternating references. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

private theorem edgeVisits_last (width : ℕ) (d : Graph.OrthogonalDrawing) (edge : ℕ) :
    (edgeVisits width d edge).getLast? = some (.tip edge true) := by
  change (_ ++ [Token.tip edge true]).getLast? = _
  exact List.getLast?_append_of_ne_nil _ (by simp)

private theorem endExtension_chain (width : ℕ) (x : ConfigurationInput)
    (drawing : NCL.GridDrawing.Closed x.input.graph.graph)
    (edge : Fin x.input.graph.edgeCount) (side : Bool) :
    (endExtension width x.input drawing edge side).IsChain
      (fun a b => x.tokenBit width a ≠ x.tokenBit width b) := by
  unfold endExtension
  split_ifs <;> simp only [List.isChain_nil, List.isChain_cons_cons, List.isChain_singleton, and_true]
  all_goals rw [x.rotation_sides]
  all_goals cases x.tokenBit width (.rotation _ true) <;> decide

private theorem falseExtension_boundary (width : ℕ) (x : ConfigurationInput) (hg : NCL.SourceValid x.input.graph)
    (drawing : NCL.GridDrawing.Closed x.input.graph.graph) (edge : Fin x.input.graph.edgeCount)
    {a b : Token} (ha : a ∈ (endExtension width x.input drawing edge false).getLast?)
    (hb : b ∈ (edgeVisits width x.input.drawing edge.val).head?) :
    x.tokenBit width a ≠ x.tokenBit width b := by
  by_cases h : endToken width x.input drawing edge false = .tip edge.val false
  · simp only [endExtension, h, ite_true, List.getLast?_nil, Option.not_mem_none] at ha
  · have hr := (endToken_role width x.input hg drawing edge false).resolve_left h
    have he := x.endToken_bit width hg drawing edge false
    rw [hr] at he
    simp only [endExtension, h, ite_false, Bool.false_eq_true, List.getLast?_cons,
      List.getLast?_nil, Option.getD_none, Option.getD_some, Option.mem_def, Option.some.injEq] at ha
    have hb' : .tip edge.val false = b := by simpa only [edgeVisits, List.singleton_append,
      List.cons_append, List.head?_cons, Option.mem_def, Option.some.injEq] using hb
    rw [← ha, ← hb', x.rotation_sides, he]
    change (!(x.bits.getD edge.val false ^^ false)) ≠ (x.bits.getD edge.val false ^^ false)
    cases x.bits.getD edge.val false <;> decide

private theorem trueExtension_boundary (width : ℕ) (x : ConfigurationInput) (hg : NCL.SourceValid x.input.graph)
    (drawing : NCL.GridDrawing.Closed x.input.graph.graph) (edge : Fin x.input.graph.edgeCount)
    {a b : Token} (ha : a ∈ (endExtension width x.input drawing edge false ++
      edgeVisits width x.input.drawing edge.val).getLast?)
    (hb : b ∈ (endExtension width x.input drawing edge true).head?) :
    x.tokenBit width a ≠ x.tokenBit width b := by
  by_cases h : endToken width x.input drawing edge true = .tip edge.val true
  · simp only [endExtension, h, ite_true, List.head?_nil, Option.not_mem_none] at hb
  · have hr := (endToken_role width x.input hg drawing edge true).resolve_left h
    have he := x.endToken_bit width hg drawing edge true
    rw [hr] at he
    have ha' : .tip edge.val true = a := by
      simpa only [List.getLast?_append, edgeVisits_last, Option.some_or, Option.mem_def,
        Option.some.injEq] using ha
    simp only [endExtension, h, ite_false, ite_true, List.head?_cons, Option.mem_def,
      Option.some.injEq] at hb
    rw [← ha', ← hb, x.rotation_sides, he]
    change (x.bits.getD edge.val false ^^ true) ≠ (!(x.bits.getD edge.val false ^^ true))
    cases x.bits.getD edge.val false <;> decide

/-- The full actual axis chain alternates at every original fragment, crossing, and rotation.
-/
theorem ConfigurationInput.axisVisits_alternate (width : ℕ) (x : ConfigurationInput)
    (hg : NCL.SourceValid x.input.graph) (drawing : NCL.GridDrawing.Closed x.input.graph.graph)
    (edge : Fin x.input.graph.edgeCount) :
    (axisVisits width x.input drawing edge).IsChain
      (fun a b => x.tokenBit width a ≠ x.tokenBit width b) := by
  exact ((endExtension_chain width x drawing edge false).append
    (x.edgeVisits_alternate width edge.val)
    (fun _ ha _ hb => falseExtension_boundary width x hg drawing edge ha hb)).append
    (endExtension_chain width x drawing edge true)
    (fun _ ha _ hb => trueExtension_boundary width x hg drawing edge ha hb)

private theorem boolChain_get {α : Type} (value : α → Bool) (head : α) (tail : List α)
    (hc : (head :: tail).IsChain (fun a b => value a ≠ value b))
    (index : Fin (head :: tail).length) :
    value ((head :: tail).get index) = (value head ^^ decide (index.val % 2 = 1)) := by
  induction tail generalizing head with
  | nil =>
    have hi : index = 0 := Fin.ext (by
      change index.val = 0
      have hi := index.isLt
      simp only [List.length_cons, List.length_nil] at hi
      omega)
    subst index
    simp
  | cons next tail ih =>
    rcases index with ⟨index, hi⟩
    cases index with
    | zero => simp
    | succ index =>
      have hi' : index < (next :: tail).length := by simpa only [List.length_cons,
        Nat.add_lt_add_iff_right] using hi
      rw [List.get_cons_succ, ih next hc.tail ⟨index, hi'⟩]
      have hn := hc.rel
      have hmod := Nat.mod_lt index (by omega : 0 < 2)
      cases ha : value head <;> cases hb : value next <;>
        simp only [ha, hb] at hn ⊢ <;> first
        | exact False.elim (hn rfl)
        | rcases (by omega : index % 2 = 0 ∨ index % 2 = 1) with h | h <;>
            simp [Nat.add_mod, h]

/-- Every actual standard subdivision segment emits its original edge bit with its literal parity.
-/
theorem ConfigurationInput.segmentToken_bit (width : ℕ) (x : ConfigurationInput)
    (hg : NCL.SourceValid x.input.graph) (drawing : NCL.GridDrawing.Closed x.input.graph.graph)
    (segment : NCL.ConstraintGraph.Subdivision.Segment (axisJointCount width x.input drawing)) :
    x.tokenBit width (segmentToken width x.input drawing segment) =
      (x.bits.getD segment.1.val false ^^ decide (segment.2.val % 2 = 1)) := by
  have hget : segmentToken width x.input drawing segment =
      (axisVisits width x.input drawing segment.1).getD segment.2.val (.tip 0 false) := by
    symm
    unfold segmentToken
    exact List.getD_eq_get _ _ ⟨segment.2.val, _⟩
  rw [hget]
  have hc := x.axisVisits_alternate width hg drawing segment.1
  have hh := axisVisits_head width x.input hg drawing segment.1
  generalize hword : axisVisits width x.input drawing segment.1 = word at hc hh ⊢
  cases word with
  | nil => simp at hh
  | cons head tail =>
    have he : head = endToken width x.input drawing segment.1 false := Option.some.inj hh
    have hi : segment.2.val < (head :: tail).length := by
      rw [← hword, ← axisJointCount_add_one]
      exact segment.2.isLt
    rw [List.getD_eq_get _ _ ⟨segment.2.val, hi⟩, boolChain_get _ head tail hc,
      he, x.endToken_bit width hg drawing segment.1 false]
    simp only [Bool.xor_false]

/-- The same original segment's reference bit is its literal position parity. -/
@[expose] def axisParity (width : ℕ) (input : Input)
    (drawing : NCL.GridDrawing.Closed input.graph.graph)
    (segment : NCL.ConstraintGraph.Subdivision.Segment (axisJointCount width input drawing)) : Bool :=
  decide (segment.2.val % 2 = 1)

/-- Original false endpoints retain the original reference direction. -/
theorem axisParity_first (width : ℕ) (input : Input)
    (drawing : NCL.GridDrawing.Closed input.graph.graph) (edge : Fin input.graph.edgeCount) :
    axisParity width input drawing (NCL.ConstraintGraph.Subdivision.first
      (axisJointCount width input drawing) edge) = false := by
  rfl

/-- Original true endpoints have the reversed actual axis reference direction. -/
theorem axisParity_last (width : ℕ) (input : Input)
    (drawing : NCL.GridDrawing.Closed input.graph.graph) (edge : Fin input.graph.edgeCount) :
    axisParity width input drawing (NCL.ConstraintGraph.Subdivision.last
      (axisJointCount width input drawing) edge) = true := by
  have hp := axisVisits_length width input drawing edge
  have he : axisJointCount width input drawing edge % 2 = 1 := by
    simp only [axisJointCount]
    omega
  simp only [axisParity, NCL.ConstraintGraph.Subdivision.last, Fin.val_last, he, decide_true]

/-- Actual emitted axes are precisely standard repeated native directions in these same references.
-/
theorem ConfigurationInput.axes_subdivisionAxisEquiv (width : ℕ) (x : ConfigurationInput)
    (hg : NCL.SourceValid x.input.graph)
    (hcount : x.input.drawing.1.length = x.input.graph.vertices.length)
    (hedges : x.input.drawing.2.length = x.input.graph.edgeCount)
    (drawing : NCL.GridDrawing.Closed x.input.graph.graph)
    (segment : NCL.ConstraintGraph.Subdivision.Segment (axisJointCount width x.input drawing)) :
    (x.axes width).getD (subdivisionAxisEquiv width x.input hg hcount hedges drawing segment).val false =
      (axisParity width x.input drawing segment ^^
        NCL.ConstraintGraph.Subdivision.enc (axisJointCount width x.input drawing)
          (x.input.graph.config x.bits) segment) := by
  rw [subdivisionAxisEquiv_val, x.axes_rank width
    (axisVisits_mem_cut width x.input hg hcount hedges drawing _ (segmentToken_mem width x.input drawing segment)),
    x.segmentToken_bit width hg drawing segment]
  exact Bool.xor_comm _ _

end PushPuzzle.PushS.Comb
