/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombAxisInventory
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.Subdivision

/-! Standard native subdivision segments are precisely the actual emitted contour axes. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

/-- The number of actual ordinary joints between this original edge's consecutive axes. -/
@[expose] def axisJointCount (width : ℕ) (input : Input)
    (drawing : NCL.GridDrawing.Closed input.graph.graph) (edge : Fin input.graph.edgeCount) : ℕ :=
  (axisVisits width input drawing edge).length - 1

/-- The standard subdivision's segment count equals the complete actual original-edge word. -/
theorem axisJointCount_add_one (width : ℕ) (input : Input)
    (drawing : NCL.GridDrawing.Closed input.graph.graph) (edge : Fin input.graph.edgeCount) :
    axisJointCount width input drawing edge + 1 = (axisVisits width input drawing edge).length := by
  have hp := (axisVisits_length width input drawing edge).1
  simp only [axisJointCount]
  omega

/-- The literal actual token of a standard subdivision segment. -/
@[expose] def segmentToken (width : ℕ) (input : Input)
    (drawing : NCL.GridDrawing.Closed input.graph.graph)
    (segment : NCL.ConstraintGraph.Subdivision.Segment (axisJointCount width input drawing)) : Token :=
  (axisVisits width input drawing segment.1).get
    ⟨segment.2.val, by rw [← axisJointCount_add_one]; exact segment.2.isLt⟩

/-- Every standard subdivision segment reads one actual original-edge occurrence. -/
theorem segmentToken_mem (width : ℕ) (input : Input)
    (drawing : NCL.GridDrawing.Closed input.graph.graph)
    (segment : NCL.ConstraintGraph.Subdivision.Segment (axisJointCount width input drawing)) :
    segmentToken width input drawing segment ∈ axisVisits width input drawing segment.1 :=
  List.get_mem _ _

/-- Actual subdivision occurrences retain the same original edge and literal axis index. -/
theorem segmentToken_injective (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (drawing : NCL.GridDrawing.Closed input.graph.graph) :
    Function.Injective (segmentToken width input drawing) := by
  intro left right he
  have hl := segmentToken_mem width input drawing left
  have hr := segmentToken_mem width input drawing right
  have heq : left.1 = right.1 := by
    by_contra hne
    exact List.disjoint_left.mp (axisVisits_disjoint width input hg drawing hne) hl (he ▸ hr)
  rcases left with ⟨edge, a⟩
  rcases right with ⟨_, b⟩
  cases heq
  have hi := (axisVisits_nodup width input drawing edge).get_inj_iff.mp he
  have hval : a.val = b.val := congrArg (fun i : Fin (axisVisits width input drawing edge).length => i.val) hi
  exact Sigma.ext rfl (heq_of_eq (Fin.ext hval))

/-- The original native segment's literal position in the same actual contour. -/
@[expose] def segmentAxis (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    (hedges : input.drawing.2.length = input.graph.edgeCount)
    (drawing : NCL.GridDrawing.Closed input.graph.graph)
    (segment : NCL.ConstraintGraph.Subdivision.Segment (axisJointCount width input drawing)) :
    Fin (compile width input).portCount :=
  ⟨(cut width input).rank (segmentToken width input drawing segment),
    (cut width input).rank_lt (axisVisits_mem_cut width input hg hcount hedges drawing
      segment.1 (segmentToken_mem width input drawing segment))⟩

private theorem segmentAxis_bijective (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    (hedges : input.drawing.2.length = input.graph.edgeCount)
    (drawing : NCL.GridDrawing.Closed input.graph.graph) :
    Function.Bijective (segmentAxis width input hg hcount hedges drawing) := by
  constructor
  · intro left right he
    apply segmentToken_injective width input hg drawing
    exact (cut width input).rank_injective
      (axisVisits_mem_cut width input hg hcount hedges drawing _ (segmentToken_mem width input drawing left))
      (congrArg Fin.val he)
  · intro axis
    let token := (cut width input).order.get axis
    have ht := List.get_mem (cut width input).order axis
    obtain ⟨edge, he⟩ := exists_axisVisits width input hg hcount hedges drawing ht
    obtain ⟨index, hi⟩ := List.mem_iff_get.mp he
    let segment : NCL.ConstraintGraph.Subdivision.Segment (axisJointCount width input drawing) :=
      ⟨edge, ⟨index.val, by rw [axisJointCount_add_one]; exact index.isLt⟩⟩
    have htoken : segmentToken width input drawing segment = token := hi
    refine ⟨segment, Fin.ext ?_⟩
    change (cut width input).rank (segmentToken width input drawing segment) = axis.val
    rw [htoken]
    change (cut width input).order.idxOf ((cut width input).order[axis.val]) = axis.val
    exact (cut_order_nodup width input hg hcount).idxOf_getElem axis.val axis.isLt

/-- The same actual axis inventory is a renaming of the original graph's standard subdivision.
-/
noncomputable def subdivisionAxisEquiv (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    (hedges : input.drawing.2.length = input.graph.edgeCount)
    (drawing : NCL.GridDrawing.Closed input.graph.graph) :
    NCL.ConstraintGraph.Subdivision.Segment (axisJointCount width input drawing) ≃
      Fin (compile width input).portCount :=
  Equiv.ofBijective (segmentAxis width input hg hcount hedges drawing)
    (segmentAxis_bijective width input hg hcount hedges drawing)

/-- The native subdivision renaming reads the literal original token's actual contour rank. -/
theorem subdivisionAxisEquiv_val (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    (hedges : input.drawing.2.length = input.graph.edgeCount)
    (drawing : NCL.GridDrawing.Closed input.graph.graph)
    (segment : NCL.ConstraintGraph.Subdivision.Segment (axisJointCount width input drawing)) :
    (subdivisionAxisEquiv width input hg hcount hedges drawing segment).val =
      (cut width input).rank (segmentToken width input drawing segment) := by
  simp only [subdivisionAxisEquiv, Equiv.ofBijective_apply, segmentAxis]

end PushPuzzle.PushS.Comb
