/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombNormalizedReachability
public import PushS.PortOrderReachability
public import PushS.CombLower

/-! Original native reachability is exactly an ordered path between its same actual normalized axes. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

/-- The original legal native configurations reach each other exactly when their actual normalized
axis arrays admit a path using the original ordered single-axis relation. -/
theorem normalizedAxes_orderedReachable_iff (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    (hedges : input.drawing.2.length = input.graph.edgeCount)
    (drawing : NCL.GridDrawing.Closed input.graph.graph) (initial target : List Bool)
    (hi : input.graph.graph.Legal (input.graph.config initial))
    (ht : input.graph.graph.Legal (input.graph.config target)) :
    input.graph.graph.Reachable (input.graph.config initial) (input.graph.config target) ↔
      Relation.ReflTransGen (compile width input).OrderedAxisStep
        (ConfigurationInput.normalizedAxes width ⟨input, initial⟩)
        (ConfigurationInput.normalizedAxes width ⟨input, target⟩) :=
  (normalizedAxes_reachable_iff width input hg hcount hedges drawing initial target hi ht).trans
    ((compile width input).axisReachable_iff_orderedReachable (compile_lower_valid width input hg hcount) _ _
      (ConfigurationInput.normalizedAxes_orderedInputs width ⟨input, initial⟩ hg hi hcount hedges)
      (ConfigurationInput.normalizedAxes_orderedInputs width ⟨input, target⟩ hg ht hcount hedges))

end PushPuzzle.PushS.Comb
