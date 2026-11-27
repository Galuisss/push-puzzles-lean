/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortConstraintStep
public import PushS.CombNormalizedInputs
public import PushS.CombUpperPartition

/-!
# Standard native constraints of the same actual compiled contour

The existing actual contour compiler supplies every native edge bound. Its emitted normalized
direction vector is therefore legal in these same standard finite native constraint records,
and graph reachability uses the existing actual single-axis move relation.

## Main results

* `Comb.compile_graphData_bounded`: the actual native records retain all original contour axes.
* `Comb.computableInPolyTime_graphData`: standard polynomial-time actual contour graph emission.
* `Comb.ConfigurationInput.normalizedAxes_nativeLegal`: original legality gives the same actual
  normalized native configuration.
-/

public section

namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

open _root_.Turing.MultiTapeTM

/-- The same actual emitted native constraint records retain all original contour axes. -/
theorem compile_graphData_bounded (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    (hedges : input.drawing.2.length = input.graph.edgeCount) :
    (compile width input).graphData.Bounded :=
  (compile width input).graphData_bounded (compile_upper_bounded width input hg hcount hedges)
    (compile_lower_bounded width input hg hcount)

/-- The actual compiled contour emits its same standard native constraint data in polynomial time.
-/
theorem computableInPolyTime_graphData (width : ℕ) :
    ComputableInPolyTime (fun input => (compile width input).graphData)
      encInput NCL.encAndOrGraph :=
  PortLayout.computableInPolyTime_graphData.comp (computableInPolyTime_compile width)

/-- Original native legality gives a legal normalized configuration of the same actual compiled
native constraint graph. -/
theorem ConfigurationInput.normalizedAxes_nativeLegal (width : ℕ) (x : ConfigurationInput)
    (hg : NCL.SourceValid x.input.graph) (hs : x.input.graph.graph.Legal (x.input.graph.config x.bits))
    (hcount : x.input.drawing.1.length = x.input.graph.vertices.length)
    (hedges : x.input.drawing.2.length = x.input.graph.edgeCount) :
    (compile width x.input).graphData.graph.Legal
      ((compile width x.input).graphData.config (x.normalizedAxes width)) :=
  ((compile width x.input).graphData_legal_iff
    (compile_graphData_bounded width x.input hg hcount hedges) _
      (length_normalizedAxes width x)).mpr
      (x.normalizedAxes_orderedInputs width hg hs hcount hedges).toInputLegal

end PushPuzzle.PushS.Comb
