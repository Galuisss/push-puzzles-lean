/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.StripSourceConfiguration
public import PushS.CombNormalizedReachability
import all PushS.StripSourceConfiguration

/-! Exact native reconfiguration of the original strip source's normalized contour vectors. -/

public section
namespace PushPuzzle.PushS.StripSource

open Cslib.Complexity

/-- The original native endpoint problem is exactly reachability of its actual normalized axes. -/
theorem normalizedAxes_reachable_iff (width : ℕ) (x : Instance) (hg : NCL.SourceValid x.ncl.graph)
    (hvertices : x.drawing.1.length = x.ncl.graph.vertices.length)
    (hedges : x.drawing.2.length = x.ncl.graph.edgeCount)
    (drawing : NCL.GridDrawing.Closed x.ncl.graph.graph)
    (hi : x.ncl.graph.graph.Legal (x.ncl.graph.config x.ncl.initial))
    (ht : x.ncl.graph.graph.Legal (x.ncl.graph.config x.ncl.target)) :
    x.ncl.graph.graph.Reachable (x.ncl.graph.config x.ncl.initial) (x.ncl.graph.config x.ncl.target) ↔
      Relation.ReflTransGen (layout width x).AxisStep
        (normalizedInitialAxes width x) (normalizedTargetAxes width x) :=
  Comb.normalizedAxes_reachable_iff width (toComb x) hg hvertices hedges drawing
    x.ncl.initial x.ncl.target hi ht

end PushPuzzle.PushS.StripSource
