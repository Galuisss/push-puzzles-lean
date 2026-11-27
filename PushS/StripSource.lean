/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.HWord.Strip.Reduction
public import PushS.CombTopologyPolyTime

/-!
# The standard native strip source of the wall-free compiler

Use the actual PSPACE-hard native AND/OR strip instances, retaining their original graph,
configuration vectors, and standard drawing arrays. The contour compiler reads the original
graph and drawing directly.

## Main definitions

* `StripSource.toComb`: the original native graph and its original standard drawing arrays.
* `StripSource.layout`: the same actual contour compiler applied to this standard source.

## Main results

* `StripSource.computableInPolyTime_layout`: standard polynomial-time contour emission.
* `StripSource.exists_pspaceHard`: fixed-width native strip source hardness.
-/

public section

namespace PushPuzzle.PushS.StripSource

open Cslib.Complexity

open _root_.Turing.MultiTapeTM

/-- The same standard native strip source instance. -/
abbrev Instance := PushPuzzle.NCL.StripAndOrNCL.Instance

/-- The same standard native graph/configuration/drawing encoding. -/
abbrev encoding := PushPuzzle.NCL.encStripAndOrNCL

/-- Original native AND/OR reachability with fixed complete strip geometry. -/
abbrev language := PushPuzzle.NCL.StripAndOrNCL

/-- Read the original native graph and its original standard vertex and edge-route arrays. -/
@[expose] def toComb (x : Instance) : Comb.Input := ⟨x.ncl.graph, x.drawing⟩

/-- The standard source-to-contour input map is polynomial-time. -/
theorem computableInPolyTime_toComb :
    ComputableInPolyTime toComb encoding Comb.encInput := by
  have hn := PushPuzzle.NCL.encStripAndOrNCL_ncl_polyTime (ComputableInPolyTime.id' (encIn := encoding))
  exact Comb.encInput_mk_polyTime (NCL.encAndOrNCL_graph_polyTime hn)
    (PushPuzzle.NCL.encStripAndOrNCL_drawing_polyTime ComputableInPolyTime.id')

/-- The actual contour compiler on the same original native source data. -/
@[expose] def layout (width : ℕ) (x : Instance) : PortLayout := Comb.compile width (toComb x)

/-- The same actual contour and port layout emit in standard encoded polynomial time. -/
theorem computableInPolyTime_layout (width : ℕ) :
    ComputableInPolyTime (layout width) encoding encPortLayout :=
  (Comb.computableInPolyTime_compile width).comp computableInPolyTime_toComb

/-- Fixed-width, fixed-whole-route-span native strip reachability is PSPACE-hard. -/
theorem exists_pspaceHard :
    ∃ width span, PSPACEHard encoding (language width span) :=
  PushPuzzle.NCL.exists_StripAndOrNCL_pspaceHard

end PushPuzzle.PushS.StripSource
