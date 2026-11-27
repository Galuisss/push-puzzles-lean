/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.StripSource
public import PushS.CombConfigurationCore
public import PushS.CombNormalizedInputs

/-!
# The actual source's initial and target contour directions

Feed the standard native initial and target vectors into the same actual contour-direction
emitter. Both arrays have exactly one bit per actual emitted port and retain every original
core's weighted threshold.

## Main definitions

* `StripSource.initialAxes`, `targetAxes`: original native directions in contour order.

## Main results

* `StripSource.computableInPolyTime_initialAxes`, `computableInPolyTime_targetAxes`:
  standard polynomial-time emission.
-/

public section

namespace PushPuzzle.PushS.StripSource

open Cslib.Complexity

open _root_.Turing.MultiTapeTM

/-- The same native initial direction vector in the actual original contour order. -/
@[expose] def initialAxes (width : ℕ) (x : Instance) : List Bool :=
  (Comb.ConfigurationInput.mk (toComb x) x.ncl.initial).axes width

/-- The same native target direction vector in the actual original contour order. -/
@[expose] def targetAxes (width : ℕ) (x : Instance) : List Bool :=
  (Comb.ConfigurationInput.mk (toComb x) x.ncl.target).axes width

/-- The same original native initial bits emit in standard polynomial-time contour order. -/
theorem computableInPolyTime_initialAxes (width : ℕ) :
    ComputableInPolyTime (initialAxes width) encoding (encList encBool) := by
  have hn := PushPuzzle.NCL.encStripAndOrNCL_ncl_polyTime (ComputableInPolyTime.id' (encIn := encoding))
  have hb := NCL.encAndOrNCL_initial_polyTime hn
  exact (Comb.computableInPolyTime_axes width).comp
    (Comb.encConfigurationInput_mk_polyTime computableInPolyTime_toComb hb)

/-- The same original native target bits emit in standard polynomial-time contour order. -/
theorem computableInPolyTime_targetAxes (width : ℕ) :
    ComputableInPolyTime (targetAxes width) encoding (encList encBool) := by
  have hn := PushPuzzle.NCL.encStripAndOrNCL_ncl_polyTime (ComputableInPolyTime.id' (encIn := encoding))
  have hb := NCL.encAndOrNCL_target_polyTime hn
  exact (Comb.computableInPolyTime_axes width).comp
    (Comb.encConfigurationInput_mk_polyTime computableInPolyTime_toComb hb)

/-- Every actual contour port has exactly one original initial direction bit. -/
theorem length_initialAxes (width : ℕ) (x : Instance) :
    (initialAxes width x).length = (layout width x).portCount := Comb.length_axes _ _

/-- Every actual contour port has exactly one original target direction bit. -/
theorem length_targetAxes (width : ℕ) (x : Instance) :
    (targetAxes width x).length = (layout width x).portCount := Comb.length_axes _ _

/-- The actual initial contour direction vector with normalized AND demands. -/
def normalizedInitialAxes (width : ℕ) (x : Instance) : List Bool :=
  (Comb.ConfigurationInput.mk (toComb x) x.ncl.initial).normalizedAxes width

/-- The actual target contour direction vector with normalized AND demands. -/
def normalizedTargetAxes (width : ℕ) (x : Instance) : List Bool :=
  (Comb.ConfigurationInput.mk (toComb x) x.ncl.target).normalizedAxes width

/-- The same original normalized initial directions emit in standard polynomial time. -/
theorem computableInPolyTime_normalizedInitialAxes (width : ℕ) :
    ComputableInPolyTime (normalizedInitialAxes width) encoding (encList encBool) := by
  have hn := PushPuzzle.NCL.encStripAndOrNCL_ncl_polyTime (ComputableInPolyTime.id' (encIn := encoding))
  have hb := NCL.encAndOrNCL_initial_polyTime hn
  exact (Comb.computableInPolyTime_normalizedAxes width).comp
    (Comb.encConfigurationInput_mk_polyTime computableInPolyTime_toComb hb)

/-- The same original normalized target directions emit in standard polynomial time. -/
theorem computableInPolyTime_normalizedTargetAxes (width : ℕ) :
    ComputableInPolyTime (normalizedTargetAxes width) encoding (encList encBool) := by
  have hn := PushPuzzle.NCL.encStripAndOrNCL_ncl_polyTime (ComputableInPolyTime.id' (encIn := encoding))
  have hb := NCL.encAndOrNCL_target_polyTime hn
  exact (Comb.computableInPolyTime_normalizedAxes width).comp
    (Comb.encConfigurationInput_mk_polyTime computableInPolyTime_toComb hb)

private theorem source_ordered {width span : ℕ} {x : Instance} (hx : x ∈ language width span)
    (bits : List Bool) (hs : x.ncl.graph.graph.Legal (x.ncl.graph.config bits)) :
    (layout width x).OrderedInputs
      ((Comb.ConfigurationInput.mk (toComb x) bits).normalizedAxes width) := by
  obtain ⟨P, he, _⟩ := hx.2.2
  have hcount : x.drawing.1.length = x.ncl.graph.vertices.length := by
    rw [← he]
    exact List.length_ofFn
  have hedges : x.drawing.2.length = x.ncl.graph.edgeCount := by
    rw [← he]
    exact List.length_ofFn
  exact (Comb.ConfigurationInput.mk (toComb x) bits).normalizedAxes_orderedInputs width
    (NCL.SourceValid.ofValid hx.1.1 hx.2.1) hs hcount hedges

/-- Every accepted original strip source emits ordered legal initial contour inputs. -/
theorem normalizedInitialAxes_ordered {width span : ℕ} {x : Instance}
    (hx : x ∈ language width span) :
    (layout width x).OrderedInputs (normalizedInitialAxes width x) :=
  source_ordered hx x.ncl.initial hx.1.2.2.2.1

/-- Every accepted original strip source emits ordered legal target contour inputs. -/
theorem normalizedTargetAxes_ordered {width span : ℕ} {x : Instance}
    (hx : x ∈ language width span) :
    (layout width x).OrderedInputs (normalizedTargetAxes width x) :=
  source_ordered hx x.ncl.target (hx.1.2.2.2.2.legal hx.1.2.2.2.1)

end PushPuzzle.PushS.StripSource
