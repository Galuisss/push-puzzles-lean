/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortCanonicalMacro
public import PushS.PortInstance

/-! The actual emitted canonical instance consumes the native frame-to-frame simulation. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS

/-- The actual emitted instance starts in the complete marked encoding at its common frame corner. -/
theorem physicalInstance_initial_eq_corner (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) :
    (l.physicalInstance p hl hM ha initial target).initial = (l.cornerState p initial).toState := rfl

/-- A native run between complete canonical frame states solves the original emitted storage instance. -/
theorem canonicalInstance_solvable_of_frame_reachable (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : List Bool)
    (hr : Reachable (l.canonicalInstance p hl hM ha initial target).board none
      (l.cornerState p (l.canonical initial)).toState (l.cornerState p (l.canonical target)).toState) :
    (l.canonicalInstance p hl hM ha initial target).Solvable :=
  ⟨_, hr, rfl⟩

/-- Each ordered legal interface-axis reversal solves its genuine complete wall-free canonical instance. -/
theorem canonicalInstance_single_axis_solvable (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (axes : List Bool) (hlegal : l.InputLegal axes) {port : ℕ} (hp : port < l.portCount)
    (gain : Bool) (hbefore : axes.getD port false = !gain) (hnew : l.OrderedInputs (axes.set port gain)) :
    (l.canonicalInstance p hl hM ha axes (axes.set port gain)).Solvable := by
  apply l.canonicalInstance_solvable_of_frame_reachable p hl hM ha
  exact l.encodedSegments_canonical_axis_from_frame p hl hM ha axes hlegal hp gain hbefore hnew _ rfl

end PushPuzzle.PushS.PortLayout
