/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceOrdinaryFailure
public import Push.AcceptanceSoundnessSupportFreeze
import all PushS.PortStreetSeparation
import all PushS.PortPageBackground
import all PushS.PortBackground

/-! Actual accepted trajectories supply the ordinary diagonal boundary boxes and initial outside player. -/

public section
namespace PushPuzzle.Push.AcceptanceOrdinaryFailure

open PushFS PushS PushS.PortLayout AcceptanceProgram AcceptanceSoundness

/-- The actual canonical source player starts outside every ordinary pocket. -/
theorem canonical_initial_outside (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (initial target : List Bool) (e : Endpoint) :
    (l.canonicalInstance p hl hM haxes initial target).initial.player ∉ ordinaryPocket p e := by
  have zero_outside (q : Cell (p.W + 1) (p.H + 1)) (hx : q.1.val = 0) : q ∉ ordinaryPocket p e := by
    intro inside
    have hx0 := readLength_add_lt_x p e.port 0
    simp only [ordinaryPocket, Finset.mem_filter, Finset.mem_univ, true_and, hx] at inside
    cases hi : e.inward <;> simp only [hi, Bool.false_eq_true, ite_false, ite_true] at inside <;> omega
  exact zero_outside _ rfl

/-- Only the outward work-row box remains to establish the ordinary boundary on an actual accepted run. -/
theorem canonical_boundary_of_outward (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (e : Endpoint) (he : e ∈ l.endpoints)
    (outward : ∀ q : Cell (p.W + 1) (p.H + 1),
      (if e.inward then (q.1.val : ℤ) - p.x e.port else (p.x e.port : ℤ) - q.1.val) = -1 →
      (if e.side = .upper then q.2.val else p.H - q.2.val) = readDepth p e.level → q ∈ u.boxes) :
    BoundaryBoxes p e u := by
  refine ⟨outward, ?_⟩
  intro q hx hy
  have hxe := x_even p e.port
  have hye := readDepth_even p e.level
  have hHe := H_even p
  have hD := readDepth_add_lt_D p e.level
  have hH : p.H = 2 * p.D := rfl
  have hqy := q.2.isLt
  have hY := readDepth_ge p (l.endpoints_level_bounds p hl hM he).1 (l.endpoints_level_bounds p hl hM he).2
  have hxodd : q.1.val % 2 = 1 := by
    cases hi : e.inward <;> simp only [hi, Bool.false_eq_true, ite_false, ite_true] at hx <;> omega
  have hyodd : q.2.val % 2 = 1 := by
    cases hs : e.side <;> simp only [hs, reduceCtorEq, ite_false, ite_true] at hy <;> omega
  apply canonical_background_full l p hl hM haxes initial target hsu hut accepted
  apply (l.mem_backgroundBoxes p q).mpr
  constructor
  · rintro (hcol | hrow)
    · have := l.streetColumnSet_even p hcol
      omega
    · have := l.workingRowSet_even p hrow
      omega
  · intro hc
    have hband := (Finset.mem_filter.mp hc).2
    cases hs : e.side <;> simp only [hs, reduceCtorEq, ite_false, ite_true] at hy <;> omega

end PushPuzzle.Push.AcceptanceOrdinaryFailure
