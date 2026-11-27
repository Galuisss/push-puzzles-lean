/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceRailReadoutFailure
public import Push.FirstExit
import all PushS.PortOrdinaryFailure

/-! Ordinary first-failure propagation from genuine train motions and frozen endpoint boundary boxes. -/

public section
namespace PushPuzzle.Push.AcceptanceOrdinaryFailure

open PushFS PushS PushS.PortLayout AcceptanceAxisReadout

/-- The frozen outward and diagonal neighbours of one actual ordinary pocket. -/
structure BoundaryBoxes (p : Scales.Parameters) (e : Endpoint)
    (u : State (p.W + 1) (p.H + 1)) : Prop where
  outward : ∀ q : Cell (p.W + 1) (p.H + 1),
    (if e.inward then (q.1.val : ℤ) - p.x e.port else (p.x e.port : ℤ) - q.1.val) = -1 →
    (if e.side = .upper then q.2.val else p.H - q.2.val) = readDepth p e.level → q ∈ u.boxes
  diagonal : ∀ q : Cell (p.W + 1) (p.H + 1),
    ((if e.inward then (q.1.val : ℤ) - p.x e.port else (p.x e.port : ℤ) - q.1.val) = -1 ∨
      (if e.inward then (q.1.val : ℤ) - p.x e.port else (p.x e.port : ℤ) - q.1.val) = 1) →
    ((if e.side = .upper then q.2.val else p.H - q.2.val) = readDepth p e.level - 1 ∨
      (if e.side = .upper then q.2.val else p.H - q.2.val) = readDepth p e.level + 1) → q ∈ u.boxes

/-- Every outside neighbour of a failed ordinary pocket is occupied. -/
private theorem fault_boundary {p : Scales.Parameters} {e : Endpoint} {u : State (p.W + 1)
    (p.H + 1)}
    (boundary : BoundaryBoxes p e u) (depth : 3 ≤ readDepth p e.level) (fault : OrdinaryFaultReadout p e u)
    {d : Direction} {q r : Cell (p.W + 1) (p.H + 1)} (adjacent : Adjacent d q r)
    (outside : q ∉ ordinaryPocket p e) (inside : r ∈ ordinaryPocket p e) : q ∈ u.boxes := by
  have hH := readDepth_add_lt_H p e.level
  have hq := q.2.isLt
  rcases outside_neighbor p e adjacent outside inside depth with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · apply fault.axis_word.fault_axis_box fault.axis_failed depth ?_ hy
    cases hi : e.inward <;> simp only [localX, hi, Bool.false_eq_true, ite_false, ite_true] at hx <;> omega
  · apply fault.horizontal_word.fault_probe_box fault.horizontal_failed
    · cases hi : e.inward <;> simp only [localX, hi, Bool.false_eq_true, ite_false, ite_true] at hx ⊢ <;> omega
    · cases hs : e.side <;> simp only [localDepth, hs, reduceCtorEq, ite_false, ite_true] at hy ⊢ <;> omega
  · exact boundary.outward q hx hy
  · exact boundary.diagonal q hx hy

/-- A real step cannot enter a failed ordinary pocket from outside its occupied boundary. -/
theorem no_entry {p : Scales.Parameters} {e : Endpoint} {B : Board (p.W + 1) (p.H + 1)}
    {u v : State (p.W + 1) (p.H + 1)} (boundary : BoundaryBoxes p e u)
    (depth : 3 ≤ readDepth p e.level) (step : Step B none u v) (fault : OrdinaryFaultReadout p e u)
    (outside : u.player ∉ ordinaryPocket p e) : v.player ∉ ordinaryPocket p e := by
  intro inside
  exact step.choose_spec.valid_source.2.2
    (fault_boundary boundary depth fault (players_adjacent step.choose_spec) outside inside)

/-- Actual axis and rail motions preserve the complete ordinary fault and its outside player. -/
theorem step (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    {B : Board (p.W + 1) (p.H + 1)} {u v : State (p.W + 1) (p.H + 1)}
    (axis : AxisMotions l p u v) (rail : RailMotions l p B u v) (e : Endpoint) (he : e ∈ l.endpoints)
    (boundary : BoundaryBoxes p e u) (move : Step B none u v)
    (fault : OrdinaryFaultReadout p e u) (outside : u.player ∉ ordinaryPocket p e) :
    ∃ _ : OrdinaryFaultReadout p e v, v.player ∉ ordinaryPocket p e := by
  have depth := readDepth_ge p (l.endpoints_level_bounds p hl hM he).1 (l.endpoints_level_bounds p hl hM he).2
  obtain ⟨parameter, shift, word, failed⟩ := endpoint_axis_failure_step_of_motions l p hl hM haxes axis e he
    fault.axis_word fault.axis_failed outside
  obtain ⟨horizontal, hword, hfailed⟩ := endpoint_horizontal_failure_step_of_motions l p hl haxes rail e he
    fault.horizontal_word fault.horizontal_failed outside
  exact ⟨⟨parameter, shift, horizontal, word, failed, hword, hfailed⟩, no_entry boundary (by omega) move fault outside⟩

/-- The first occurrence of an ordinary fault leaves its actual next player outside the pocket. -/
theorem onset (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    {B : Board (p.W + 1) (p.H + 1)} {u v : State (p.W + 1) (p.H + 1)}
    (axis : AxisMotions l p u v) (rail : RailMotions l p B u v) (e : Endpoint) (he : e ∈ l.endpoints)
    (move : Step B none u v) {parameter shift horizontal : ℕ}
    (axisWord : EndpointAxisReadout p e u parameter shift) (railWord : EndpointHorizontalReadout p e u horizontal)
    (fault : OrdinaryFaultReadout p e v) (source : ¬Nonempty (OrdinaryFaultReadout p e u)) :
    v.player ∉ ordinaryPocket p e := by
  by_cases supplied : parameter ≤ 1
  · exact endpoint_axis_loss_outside_of_motions l p hl hM haxes axis e he axisWord fault.axis_word
      supplied fault.axis_failed (players_adjacent move.choose_spec)
  · have suppliedRail : 2 ≤ horizontal := by
      by_contra failed
      exact source ⟨⟨parameter, shift, horizontal, axisWord, by omega, railWord, by omega⟩⟩
    exact endpoint_horizontal_loss_outside_of_motions l p hl haxes rail e he railWord fault.horizontal_word
      suppliedRail fault.horizontal_failed (players_adjacent move.choose_spec)

end PushPuzzle.Push.AcceptanceOrdinaryFailure
