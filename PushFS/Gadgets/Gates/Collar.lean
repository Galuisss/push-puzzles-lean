/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Gates.Macros
public import PushFS.Gadgets.Gates.Framing

/-!
# Real neighboring boxes in the overlapping port collars

For the changing port, the neighbor must occupy its permissive phase. The
other two ports retain their original phases. The checked movement footprint
avoids all these cells, so any actual boxes represented there stay fixed.
-/

@[expose] public section

namespace PushPuzzle.PushFS.Gadgets.Gates


-- Finite coordinate certificates inspect the explicit macro direction lists.
set_option maxRecDepth 65536
set_option maxHeartbeats 0

def neighborSignals (a b : Signals) : Signals :=
  ⟨if changingPort a b = 0 then true else a.left,
   if changingPort a b = 1 then true else a.upper,
   if changingPort a b = 2 then false else a.right⟩

def boundaryNeighbors (kind : Bool) (phase : Signals) : Finset C :=
  if kind then
    (if phase.left then ∅ else {(0,29)}) ∪
    {(43, if phase.upper then 0 else 1)} ∪
    (if phase.right then {(80,90)} else ∅)
  else {(if phase.left then 0 else 1, 90), (44, if phase.upper then 0 else 1),
    (if phase.right then 79 else 80, 90)}

def boundaryTest (kind : Bool) (a b : Signals) (p : C) : Bool :=
  decide (p ∈ boundaryNeighbors kind (neighborSignals a b))

def Case.neighborChecked (kind : Bool) (c : Case) : Bool :=
  Execution.valid (fun p => wallTest kind p || boundaryTest kind c.before c.after p)
    (canonical kind c.before) &&
  clearFootprint (boundaryTest kind c.before c.after) hub c.directions

private theorem fullandCases_neighbors :
    (fullandCases.all fun c => c.neighborChecked true) = true := by decide +kernel
private theorem fullorCases_neighbors :
    (fullorCases.all fun c => c.neighborChecked false) = true := by decide +kernel

/-- Every allowed collar position is an actual floor cell of the long-wall tile. -/
theorem boundaryNeighbors_floor (kind : Bool) (phase : Signals) :
    Disjoint (boundaryNeighbors kind phase) (walls kind) := by
  have hh : ∀ (kind a b c : Bool),
      @decide (∀ p ∈ boundaryNeighbors kind ⟨a,b,c⟩, wallTest kind p = false)
        Finset.decidableDforallFinset = true := by decide +kernel
  apply Finset.disjoint_left.mpr
  intro p hp hw
  have hf := (@of_decide_eq_true _ Finset.decidableDforallFinset
    (hh kind phase.left phase.upper phase.right)) p hp
  rw [(mem_walls kind p).mp hw] at hf
  contradiction

private theorem case_neighbors (kind : Bool) (c : Case) (hc : c.FullChecked kind)
    (hn : c.neighborChecked kind = true) (goals fixed : Finset C)
    (hf : fixed ⊆ boundaryNeighbors kind (neighborSignals c.before c.after))
    (hw : Disjoint fixed (walls kind)) :
    Reachable (board kind goals) (some 1) (withFixed fixed (canonical kind c.before))
      (withFixed fixed (canonical kind c.after)) := by
  have he := (Execution.check_correct _ _ _ _).mp hc.2
  have hb : ∀ p, boundaryTest kind c.before c.after p = true ↔
      p ∈ boundaryNeighbors kind (neighborSignals c.before c.after) := by
    intro p
    simp [boundaryTest]
  have hs : ∀ p, (wallTest kind p || boundaryTest kind c.before c.after p) = true ↔
      p ∈ (⟨walls kind ∪ boundaryNeighbors kind (neighborSignals c.before c.after), goals⟩ : Board 81 107).walls := by
    intro p
    simp [boundaryTest]
  simp only [Case.neighborChecked, Bool.and_eq_true] at hn
  exact frame_checked (wallTest_correct kind goals) hb
    ((Execution.valid_correct hs _).mp hn.1) he hn.2 hf hw

/-- The full canonical macro with real stationary boxes in every allowed port collar. -/
theorem canonical_transition_neighbors (kind : Bool) (a b : Signals)
    (ha : legal kind a) (hb : legal kind b) (hs : singleChange a b)
    (goals fixed : Finset C) (hf : fixed ⊆ boundaryNeighbors kind (neighborSignals a b)) :
    Reachable (board kind goals) (some 1) (withFixed fixed (canonical kind a))
      (withFixed fixed (canonical kind b)) := by
  have hc : ∃ c : Case, c.before = a ∧ c.after = b ∧
      c.FullChecked kind ∧ c.neighborChecked kind = true := by
    cases kind with
    | false =>
      obtain ⟨c, hc, h⟩ := List.any_eq_true.mp
        (fullorCases_covers a.left a.upper a.right b.left b.upper b.right ha hb hs)
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact ⟨c, h.1, h.2, fullorCases_checked c hc, List.all_eq_true.mp fullorCases_neighbors c hc⟩
    | true =>
      obtain ⟨c, hc, h⟩ := List.any_eq_true.mp
        (fullandCases_covers a.left a.upper a.right b.left b.upper b.right ha hb hs)
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact ⟨c, h.1, h.2, fullandCases_checked c hc, List.all_eq_true.mp fullandCases_neighbors c hc⟩
  obtain ⟨c, hi, ht, hc, hn⟩ := hc
  have hw := (boundaryNeighbors_floor kind (neighborSignals a b)).mono_left hf
  have hr := case_neighbors kind c hc hn goals fixed (by simpa only [hi, ht] using hf) hw
  simpa only [hi, ht] using hr

end PushPuzzle.PushFS.Gadgets.Gates
