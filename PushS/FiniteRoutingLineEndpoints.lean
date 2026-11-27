/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingLineMatching
public import Mathlib.Data.List.GetD

/-! Exact shared endpoints and spacing of the owned inventory of each emitted straight piece. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting.Line

open PushFS

def firstLabel (w : ℕ) (atoms : List Atom) : Label w atoms :=
  ⟨0,positions_length_pos w atoms false⟩

def lastLabel (w : ℕ) (atoms : List Atom) : Label w atoms :=
  ⟨(positions w false atoms).length-1,by have h := positions_length_pos w atoms false; omega⟩

theorem position_last (w : ℕ) (atoms : List Atom) (phase : Bool) :
    position w atoms phase (lastLabel w atoms) = span w atoms+phase.toNat := by
  have hh := positions_last w atoms phase
  rw [List.getLast_eq_getElem] at hh
  simpa only [position,lastLabel,List.get_eq_getElem,positions_length] using hh

theorem program_position_first (w length : ℕ) (switch phase : Bool) :
    position w (program w length switch) phase (firstLabel w (program w length switch)) = phase.toNat := by
  have hh := program_positions_head w length switch phase
  rw [List.headD_eq_getD] at hh
  rw [List.getD_eq_getElem _ _ (positions_length_pos w _ phase)] at hh
  exact hh

private theorem position_separated (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (phase : Bool)
    (a b : Label w atoms) (hab : a.val < b.val) :
    position w atoms phase a+2 ≤ position w atoms phase b := by
  have ha : a.val < (positions w phase atoms).length := by simpa only [positions_length] using a.isLt
  have hb : b.val < (positions w phase atoms).length := by simpa only [positions_length] using b.isLt
  exact List.pairwise_iff_getElem.mp (positions_pairwise w hw phase atoms) a.val b.val ha hb hab

/-- A line leaving its first interface to another owner starts at least two cells farther along the stock. -/
theorem owned_position_after_first (w length : ℕ) (hw : 2 ≤ w) (switch phase last : Bool)
    (l : OwnedLabel w (program w length switch) false last) :
    phase.toNat+2 ≤ position w (program w length switch) phase l.val := by
  have hi : 0 < l.val.val := by simpa only [Bool.false_eq_true,false_or] using l.property.1
  have hh := position_separated w hw (program w length switch) phase (firstLabel w _) l.val hi
  rw [program_position_first] at hh
  exact hh

/-- A line leaving its final interface to another owner ends at least two cells before that box. -/
theorem owned_position_before_last (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (phase first : Bool)
    (l : OwnedLabel w atoms first false) :
    position w atoms phase l.val+2 ≤ span w atoms+phase.toNat := by
  have hi : l.val.val+1 < (positions w false atoms).length := by
    simpa only [Bool.false_eq_true,false_or] using l.property.2
  have hilast : l.val.val < (lastLabel w atoms).val := by dsimp [lastLabel]; omega
  have hh := position_separated w hw atoms phase l.val (lastLabel w atoms) hilast
  rw [position_last] at hh
  exact hh

end PushPuzzle.PushS.FiniteRouting.Line
