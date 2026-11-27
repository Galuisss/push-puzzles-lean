/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingActionContract

/-! Exact full-label slots of a prepared line, including its two actual external interfaces. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting.Line

open PushFS

variable {W H : ℕ}

attribute [local irreducible] width height positions ownedCount program

/-- The high-to-low propagation cut, with the real first low and unowned last high. -/
def preparedCut (w : ℕ) (atoms : List Atom) (last q : Bool) : ℕ :=
  if q then 1 else ownedCount w atoms+if last then 1 else 0

/-- Every physical label, including real external owners, at the prepared propagation endpoint. -/
def preparedCell (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (last q : Bool) (l : Label w atoms) :
    Cell (width w atoms) (height w) := cutCell w hw (preparedCut w atoms last q) atoms l

theorem preparedCell_first (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (last q : Bool)
    (hcount : 0 < ownedCount w atoms) :
    preparedCell w hw atoms last q (cutFirstLabel w atoms) = cell w hw atoms false (cutFirstLabel w atoms) :=
  cutCell_first w hw _ atoms (by cases q <;> cases last <;> dsimp [preparedCut] <;> omega)

theorem preparedCell_last (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (q : Bool)
    (hcount : 0 < ownedCount w atoms) :
    preparedCell w hw atoms false q (cutLastLabel w atoms) = cell w hw atoms true (cutLastLabel w atoms) := by
  apply cutCell_last
  have hh := Terminal.length_eq w atoms
  cases q <;> dsimp [preparedCut] <;> omega

theorem preparedCell_owned (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (last q : Bool)
    (l : OwnedLabel w atoms false last) :
    preparedCell w hw atoms last q l.val = ownedCell w hw atoms false last q l := by
  have hp := l.property
  have hl := l.val.isLt
  have hlen := Terminal.length_eq w atoms
  cases q with
  | false =>
    have hb : l.val.val < preparedCut w atoms last false := by
      cases last <;> simp only [Bool.false_eq_true,false_or] at hp <;> dsimp [preparedCut] <;> omega
    exact ite_eq_left hb
  | true =>
    have hb : ¬l.val.val < preparedCut w atoms last true := by
      simp only [Bool.false_eq_true,false_or] at hp
      dsimp [preparedCut]
      omega
    exact ite_eq_right hb

/-- The actual strict-footprint program changes exactly the prepared source and target full-label inventories. -/
private theorem prepared_program_placed (w : ℕ) (hw : 2 ≤ w) (length : ℕ)
    (switch above last a b : Bool)
    (hab : b = !a)
    (e : GridEmbedding (width w (program w length switch)) (height w) W H)
    {B : Board W H} {fixed : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (Action.active w (program w length switch) above last) e B fixed) :
    Reachable B (some 1)
      (e.extend fixed ⟨outerHub w _,Finset.univ.image (preparedCell w hw _ last a)⟩)
      (e.extend fixed ⟨outerHub w _,Finset.univ.image (preparedCell w hw _ last b)⟩) := by
  cases a with
  | false =>
    have hb : b = true := hab
    subst b
    exact Action.program_low_high_placed w hw length switch above last e F
  | true =>
    have hb : b = false := hab
    subst b
    exact Action.program_high_low_placed w hw length switch above last e F

/-- The same strict-footprint run with a literal atom-list equality hidden from the consumer. -/
theorem prepared_program_of_eq (w : ℕ) (hw : 2 ≤ w) (atoms : List Atom) (length : ℕ)
    (switch above last a b : Bool) (hatoms : atoms = program w length switch) (hab : b = !a)
    (e : GridEmbedding (width w atoms) (height w) W H) {B : Board W H} {fixed : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (Action.active w atoms above last) e B fixed) :
    Reachable B (some 1)
      (e.extend fixed ⟨outerHub w atoms,Finset.univ.image (preparedCell w hw atoms last a)⟩)
      (e.extend fixed ⟨outerHub w atoms,Finset.univ.image (preparedCell w hw atoms last b)⟩) := by
  subst atoms
  exact prepared_program_placed w hw length switch above last a b hab e F

end PushPuzzle.PushS.FiniteRouting.Line
