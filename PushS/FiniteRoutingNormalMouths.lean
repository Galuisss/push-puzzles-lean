/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingLineAction

/-! The two literal first-flip mouth columns belong to the actual strict program action floor. -/

public section
namespace PushPuzzle.PushS.FiniteRouting.Line

open PushFS

attribute [local irreducible] width height

private theorem mouth_active_of_eq (w : ℕ) (hw : 2 ≤ w) (atoms pre post : List Atom)
    (he : atoms = pre++ .flip::post) (above last : Bool) (j : Fin 2)
    (p : Cell (width w atoms) (height w))
    (hx : p.1.val = FiniteTools.radius w+span w pre+w+1+j.val)
    (hy : FiniteTools.radius w-w-1 ≤ p.2.val) (hy' : p.2.val ≤ FiniteTools.radius w+w+1)
    (hside : if flipMouthNorth above pre j then p.2.val ≤ FiniteTools.radius w else FiniteTools.radius w ≤ p.2.val) :
    p ∈ Action.active w atoms above last := by
  subst atoms
  have hx' : p.1 = flipMouthX w pre post j := Fin.ext hx
  exact (FiniteWireFrame.floor_iff _ _ _).mp
    (Action.flipMouth_macro_free (last := last) w hw 0 pre post above j p hx' hy hy' hside).1

theorem program_first_mouth_active (w : ℕ) (hw : 2 ≤ w) (length : ℕ) (switch above last : Bool) (j : Fin 2)
    (p : Cell (width w (program w length switch)) (height w))
    (hx : p.1.val = FiniteTools.radius w+2*buffer w+w+1+j.val)
    (hy : FiniteTools.radius w-w-1 ≤ p.2.val) (hy' : p.2.val ≤ FiniteTools.radius w+w+1)
    (hside : if flipMouthNorth above [.line (buffer w)] j then p.2.val ≤ FiniteTools.radius w else FiniteTools.radius w ≤ p.2.val) :
    p ∈ Action.active w (program w length switch) above last := by
  obtain ⟨post,hpost⟩ := program_contains_flip w length switch
  apply mouth_active_of_eq w hw _ [.line (buffer w)] post hpost above last j p _ hy hy' hside
  simpa only [span_cons,span_nil,Atom.span,Nat.add_zero] using hx

end PushPuzzle.PushS.FiniteRouting.Line
