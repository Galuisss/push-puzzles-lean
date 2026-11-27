/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.ShortCorners.Basic
public import PushFS.DisplacementCheck

/-! True finite wall classification, all owned slots and exact target order of the four short corners. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.ShortCorners

set_option maxHeartbeats 0
set_option maxRecDepth 65536

def axisName (k : Kind) (p : Cell (width k) (height k)) : AxisTrack :=
  if p.1.val=10 ∧p.2.val=10 then .sink 10 10
  else if p.2.val=10 ∧10<p.1.val then .horizontal 10
  else if p.1.val=10 ∧10<p.2.val then .vertical 10 else .outside

theorem supported_checked (k : Kind) : ∀p, AxisTrack.supportTest (axisName k) p=true := by
  cases k <;> decide +kernel

theorem strong_checked (k : Kind) :
    checkDisplacements (template k).wall (AxisTrack.activeSources (axisName k)) (AxisTrack.strongAllowed (axisName k))=true := by
  cases k <;> decide +kernel

def classifier (k : Kind) (goals : Finset (Cell (width k) (height k))) : AxisClassifier ((template k).board goals) :=
  AxisClassifier.of_strong_check ((template k).wall_correct goals) (axisName k) (supported_checked k) (strong_checked k)

theorem slot_active (k : Kind) : ∀(phase : Bool) (i : Fin (count k)),
    axisName k ((template k).position phase i)≠.outside := by cases k <;> decide +kernel

theorem sparse_slots (k : Kind) : ∀(phase : Bool) (i j : Fin (count k)) (d : Direction),
    ¬Adjacent d ((template k).position phase i) ((template k).position phase j) := by cases k <;> decide +kernel

theorem order_x (k : Kind) : ∀(a b : Bool) (i j : Fin (count k)),
    ((template k).position a i).1.val<((template k).position a j).1.val→
      ((template k).position b i).1.val<((template k).position b j).1.val := by cases k <;> decide +kernel

theorem order_y (k : Kind) : ∀(a b : Bool) (i j : Fin (count k)),
    ((template k).position a i).2.val<((template k).position a j).2.val→
      ((template k).position b i).2.val<((template k).position b j).2.val := by cases k <;> decide +kernel

end PushPuzzle.PushFS.Gadgets.Wires.ShortCorners
