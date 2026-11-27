/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingPieces
public import PushS.FiniteRoutingLineEndpoints

/-! Exact shared boundary slots of producing and consuming source macrocells. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

def boundaryPoint (w : ℕ) : Direction → ℕ × ℕ
  | .north => (25*spacing w,0)
  | .east => (tileStride w,25*spacing w)
  | .south => (25*spacing w,tileStride w)
  | .west => (0,25*spacing w)

/-- Consuming endpoints use the inward no-inflow reference slot. -/
def boundarySlot (w : ℕ) (d : Direction) (incoming phase : Bool) : ℕ × ℕ :=
  Line.along w d (if incoming then advance d.opposite (boundaryPoint w d) 1 else boundaryPoint w d) phase.toNat

def shift (offset point : ℕ × ℕ) : ℕ × ℕ := (offset.1+point.1,offset.2+point.2)

/-- Adjacent source tiles give exactly the same physical box cell, with complementary local inward bits. -/
theorem boundary_seam (w : ℕ) (d : Direction) (u v : ℕ × ℕ) (phase : Bool)
    (h : Travels d u v (tileStride w)) :
    shift u (boundarySlot w d false phase) =
      shift v (boundarySlot w d.opposite true (!phase)) := by
  cases d <;> cases phase <;> apply Prod.ext <;>
    simp [Travels,shift,boundarySlot,boundaryPoint,Line.along,advance,Direction.opposite,
      tileStride,spacing,padding] at * <;> omega

/-- Reversing the local input direction reverses its inward bit and keeps the same shared slot. -/
theorem wire_input_slot (w : ℕ) (d : Direction) (phase : Bool) :
    Line.along w d.opposite (boundaryPoint w d) phase.toNat = boundarySlot w d true (!phase) := by
  cases d <;> cases phase <;> apply Prod.ext <;>
    simp [boundarySlot,boundaryPoint,Line.along,advance,Direction.opposite] <;>
    unfold tileStride spacing padding <;> omega

theorem along_finish (w : ℕ) (d : Direction) (p q : ℕ × ℕ) (length : ℕ) (phase : Bool)
    (h : Travels d p q length) : Line.along w d p (length+phase.toNat) = Line.along w d q phase.toNat := by
  cases d <;> apply Prod.ext <;> dsimp [Travels,Line.along] at * <;>
    unfold padding at * <;> have hphase := Bool.toNat_le phase <;> omega

/-- A line's owned final box agrees with the literal endpoint slot, including phase one outside the raw source rectangle. -/
theorem Line.placed_last_slot (w : ℕ) (hw : 2 ≤ w) (atoms : List Line.Atom)
    (d : Direction) (p q : ℕ × ℕ) (h : Travels d p q (Line.span w atoms))
    (hp : p.1 ≤ tileStride w ∧ p.2 ≤ tileStride w)
    (hq : q.1 ≤ tileStride w ∧ q.2 ≤ tileStride w) (phase : Bool) :
    (((Line.placement w atoms d p q h hp hq).cells (Line.cell w hw atoms phase (Line.lastLabel w atoms))).1.val,
      ((Line.placement w atoms d p q h hp hq).cells (Line.cell w hw atoms phase (Line.lastLabel w atoms))).2.val) =
      Line.along w d q phase.toNat := by
  rw [Line.placement_cell,Line.position_last]
  exact along_finish w d p q _ phase h

end PushPuzzle.PushS.FiniteRouting
