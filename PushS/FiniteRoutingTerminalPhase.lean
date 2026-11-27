/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingPortCoordinates
public import PushS.FiniteRoutingPortPhases

/-! A prepared consuming neighbor leaves the producer's last support cell empty. -/

public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

private theorem macro_terminal_phase_ne (w : ℕ) (pos other a : ℕ × ℕ) (face : Direction)
    (hn : neighbor face pos = some other) (hb : PortPhaseBound w face.opposite true false a) :
    macroShift w pos (Line.along w face (boundaryPoint w face) 2) ≠ macroShift w other a := by
  have hpad : 2 ≤ padding w := by unfold padding; omega
  have hstride : 1 ≤ tileStride w := by unfold tileStride spacing; omega
  have ht := neighbor_travels hn
  intro he
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  dsimp only [macroShift] at hx hy
  cases face <;> dsimp only [Travels] at ht
  all_goals simp only [ht.1,ht.2,Nat.mul_add,Nat.mul_one] at hx hy
  all_goals dsimp [PortPhaseBound,boundarySlot,boundaryPoint,Line.along,advance,Direction.opposite] at hb hx hy
  all_goals omega

theorem LinePort.terminal_ne (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (pos other a : ℕ × ℕ) (face : Direction) (hn : neighbor face pos = some other)
    (hport : LinePort w c face false) (hb : PortPhaseBound w face.opposite true false a) :
    macroShift w pos (c.capWorld w hw false) ≠ macroShift w other a := by
  rcases hport with ⟨hd,he,_,_⟩ | ⟨h,_⟩
  · rw [c.capWorld_eq w hw hc false]
    simp only [Bool.false_eq_true,↓reduceIte,hd,he,Bool.toNat_false,advance_zero]
    exact macro_terminal_phase_ne w pos other a face hn hb
  · cases h

end PushPuzzle.PushS.FiniteRouting
