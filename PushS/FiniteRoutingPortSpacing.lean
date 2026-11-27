/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingPortPhases
public import PushS.FiniteRoutingMacroContacts

/-! Complementary real port phases give a full empty cell across each source boundary. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

theorem macro_port_phase_sparse (w : ℕ) (face : Direction) (p r a b : ℕ × ℕ) (incoming phase : Bool)
    (hn : neighbor face p = some r) (ha : PortPhaseBound w face incoming phase a)
    (hb : PortPhaseBound w face.opposite (!incoming) (!phase) b) :
    ¬Nearby 1 (macroShift w p a) (macroShift w r b) := by
  have ht := neighbor_travels hn
  have hp : 3 ≤ padding w := by unfold padding; omega
  have hs : 1 ≤ tileStride w := by unfold tileStride spacing; omega
  intro he
  dsimp only [macroShift,Nearby] at he
  cases face <;> dsimp only [Travels] at ht
  all_goals rw [ht.2,Nat.mul_add,Nat.mul_one] at he
  all_goals cases incoming <;> cases phase <;>
    simp [PortPhaseBound,boundarySlot,boundaryPoint,Line.along,advance,Direction.opposite] at ha hb <;> omega

end PushPuzzle.PushS.FiniteRouting
