/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingPortBounds

/-! Normal actors remain within one cell of the padded source macrocell. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction Gadgets.Wires

private theorem local_actor_owned_bound (w : ℕ) (hw : 2 ≤ w) (code : CellPlan.Code)
    (c : PrimitiveCode)
    (hc : c ∈ FiniteSourceInventory.localCodes w code) (goal : Bool) (l : c.Labels w) (face : Direction)
    (hf : InCollar w face (c.actor w hw goal l)) :
    ∃ incoming, PortOwnedBound w face incoming (c.actor w hw goal l) := by
  cases code with
  | none => simp [FiniteSourceInventory.localCodes] at hc
  | some code =>
    cases code with
    | inl g =>
      obtain ⟨role,_,hb⟩ := gate_actor_collar_bound w hw g.2 c hc goal l face hf
      exact ⟨g.2.incoming.get role,hb⟩
    | inr q =>
      rcases wire_actor_collar_bound w hw q.2 c hc goal l face hf with h | h
      · exact ⟨true,h.2⟩
      · exact ⟨false,h.2⟩

def ActorBounds (w : ℕ) (a : ℕ × ℕ) : Prop :=
  padding w ≤ a.1+1 ∧ a.1 ≤ tileStride w+padding w+1 ∧
    padding w ≤ a.2+1 ∧ a.2 ≤ tileStride w+padding w+1

theorem local_actor_inner_bounds (w : ℕ) (hw : 2 ≤ w) (code : CellPlan.Code) (c : PrimitiveCode)
    (hc : c ∈ FiniteSourceInventory.localCodes w code) (goal : Bool) (l : c.Labels w) :
    ActorBounds w (c.actor w hw goal l) := by
  have hl (face : Direction) := local_actor_owned_bound w hw code c hc goal l face
  let a := c.actor w hw goal l
  have hx0 : padding w ≤ a.1+1 := by
    by_cases hh : a.1 ≤ 2*padding w
    · obtain ⟨incoming,hb⟩ := hl .west hh
      cases incoming <;> dsimp [PortOwnedBound] at hb <;> dsimp only [a] at * <;> omega
    · omega
  have hx1 : a.1 ≤ tileStride w+padding w+1 := by
    by_cases hh : tileStride w ≤ a.1
    · obtain ⟨incoming,hb⟩ := hl .east hh
      cases incoming <;> dsimp [PortOwnedBound] at hb <;> dsimp only [a] at * <;> omega
    · omega
  have hy0 : padding w ≤ a.2+1 := by
    by_cases hh : a.2 ≤ 2*padding w
    · obtain ⟨incoming,hb⟩ := hl .north hh
      cases incoming <;> dsimp [PortOwnedBound] at hb <;> dsimp only [a] at * <;> omega
    · omega
  have hy1 : a.2 ≤ tileStride w+padding w+1 := by
    by_cases hh : tileStride w ≤ a.2
    · obtain ⟨incoming,hb⟩ := hl .south hh
      cases incoming <;> dsimp [PortOwnedBound] at hb <;> dsimp only [a] at * <;> omega
    · omega
  exact ⟨hx0,hx1,hy0,hy1⟩

end PushPuzzle.PushS.FiniteRouting
