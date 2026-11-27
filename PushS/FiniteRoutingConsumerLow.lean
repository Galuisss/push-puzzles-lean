/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingTerminalPhase
public import PushS.FiniteSourcePortPhases

/-! Literal normal consuming ports with false inward claim leave the last producer support clear. -/

public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction Gadgets.Wires

/-- A consuming source port has its inward claim false in this normal phase. -/
@[expose] def ConsumerLow (code : CellPlan.Code) (face : Direction) (goal : Bool) : Prop :=
  match code with
  | none => False
  | some (.inl (_,g)) => ∀ role : Fin 3, PortAnnulus.outerDirection (g.pattern,g.rotation,role) = face →
      g.incoming.get role = true ∧
      portInflow (coreSignals g goal).left (coreSignals g goal).upper (coreSignals g goal).right role = false
  | some (.inr (_,a)) => face = (Catalog.sourceDirection a.1).opposite ∧ PhysicalTiles.wirePhase a goal = true

theorem consumerLow_actor_bound (w : ℕ) (hw : 2 ≤ w) (code : CellPlan.Code) (face : Direction) (goal : Bool)
    (H : ConsumerLow code face goal) (c : PrimitiveCode) (hc : c ∈ FiniteSourceInventory.localCodes w code)
    (l : c.Labels w) (hf : InCollar w face (c.actor w hw goal l)) :
    PortPhaseBound w face true false (c.actor w hw goal l) := by
  cases code with
  | none => exact H.elim
  | some code =>
    cases code with
    | inl g =>
      obtain ⟨role,hd,hb⟩ := gate_actor_phase_bound w hw g.2 c hc goal l face hf
      obtain ⟨hin,hphase⟩ := H role hd
      rwa [hin,hphase] at hb
    | inr a =>
      have hb := wire_input_phase_bound w hw a.2 c hc goal l face hf H.1
      change PortPhaseBound w face true (!(PhysicalTiles.wirePhase a.2 goal)) (c.actor w hw goal l) at hb
      simpa only [H.2,Bool.not_true] using hb

end PushPuzzle.PushS.FiniteRouting
