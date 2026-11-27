/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceOrdinaryBoundary

/-! Genuine train dynamics and a fault-free accepted endpoint exclude ordinary faults along the whole run. -/

public section
namespace PushPuzzle.Push.AcceptanceOrdinaryFailure

open PushFS PushS PushS.PortLayout AcceptanceAxisReadout

private theorem propagate {α : Type} {P : α → Prop} {a b : α}
    (path : Relation.ReflTransGen (fun u v => P u → P v) a b) (base : P a) : P b := by
  induction path with
  | refl => exact base
  | tail _ move ih => exact move ih

/-- Complete physical train motions, endpoint words and frozen boundaries on one actual trajectory. -/
structure Dynamics (l : PortLayout) (p : Scales.Parameters) (B : Board (p.W + 1) (p.H + 1))
    (start finish : State (p.W + 1) (p.H + 1)) : Prop where
  axis : ∀ {u v}, Reachable B none start u → Step B none u v → Reachable B none v finish → AxisMotions l p u v
  rail : ∀ {u v}, Reachable B none start u → Step B none u v → Reachable B none v finish → RailMotions l p B u v
  words : ∀ {u}, Reachable B none start u → Reachable B none u finish → ∀ e ∈ l.endpoints,
    ∃ parameter shift horizontal, EndpointAxisReadout p e u parameter shift ∧ EndpointHorizontalReadout p e u horizontal
  boundary : ∀ {u}, Reachable B none start u → Reachable B none u finish → ∀ e ∈ l.endpoints, BoundaryBoxes p e u

section Trace
variable {l : PortLayout} {p : Scales.Parameters} (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
  {B : Board (p.W + 1) (p.H + 1)} {start finish : State (p.W + 1) (p.H + 1)}
  (dynamics : Dynamics l p B start finish) (e : Endpoint) (he : e ∈ l.endpoints)

include hl hM haxes dynamics he

/-- The same real suffix preserves every actual ordinary fault reached from outside its pocket. -/
private theorem Dynamics.failure_suffix {u : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable B none start u) (hut : Reachable B none u finish)
    (fault : OrdinaryFaultReadout p e u) (outside : u.player ∉ ordinaryPocket p e) :
    ∃ _ : OrdinaryFaultReadout p e finish, finish.player ∉ ordinaryPocket p e := by
  let Inv (s : State (p.W + 1) (p.H + 1)) := ∃ _ : OrdinaryFaultReadout p e s, s.player ∉ ordinaryPocket p e
  have path : Relation.ReflTransGen (fun a b => Inv a → Inv b) u finish := by
    apply Path.enrich hut
    intro a b hua move hbt
    rintro ⟨current, player⟩
    exact step l p hl hM haxes (dynamics.axis (hsu.trans hua) move hbt)
      (dynamics.rail (hsu.trans hua) move hbt) e he
      (dynamics.boundary (hsu.trans hua) ((Relation.ReflTransGen.single move).trans hbt) e he) move current player
  have base : Inv u := ⟨fault, outside⟩
  exact propagate (P := Inv) path base

/-- Every ordinary fault is absent at every prefix when its terminal fault is excluded. -/
theorem Dynamics.failure_absent (initialOutside : start.player ∉ ordinaryPocket p e)
    (terminal : ¬Nonempty (OrdinaryFaultReadout p e finish))
    {u : State (p.W + 1) (p.H + 1)} (hsu : Reachable B none start u) (hut : Reachable B none u finish) :
    ¬Nonempty (OrdinaryFaultReadout p e u) := by
  let Inv (s : State (p.W + 1) (p.H + 1)) := ¬Nonempty (OrdinaryFaultReadout p e s)
  have impossible {a} (hsa : Reachable B none start a) (hat : Reachable B none a finish)
      (fault : OrdinaryFaultReadout p e a) (outside : a.player ∉ ordinaryPocket p e) : False := by
    obtain ⟨finalFault, _⟩ := dynamics.failure_suffix hl hM haxes e he hsa hat fault outside
    exact terminal ⟨finalFault⟩
  have base : Inv start := by rintro ⟨fault⟩; exact impossible .refl (hsu.trans hut) fault initialOutside
  have path : Relation.ReflTransGen (fun a b => Inv a → Inv b) start u := by
    apply Path.enrich hsu
    intro a b hsa move hbu source
    rintro ⟨fault⟩
    have hbt := hbu.trans hut
    have hat := (Relation.ReflTransGen.single move).trans hbt
    obtain ⟨parameter, shift, horizontal, axisWord, railWord⟩ := dynamics.words hsa hat e he
    have outside := onset l p hl hM haxes (dynamics.axis hsa move hbt) (dynamics.rail hsa move hbt)
      e he move axisWord railWord fault source
    exact impossible (hsa.tail move) hbt fault outside
  exact propagate (P := Inv) path base

end Trace
end PushPuzzle.Push.AcceptanceOrdinaryFailure
