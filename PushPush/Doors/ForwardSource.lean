/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.ForwardCalls

/-! Original door-network steps lift to the complete finite physical work board. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open Cslib.Complexity

/-- Stable physical inventory at a location's incoming port, with the exact exterior player. -/
def encodedState (storage : Bool) (I : Instance) (s : State) (port : ℕ) : Stock I :=
  Stock.ofBits I s.bits (atRow storage I (inputRow I (rank I s.location) 0 port))

private theorem encodedState_initial (storage : Bool) (I : Instance) :
    encodedState storage I I.initial (2 * I.doors.length) = Stock.initial storage I :=
  Stock.ofBits_initial storage I

/-- One original enabled tunnel traverses the complete physical choice chain and door. -/
private theorem encodedState_step (storage : Bool) (I : Instance) (hwire : WireSimulation storage I)
    {s t : State} (hstep : SelfClosingDoor.Step I.doors s t)
    (hloc : s.location ∈ labels I) (hnt : s.location ≠ I.target)
    (port : ℕ) (hport : port < slots I) :
    ∃ nextPort < slots I,
      Finite.Reachable 1 ((encodedState storage I s port).canonical storage)
        ((encodedState storage I t nextPort).canonical storage) := by
  obtain ⟨hvalid, i, hentry, rfl⟩ := hstep
  let bit := s.bits.getD i.val false
  let k := tunnelIndex i.val bit
  let current := encodedState storage I s port
  have hcurrent : current.register i = Register.stable bit := rfl
  have hv : rank I s.location < (labels I).length := rank_bound I hloc
  have hk : k < 2 * I.doors.length := tunnelIndex_lt I i bit
  have hne : rank I s.location ≠ rank I I.target := by
    intro he
    exact hnt ((rank_eq_iff I hloc).mp he)
  have hsource : rank I (channel I k).source = rank I s.location := by
    rw [channel_tunnelIndex]
    exact congrArg (rank I) hentry.symm
  have htarget : doorBase (k / 2) + (if channelBit k then 50 else 40) =
      doorBase i.val + (checkRegister bit).row := by
    rw [tunnelIndex_div, tunnelIndex_bit]
    cases bit <;> rfl
  have hready : atRow storage I (doorBase (k / 2) + (if channelBit k then 50 else 40)) ∉
      current.registerPoints storage := by
    rw [htarget]
    apply current.door_input_ready storage i (checkRegister bit)
    rw [hcurrent]
    cases bit <;> decide
  have hchoose := current.choose storage hwire (rank I s.location) k port hv hk hport hne hsource rfl hready
  let entered : Stock I := {current with signal := atRow storage I (doorBase i.val + (checkRegister bit).row)}
  have hc : Finite.Reachable 1 (current.canonical storage) (entered.canonical storage) := by
    simpa only [htarget] using hchoose
  have hcall := entered.call storage hwire i bit hcurrent rfl
  let destination := atRow storage I
    (inputRow I (rank I (I.doors[i].tunnel bit).target) 0 k)
  have heq : encodedState storage I
      ⟨(I.doors[i].tunnel bit).target, s.bits.set i.val (!bit)⟩ k =
      ({(entered.setRegister i (Register.stable (!bit))) with signal := destination} : Stock I) := by
    change Stock.ofBits I (s.bits.set i.val (!bit)) destination = _
    rw [Stock.ofBits_set I s.bits destination hvalid i (!bit)]
    rfl
  refine ⟨k, by unfold slots; omega, ?_⟩
  rw [heq]
  exact hc.trans hcall

/-- Reach a target-location stock, stopping the physical simulation at its first visit. -/
theorem encodedState_reaches_target (storage : Bool) (I : Instance)
    (hwire : WireSimulation storage I) (hs : I ∈ SelfClosingDoor.Reachability) :
    ∃ (s : State) (port : ℕ), s.location = I.target ∧ port < slots I ∧
      Finite.Reachable 1 (puzzle storage I).initial ((encodedState storage I s port).canonical storage) := by
  obtain ⟨s, hr, ht⟩ := hs
  have hsim :
      (∃ (t : State) (port : ℕ), t.location = I.target ∧ port < slots I ∧
        Finite.Reachable 1 (puzzle storage I).initial ((encodedState storage I t port).canonical storage)) ∨
      (∃ port < slots I,
        Finite.Reachable 1 (puzzle storage I).initial ((encodedState storage I s port).canonical storage)) := by
    clear ht
    induction hr with
    | refl =>
      apply Or.inr
      refine ⟨2 * I.doors.length, by unfold slots; omega, ?_⟩
      rw [encodedState_initial, Stock.initial_canonical]
    | @tail u v hr hstep ih =>
      rcases ih with hd | ⟨port, hport, hp⟩
      · exact Or.inl hd
      · by_cases hu : u.location = I.target
        · exact Or.inl ⟨u, port, hu, hport, hp⟩
        · obtain ⟨nextPort, hn, hs⟩ := encodedState_step storage I hwire hstep
            (reachable_location_mem I hr) hu port hport
          exact Or.inr ⟨nextPort, hn, hp.trans hs⟩
  rcases hsim with hdone | ⟨port, hport, hp⟩
  · exact hdone
  · exact ⟨s, port, ht, hport, hp⟩

end PushPuzzle.PushPush.Doors.Source
