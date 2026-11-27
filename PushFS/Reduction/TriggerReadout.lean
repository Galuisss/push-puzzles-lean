/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Labels
public import PushFS.NCL.PortClaims

/-!
# Source-port observations from actual physical trigger identities

Different ports use different physical boxes. A real single push therefore
changes at most one observed port, including during noncanonical intermediate
states. Legal exclusive gate/wire observations along a successful path project
to the actual upstream NCL reachability relation.
-/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction


open Cslib.Complexity.NCL PushPuzzle.NCL

/-- The actual trigger box and position threshold of every source port. -/
structure TriggerReadout (E Label : Type) (w h : ℕ) where
  /-- Separate logical ports have separate physical trigger identities. -/
  label : Port E ↪ Label
  /-- Each port's literal inward threshold on its own physical coordinate. -/
  threshold : Port E → Cell w h → Bool

namespace TriggerReadout

variable {E Label : Type} [Fintype Label] {w h : ℕ}

/-- Read inward claims without discarding player positions or imposing canonical box positions. -/
def read (R : TriggerReadout E Label w h) (S : LabelledState Label w h) : PortClaims.Claims E :=
  fun p => R.threshold p (S.position (R.label p))

/-- At most one logical trigger can change in one actual physical move. -/
private theorem step_one_port (R : TriggerReadout E Label w h) {B : Board w h}
    {S T : LabelledState Label w h} (hs : LabelledState.Step B S T) :
    R.read S = R.read T ∨ ∃ p, ∀ q, q ≠ p → R.read T q = R.read S q := by
  classical
  by_cases he : R.read S = R.read T
  · exact Or.inl he
  · have hex : ∃ p, R.read S p ≠ R.read T p := by
      by_contra hh
      apply he
      funext p
      by_contra hp
      exact hh ⟨p, hp⟩
    obtain ⟨p, hp⟩ := hex
    obtain ⟨d, hm, hwalk | hpush⟩ := hs
    · exact False.elim (hp (by simp only [read, hwalk.2]))
    · obtain ⟨dest, _, _, _, _, hpos⟩ := hpush
      have hmove : S.position (R.label p) = T.state.player := by
        by_contra hfix
        apply hp
        unfold read
        rw [hpos]
        simp only [Function.comp_apply, Gadgets.shiftBox_other hfix]
      refine Or.inr ⟨p, fun q hq => ?_⟩
      have hfix : S.position (R.label q) ≠ T.state.player := by
        intro heq
        exact hq (R.label.injective (S.injective (heq.trans hmove.symm)))
      unfold read
      rw [hpos]
      simp only [Function.comp_apply, Gadgets.shiftBox_other hfix]

/-- Local gate legality and line exclusivity turn this real physical step into a source observation step. -/
private theorem observation_step (R : TriggerReadout E Label w h) {V : Type}
    {G : ConstraintGraph V E} {B : Board w h} {S T : LabelledState Label w h}
    (hs : LabelledState.Step B S T)
    (hS : PortClaims.Exclusive (R.read S) ∧ PortClaims.Legal G (R.read S))
    (hT : PortClaims.Exclusive (R.read T) ∧ PortClaims.Legal G (R.read T)) :
    PortClaims.Step G (R.read S) (R.read T) := by
  rcases R.step_one_port hs with he | ⟨p, hp⟩
  · exact ⟨hS.1, hS.2, hT.1, hT.2, Or.inl he⟩
  · exact PortClaims.step_of_single_port hS.1 hS.2 hT.1 hT.2 p hp

/-- All observed legal exclusive states of a successful physical path form an actual NCL path. -/
theorem successful_path (R : TriggerReadout E Label w h) [DecidableEq E]
    {V : Type} {G : ConstraintGraph V E} {B : Board w h}
    {initial final : LabelledState Label w h} {s t : E → Bool}
    (hr : LabelledState.Reachable B initial final)
    (hadmissible : ∀ S, LabelledState.Reachable B initial S → LabelledState.Reachable B S final →
      PortClaims.Exclusive (R.read S) ∧ PortClaims.Legal G (R.read S))
    (hstart : R.read initial = PortClaims.full s) (hfinish : R.read final = PortClaims.full t) :
    G.Reachable s t := by
  have project_prefix {S : LabelledState Label w h} (hb : LabelledState.Reachable B initial S)
      (ha : LabelledState.Reachable B S final) :
      Relation.ReflTransGen (PortClaims.Step G) (R.read initial) (R.read S) := by
    induction hb with
    | refl => exact .refl
    | @tail U T hb hs ih =>
      have hbefore := hadmissible U hb (ha.head hs)
      have hafter := hadmissible T (hb.tail hs) ha
      exact (ih (ha.head hs)).tail (R.observation_step hs hbefore hafter)
  have hp := project_prefix hr (.refl)
  rw [hstart, hfinish] at hp
  exact PortClaims.full_reachable_iff.mp hp

end TriggerReadout
end PushPuzzle.PushFS.Reduction
