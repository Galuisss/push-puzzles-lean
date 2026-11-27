/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceAxisReadout
public import PushS.PortAxisTrainStep
public import PushS.PortGateAxisTrainStep
import all PushS.PortAxisGroups
import all PushS.PortGateAxisTrainReadout
import all PushS.PortAxisDecodeStep

/-! Genuine shared train motions locate every changed decoded bit on its actual original main axis. -/

public section
namespace PushPuzzle.Push.AcceptanceAxisReadout

open PushFS PushS PushS.PortLayout

/-- The actual ordinary and gate shared-axis train motions for one pair of physical states. -/
structure AxisMotions (l : PortLayout) (p : Scales.Parameters)
    (u v : State (p.W + 1) (p.H + 1)) : Prop where
  ordinary : ∀ upper lower, upper ∈ l.endpoints → lower ∈ l.endpoints →
    upper.side = .upper → lower.side = .lower → lower.port = upper.port →
      ∃ before after, OrdinaryAxisMotion p upper lower u v before after
  gate : ∀ g, g ∈ placements l → ∀ kind, g.gate = some kind →
    ∀ upper, upper ∈ l.endpoints → upper.side = .upper → upper.port = g.left + 1 →
      ∃ before after, GateAxisTrainMotion p g upper u v before after

/-- A changed actual upper threshold moves a shared train on that same source-player column. -/
private theorem axis_bit_change_column_of_motions (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid)
    {u v : State (p.W + 1) (p.H + 1)} (motions : AxisMotions l p u v)
    {axes next : List Bool} (source : l.AxisReadout p u axes) (target : l.AxisReadout p v next)
    {i : ℕ} (hi : i < l.portCount) (hchanged : axes.getD i false ≠ next.getD i false) :
    u.player.1.val = p.x i := by
  obtain ⟨upper, hu, hsuSide, hp⟩ := l.endpoints_upper_exists hl hi
  have hbit : axes.getD upper.port false ≠ next.getD upper.port false := by simpa only [hp] using hchanged
  obtain ⟨groups⟩ := l.axisGroups_nonempty hl hi
  have ordinary (hk : i = groups.lower.left ∨ i = groups.lower.right) : u.player.1.val = p.x i := by
    obtain ⟨lower, hlow, hls, hlp, _⟩ := placement_outer_endpoint l groups.lower_mem hk
    obtain ⟨before, after, motion⟩ := motions.ordinary upper lower hu hlow hsuSide
      (hls.trans groups.lower_side) (hlp.trans hp.symm)
    have hparameter := parameter_ne source target hu hsuSide (motion.before_readout.upper_endpoint hsuSide)
      (motion.after_readout.upper_endpoint hsuSide) hbit
    have hmiddle : before.middle ≠ after.middle := by
      intro heq
      apply hparameter
      change ((readDepth p upper.level : ℤ) + 4 - before.middle).toNat =
        ((readDepth p upper.level : ℤ) + 4 - after.middle).toNat
      rw [heq]
    simpa only [hp] using motion.player_column hmiddle
  rcases groups.lower_port with hleft | hright | ⟨hgate, hmid⟩
  · exact ordinary (Or.inl hleft)
  · exact ordinary (Or.inr hright)
  · cases hk : groups.lower.gate with
    | none => simp only [hk, Option.isSome_none, Bool.false_eq_true] at hgate
    | some kind =>
      have hupperPort : upper.port = groups.lower.left + 1 := hp.trans hmid
      obtain ⟨before, after, motion⟩ := motions.gate groups.lower groups.lower_mem kind hk upper hu hsuSide hupperPort
      have hparameter := parameter_ne source target hu hsuSide
        ((motion.before_shape.readout motion.before_positive).upper_endpoint hsuSide hupperPort)
        ((motion.after_shape.readout motion.after_positive).upper_endpoint hsuSide hupperPort) hbit
      have hlast : before.last ≠ after.last := by
        intro heq
        apply hparameter
        change ((readDepth p upper.level : ℤ) + 4 - before.last).toNat =
          ((readDepth p upper.level : ℤ) + 4 - after.last).toNat
        rw [heq]
      simpa only [← hmid] using motion.player_column (Or.inr hlast)

/-- Complete actual shared-axis motions project to stuttering or one legal original axis reversal. -/
theorem axisReadout_step_of_motions (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    {u v : State (p.W + 1) (p.H + 1)} (motions : AxisMotions l p u v)
    {axes next : List Bool} (source : l.AxisReadout p u axes) (target : l.AxisReadout p v next)
    (hsource : l.InputLegal axes) (htarget : l.InputLegal next) : axes = next ∨ l.AxisStep axes next :=
  axisReadout_step_of_columns source target hsource htarget
    (fun _ hi hb => axis_bit_change_column_of_motions l p hl motions source target hi hb)

end PushPuzzle.Push.AcceptanceAxisReadout
