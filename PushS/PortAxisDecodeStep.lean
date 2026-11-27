/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortAxisDecode
public import PushS.PortAxisTrainStep
public import PushS.PortGateAxisTrainStep
import all PushS.PortAxisGroups
import all PushS.PortGateAxisTrainReadout
import all PushS.PortEndpointCrossing
import CslibFrontier.Foundations.Data.List.Lookup

/-! Each real physical step changes at most one original decoded interface-axis bit. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS

private theorem parameter_ne {l : PortLayout} {p : Scales.Parameters}
    {u v : State (p.W + 1) (p.H + 1)} {axes next : List Bool}
    (source : l.AxisReadout p u axes) (target : l.AxisReadout p v next)
    {e : Endpoint} (he : e ∈ l.endpoints) (hs : e.side = .upper)
    {beforeParameter beforeShift afterParameter afterShift : ℕ}
    (before : EndpointAxisReadout p e u beforeParameter beforeShift)
    (after : EndpointAxisReadout p e v afterParameter afterShift)
    (hchanged : axes.getD e.port false ≠ next.getD e.port false) : beforeParameter ≠ afterParameter := by
  intro heq
  have hsource := source.upper e he hs before
  have htarget := target.upper e he hs after
  rw [heq] at hsource
  exact hchanged (Bool.eq_iff_iff.mpr (hsource.trans htarget.symm))

private theorem axis_x_injective (p : Scales.Parameters) {i j : ℕ} (heq : p.x i = p.x j) : i = j := by
  by_contra hne
  have hD := p.outer_distance
  rcases lt_or_gt_of_ne hne with h | h
  · have hspace := axis_spacing p h
    omega
  · have hspace := axis_spacing p h
    omega

private theorem flip_of_ne (a b : Bool) (h : a ≠ b) : b = !a := by
  cases a <;> cases b <;> simp_all

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)

local notation "I" => l.physicalInstance p hl hM ha initial target

/-- Changing a decoded axis bit forces the real source player onto that same actual main-axis column. -/
theorem physicalInstance_axis_bit_change_column {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals)
    {axes next : List Bool} (source : l.AxisReadout p u axes) (targetReadout : l.AxisReadout p v next)
    {i : ℕ} (hi : i < l.portCount) (hchanged : axes.getD i false ≠ next.getD i false) :
    u.player.1.val = p.x i := by
  obtain ⟨upper, hu, hsuSide, hp⟩ := l.endpoints_upper_exists hl hi
  have hbit : axes.getD upper.port false ≠ next.getD upper.port false := by simpa only [hp] using hchanged
  obtain ⟨groups⟩ := l.axisGroups_nonempty hl hi
  have ordinary (hk : i = groups.lower.left ∨ i = groups.lower.right) : u.player.1.val = p.x i := by
    obtain ⟨lower, hlow, hls, hlp, _⟩ := placement_outer_endpoint l groups.lower_mem hk
    obtain ⟨before, after, motion⟩ := l.physicalInstance_ordinaryAxis_train_motion p hl hM ha initial target
      hu hlow hsuSide (hls.trans groups.lower_side) (hlp.trans hp.symm) hsu hm hvt ht
    have hparameter := parameter_ne source targetReadout hu hsuSide (motion.before_readout.upper_endpoint hsuSide)
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
      obtain ⟨before, after, motion⟩ := l.physicalInstance_gateAxis_train_motion p hl hM ha initial target
        groups.lower_mem hk hu hsuSide hupperPort hsu hm hvt ht
      have hparameter := parameter_ne source targetReadout hu hsuSide
        ((motion.before_shape.readout motion.before_positive).upper_endpoint hsuSide hupperPort)
        ((motion.after_shape.readout motion.after_positive).upper_endpoint hsuSide hupperPort) hbit
      have hlast : before.last ≠ after.last := by
        intro heq
        apply hparameter
        change ((readDepth p upper.level : ℤ) + 4 - before.last).toNat =
          ((readDepth p upper.level : ℤ) + 4 - after.last).toNat
        rw [heq]
      simpa only [← hmid] using motion.player_column (Or.inr hlast)

/-- Two decoded bits changed by the same real physical step have the same original port index. -/
theorem physicalInstance_axis_bits_changed_unique {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals)
    {axes next : List Bool} (source : l.AxisReadout p u axes) (targetReadout : l.AxisReadout p v next)
    {i j : ℕ} (hi : i < l.portCount) (hj : j < l.portCount)
    (hchangedI : axes.getD i false ≠ next.getD i false) (hchangedJ : axes.getD j false ≠ next.getD j false) : i = j := by
  have hI := l.physicalInstance_axis_bit_change_column p hl hM ha initial target hsu hm hvt ht source targetReadout hi hchangedI
  have hJ := l.physicalInstance_axis_bit_change_column p hl hM ha initial target hsu hm hvt ht source targetReadout hj hchangedJ
  exact axis_x_injective p (hI.symm.trans hJ)

/-- A real physical step projects to stuttering or one original legal axis flip whenever both decoded arrays are legal. -/
theorem physicalInstance_axisReadout_step {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals)
    {axes next : List Bool} (source : l.AxisReadout p u axes) (targetReadout : l.AxisReadout p v next)
    (hsource : l.InputLegal axes) (htarget : l.InputLegal next) : axes = next ∨ l.AxisStep axes next := by
  classical
  by_cases heq : axes = next
  · exact Or.inl heq
  · have hex : ∃ i < l.portCount, axes.getD i false ≠ next.getD i false := by
      by_contra hnone
      apply heq
      apply List.ext_getElem (source.axes_length.trans targetReadout.axes_length.symm)
      intro i hi hj
      have hip : i < l.portCount := by simpa only [source.axes_length] using hi
      have hbit : axes.getD i false = next.getD i false := by
        by_contra hn
        exact hnone ⟨i, hip, hn⟩
      simpa only [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] using hbit
    obtain ⟨i, hi, hbit⟩ := hex
    right
    refine ⟨hsource, i, hi, ?_, htarget⟩
    apply List.ext_getElem (by simp only [List.length_set, targetReadout.axes_length, source.axes_length])
    intro j hj hj'
    have hjp : j < l.portCount := by simpa only [targetReadout.axes_length] using hj
    have hread : next.getD j false = (axes.set i (!(axes.getD i false))).getD j false := by
      by_cases hij : i = j
      · subst j
        rw [List.getD_set_self (by simpa only [source.axes_length] using hi)]
        exact flip_of_ne _ _ hbit
      · rw [List.getD_set_ne hij]
        by_contra hne
        have hsame := l.physicalInstance_axis_bits_changed_unique p hl hM ha initial target hsu hm hvt ht
          source targetReadout hi hjp hbit (Ne.symm hne)
        exact hij hsame
    simpa only [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hj'] using hread

end Solution
end PushPuzzle.PushS.PortLayout
