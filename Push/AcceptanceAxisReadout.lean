/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.PortAxisDecode
public import PushS.PortInputStep
import all PushS.PortAxisDecodeStep
import CslibFrontier.Foundations.Data.List.Lookup

/-! Assemble complete original axis words from genuine endpoint readouts and actual single-bit changes. -/

public section
namespace PushPuzzle.Push.AcceptanceAxisReadout

open PushFS PushS PushS.PortLayout

/-- Genuine upper endpoint words determine one complete existing Boolean axis array. -/
theorem axisReadout_exists_of_endpoint_words (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    {u : State (p.W + 1) (p.H + 1)}
    (hex : ∀ e ∈ l.endpoints, e.side = .upper → ∃ parameter shift, EndpointAxisReadout p e u parameter shift) :
    ∃ axes, l.AxisReadout p u axes := by
  classical
  have hport (i : Fin l.portCount) : ∃ e : Endpoint,
      e ∈ l.endpoints ∧ e.side = .upper ∧ e.port = i.val ∧
        ∃ parameter shift, EndpointAxisReadout p e u parameter shift := by
    obtain ⟨e, he, hs, hp⟩ := l.endpoints_upper_exists hl i.isLt
    exact ⟨e, he, hs, hp, hex e he hs⟩
  choose endpoint endpoint_mem endpoint_side endpoint_port parameter shift word using hport
  let axes := List.ofFn fun i : Fin l.portCount => decide (parameter i ≤ 1)
  refine ⟨axes, ⟨List.length_ofFn, hex, ?_⟩⟩
  intro e he hs parameter' shift' word'
  let i : Fin l.portCount := ⟨e.port, l.endpoints_port_lt hl he⟩
  have heq : endpoint i = e := l.endpoints_key_injective hl (endpoint_mem i) he
    ((endpoint_side i).trans hs.symm) (endpoint_port i)
  have hword : EndpointAxisReadout p e u (parameter i) (shift i) := heq ▸ word i
  have hparameter := l.endpoint_axis_parameter_unique p hl hM haxes he hword word'
  change (List.ofFn fun j : Fin l.portCount => decide (parameter j ≤ 1)).getD e.port false = true ↔ _
  rw [List.getD_ofFn_of_lt _ (l.endpoints_port_lt hl he) false]
  change decide (parameter i ≤ 1) = true ↔ _
  rw [decide_eq_true_eq, hparameter]

/-- Two legal complete arrays differing at at most one actual port stutter or form one original axis step. -/
private theorem axisReadout_step_of_changed_unique {l : PortLayout} {p : Scales.Parameters}
    {u v : State (p.W + 1) (p.H + 1)} {axes next : List Bool}
    (source : l.AxisReadout p u axes) (target : l.AxisReadout p v next)
    (hsource : l.InputLegal axes) (htarget : l.InputLegal next)
    (hunique : ∀ i < l.portCount, ∀ j < l.portCount,
      axes.getD i false ≠ next.getD i false → axes.getD j false ≠ next.getD j false → i = j) :
    axes = next ∨ l.AxisStep axes next := by
  classical
  by_cases heq : axes = next
  · exact Or.inl heq
  · have hex : ∃ i < l.portCount, axes.getD i false ≠ next.getD i false := by
      by_contra hnone
      apply heq
      apply List.ext_getElem (source.axes_length.trans target.axes_length.symm)
      intro i hi hj
      have hip : i < l.portCount := by simpa only [source.axes_length] using hi
      have hbit : axes.getD i false = next.getD i false := by
        by_contra hn
        exact hnone ⟨i, hip, hn⟩
      simpa only [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] using hbit
    obtain ⟨i, hi, hbit⟩ := hex
    right
    refine ⟨hsource, i, hi, ?_, htarget⟩
    apply List.ext_getElem (by simp only [List.length_set, target.axes_length, source.axes_length])
    intro j hj hj'
    have hjp : j < l.portCount := by simpa only [target.axes_length] using hj
    have hread : next.getD j false = (axes.set i (!(axes.getD i false))).getD j false := by
      by_cases hij : i = j
      · subst j
        rw [List.getD_set_self (by simpa only [source.axes_length] using hi)]
        exact flip_of_ne _ _ hbit
      · rw [List.getD_set_ne hij]
        by_contra hne
        exact hij (hunique i hi j hjp hbit (Ne.symm hne))
    simpa only [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hj'] using hread

/-- Locating every changed bit on the same actual player column gives a single original legal axis flip. -/
theorem axisReadout_step_of_columns {l : PortLayout} {p : Scales.Parameters}
    {u v : State (p.W + 1) (p.H + 1)} {axes next : List Bool}
    (source : l.AxisReadout p u axes) (target : l.AxisReadout p v next)
    (hsource : l.InputLegal axes) (htarget : l.InputLegal next)
    (hcolumn : ∀ i < l.portCount, axes.getD i false ≠ next.getD i false → u.player.1.val = p.x i) :
    axes = next ∨ l.AxisStep axes next := by
  apply axisReadout_step_of_changed_unique source target hsource htarget
  intro i hi j hj hbi hbj
  exact axis_x_injective p ((hcolumn i hi hbi).symm.trans (hcolumn j hj hbj))

end PushPuzzle.Push.AcceptanceAxisReadout
