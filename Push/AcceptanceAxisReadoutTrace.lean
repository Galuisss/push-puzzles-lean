/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceAxisReadout
public import Push.FirstExit

/-! Project an actual physical trajectory with complete local axis readouts to the original axis path. -/

public section
namespace PushPuzzle.Push.AcceptanceAxisReadout

open PushFS PushS PushS.PortLayout

/-- Complete local axis observations along one actual physical trajectory. -/
structure TraceReadout (l : PortLayout) (p : Scales.Parameters)
    (B : Board (p.W + 1) (p.H + 1)) (start finish : State (p.W + 1) (p.H + 1))
    (initial target : List Bool) : Prop where
  exists_readout : ∀ u, Reachable B none start u → Reachable B none u finish →
    ∃ axes, l.AxisReadout p u axes
  initial_readout : ∀ axes, l.AxisReadout p start axes → axes = initial
  target_readout : ∀ axes, l.AxisReadout p finish axes → axes = target
  step_readout : ∀ {u v}, Reachable B none start u → Step B none u v → Reachable B none v finish →
    ∀ {axes next}, l.AxisReadout p u axes → l.AxisReadout p v next → axes = next ∨ l.AxisStep axes next

private theorem propagate {α : Type} {P : α → Prop} {a b : α}
    (hr : Relation.ReflTransGen (fun x y => P x → P y) a b) (ha : P a) : P b := by
  induction hr with
  | refl => exact ha
  | tail _ hm ih => exact hm ih

/-- Every complete readout along the actual source run lies on the original legal axis path. -/
private theorem TraceReadout.prefix_reachable {l : PortLayout} {p : Scales.Parameters}
    {B : Board (p.W + 1) (p.H + 1)} {start finish : State (p.W + 1) (p.H + 1)}
    {initial target : List Bool} (trace : TraceReadout l p B start finish initial target)
    {u : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable B none start u) (hut : Reachable B none u finish)
    {axes : List Bool} (decoded : l.AxisReadout p u axes) : Relation.ReflTransGen l.AxisStep initial axes := by
  let Inv (s : State (p.W + 1) (p.H + 1)) :=
    ∀ axes, l.AxisReadout p s axes → Relation.ReflTransGen l.AxisStep initial axes
  have hbase : Inv start := by
    intro axes hr
    rw [trace.initial_readout axes hr]
  have hpath : Relation.ReflTransGen (fun a b => Inv a → Inv b) start u := by
    apply Path.enrich hsu
    intro a b hsa hm hbu hinv next hnext
    obtain ⟨before, hbefore⟩ := trace.exists_readout a hsa
      ((Relation.ReflTransGen.single hm).trans (hbu.trans hut))
    have hprefix := hinv before hbefore
    rcases trace.step_readout hsa hm (hbu.trans hut) hbefore hnext with heq | hflip
    · exact heq ▸ hprefix
    · exact hprefix.tail hflip
  exact propagate hpath hbase axes decoded

/-- The complete actual physical trajectory projects to the original initial-to-target axis reachability. -/
theorem TraceReadout.reachable {l : PortLayout} {p : Scales.Parameters}
    {B : Board (p.W + 1) (p.H + 1)} {start finish : State (p.W + 1) (p.H + 1)}
    {initial target : List Bool} (trace : TraceReadout l p B start finish initial target)
    (hr : Reachable B none start finish) : Relation.ReflTransGen l.AxisStep initial target := by
  obtain ⟨axes, hread⟩ := trace.exists_readout finish hr .refl
  have hpath := trace.prefix_reachable hr .refl hread
  exact trace.target_readout axes hread ▸ hpath

end PushPuzzle.Push.AcceptanceAxisReadout
