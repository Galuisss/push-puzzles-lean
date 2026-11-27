/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceAxisReadoutInventory
public import PushS.PortEndpointReadouts

/-! Finite hole inventory of a genuine gate middle-axis terminal gap. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceAxisReadout

open PushFS PushS PushS.PortLayout

/-- Actual gate-axis holes from the central cut up to its lower work row. -/
def coreHoles (p : Scales.Parameters) (g : Placement) (u : State (p.W + 1) (p.H + 1)) :
    Finset (Cell (p.W + 1) (p.H + 1)) :=
  (holes u).filter fun q => q.1.val = p.x (g.left + 1) ∧
    p.D ≤ q.2.val ∧ q.2.val < p.H - readDepth p 1

/-- A genuine gate-axis readout has at most its shared parameter many lower terminal-gap holes. -/
private theorem gate_core_card_le {p : Scales.Parameters} {g : Placement} {upper : Endpoint}
    {u : State (p.W + 1) (p.H + 1)} {a : GateAxisPlacement}
    (joint : GateAxisReadout p g upper u a) : (coreHoles p g u).card ≤ a.parameter := by
  let index := fun q : Cell (p.W + 1) (p.H + 1) => p.H - readDepth p 1 - q.2.val - 1
  have hbound (q : Cell (p.W + 1) (p.H + 1)) (hq : q ∈ coreHoles p g u) : index q < a.parameter := by
    obtain ⟨hq, hx, hlo, hhi⟩ := Finset.mem_filter.mp hq
    have hg := (joint.core_holes q hx ⟨hlo, hhi⟩).mp hq
    dsimp only [index]
    omega
  have hinj : Set.InjOn index (coreHoles p g u) := by
    intro q hq r hr he
    obtain ⟨_, hqx, _, hqy⟩ := Finset.mem_filter.mp hq
    obtain ⟨_, hrx, _, hry⟩ := Finset.mem_filter.mp hr
    dsimp only [index] at he
    apply Prod.ext <;> apply Fin.ext
    · exact hqx.trans hrx.symm
    · omega
  have hsub : (coreHoles p g u).image index ⊆ Finset.range a.parameter := by
    intro i hi
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr (hbound q hq)
  have hc := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injOn hinj, Finset.card_range] at hc

/-- The actual lower terminal gap has exactly the shared gate-axis parameter many holes. -/
theorem gate_core_card {p : Scales.Parameters} {g : Placement} {upper : Endpoint}
    {u : State (p.W + 1) (p.H + 1)} {a : GateAxisPlacement}
    (joint : GateAxisReadout p g upper u a) (hp : g.left + 1 < p.axes) :
    (coreHoles p g u).card = a.parameter := by
  have hD := readDepth_add_lt_D p 1
  have hH : p.H = 2 * p.D := rfl
  have ha := joint.parameter_le
  have hx := x_add_readLength_lt_W p hp 0
  let f : Fin a.parameter → Cell (p.W + 1) (p.H + 1) := fun i =>
    (⟨p.x (g.left + 1), by omega⟩, ⟨p.H - readDepth p 1 - 1 - i.val, by have := i.isLt; omega⟩)
  have hinj : Function.Injective f := by
    intro i j he
    have hy := congrArg (fun q => q.2.val) he
    have hi := i.isLt
    have hj := j.isLt
    dsimp only [f] at hy
    apply Fin.ext
    omega
  have hsub : Finset.univ.image f ⊆ coreHoles p g u := by
    intro q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    have hi := i.isLt
    have hy : p.D ≤ (f i).2.val ∧ (f i).2.val < p.H - readDepth p 1 := by dsimp only [f]; omega
    apply Finset.mem_filter.mpr
    refine ⟨(joint.core_holes (f i) rfl hy).mpr ?_, rfl, hy⟩
    dsimp only [f]
    omega
  have hge := Finset.card_le_card hsub
  simp only [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at hge
  exact le_antisymm (gate_core_card_le joint) hge

end PushPuzzle.Push.AcceptanceAxisReadout
