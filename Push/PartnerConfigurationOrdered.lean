/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.PartnerConfigurationRepair
public import PushS.PortOrderReachability
import all Push.PartnerConfiguration
import all Push.PartnerInternal
import all Push.PartnerInternalValidity
import all Push.PartnerConfigurationCutsLegal
import all Push.PartnerConfigurationRepair

/-! Reader-partner direction compilation preserves the actual AND light-input order. -/

@[expose] public section
namespace PushPuzzle.Push.Partner

open PushS

private theorem earExtend_ordered {l : PortLayout} (hl : PortInventory l) {cut : ℕ}
    (hc : cut ≤ l.portCount)
    (hs : SafeCut l cut) {ab : ℕ × ℕ} (hp : ab ∈ l.upperPairs) {axes : List Bool}
    (haxes : l.OrderedInputs axes) : (ear l cut ab).OrderedInputs (earExtend l cut ab axes) := by
  refine ⟨earExtend_legal hl hc hs hp haxes.toInputLegal, ?_⟩
  intro first hg hmiddle
  obtain ⟨old, hold, rfl⟩ := (ear_gate_mem l cut ab .andGate first).mp hg
  obtain ⟨h₀, h₁, _⟩ := earState_gate_reads hl hs hold axes (!(axes.getD ab.2 false)) (axes.getD ab.2 false)
  change (earState l cut axes _ _).getD _ false = false at hmiddle ⊢
  rw [h₀]
  apply haxes.and_ordered old hold
  rwa [h₁] at hmiddle

private theorem bufferAtAxes_ordered (s : BufferState) (first : ℕ) (hs : PortInventory s.layout)
    {axes : List Bool} (haxes : s.layout.OrderedInputs axes) :
    (s.bufferAt first).layout.OrderedInputs (bufferAtAxes s first axes) := by
  unfold bufferAtAxes BufferState.bufferAt
  split_ifs with hg hl hr
  · obtain ⟨kind, hgate⟩ := BufferState.gate_of_any hg
    have hc := inventory_gate_bound hs hgate
    exact earExtend_ordered hs (by omega) (inventory_gate_boundary_safe hs hgate).1 hl haxes
  · obtain ⟨kind, hgate⟩ := BufferState.gate_of_any hg
    exact earExtend_ordered hs (inventory_gate_bound hs hgate) (inventory_gate_boundary_safe hs hgate).2 hr haxes
  all_goals exact haxes

private theorem scanAxes_ordered (s : BufferState) (positions : List ℕ)
    (hs : PortInventory s.layout)
    {axes : List Bool} (haxes : s.layout.OrderedInputs axes) :
    (s.scan positions).layout.OrderedInputs (scanAxes s positions axes) := by
  induction positions generalizing s axes with
  | nil => exact haxes
  | cons first rest ih =>
    exact ih (s.bufferAt first) (s.bufferAt_inventory first hs) (bufferAtAxes_ordered s first hs haxes)

private theorem internalAxes_ordered {l : PortLayout} (hl : PortInventory l) {axes : List Bool}
    (haxes : l.OrderedInputs axes) :
    (bufferInternal l).layout.OrderedInputs (internalAxes l axes) := scanAxes_ordered _ _ hl haxes

namespace Cuts

private theorem cutExtend_ordered {l : PortLayout} (hl : l.pages.Valid) {cut : ℕ}
    (hc : cut ≤ l.portCount)
    (hs : SafeCut l cut) {axes : List Bool} (haxes : l.OrderedInputs axes) :
    (compile l cut).OrderedInputs (cutExtend l cut axes) := by
  refine ⟨cutExtend_legal hl hc hs haxes.toInputLegal, ?_⟩
  intro first hg hmiddle
  obtain ⟨old, hold, rfl⟩ := (compile_gate_mem l cut .andGate first).mp hg
  obtain ⟨h₀, h₁, _⟩ := cutState_gate_reads (inventory_of_pages hl) hs hold axes
    (activeValues l cut axes false) (activeValues l cut axes true)
  change (cutState l cut axes _ _).getD _ false = false at hmiddle ⊢
  rw [h₀]
  apply haxes.and_ordered old hold
  rwa [h₁] at hmiddle

private theorem cutAtAxes_ordered (s : BufferState) (cut : ℕ) (hs : s.layout.pages.Valid)
    (hc : cut ≤ s.layout.portCount)
    {axes : List Bool} (haxes : s.layout.OrderedInputs axes) :
    (cutAt s cut).layout.OrderedInputs (cutAtAxes s cut axes) := by
  unfold cutAtAxes cutAt
  split_ifs with hsafe
  · exact cutExtend_ordered hs hc ((safeTest_eq_true s.layout cut).mp hsafe) haxes
  · exact haxes

private theorem scanAxes_ordered (s : BufferState) (positions : List ℕ) (hs : s.layout.pages.Valid)
    (hb : ∀ cut ∈ positions, cut ≤ s.layout.portCount) {axes : List Bool} (haxes : s.layout.OrderedInputs axes) :
    (scan s positions).layout.OrderedInputs (scanAxes s positions axes) := by
  induction positions generalizing s axes with
  | nil => exact haxes
  | cons cut rest ih =>
    exact ih (cutAt s cut) (cutAt_valid s cut hs (hb cut List.mem_cons_self)) (remaining_bounds hb)
      (cutAtAxes_ordered s cut hs (hb cut List.mem_cons_self) haxes)

/-- The actual complete axis emitter preserves each original AND's prescribed light-input order. -/
theorem repairAxes_ordered {l : PortLayout} (hl : l.pages.Valid) {axes : List Bool} (haxes : l.OrderedInputs axes) :
    (repair l).layout.OrderedInputs (repairAxes l axes) := by
  apply scanAxes_ordered _ _ (bufferInternal_valid hl)
  · intro cut hc
    exact (List.mem_range.mp (List.mem_reverse.mp hc)).le
  · exact internalAxes_ordered (inventory_of_pages hl) haxes

end Cuts
end PushPuzzle.Push.Partner
