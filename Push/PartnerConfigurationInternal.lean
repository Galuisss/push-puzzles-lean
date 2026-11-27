/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.PartnerConfigurationReachability
import all Push.PartnerInternal

/-! Exact configuration words and full reachability through the actual internal-ear compiler. -/

@[expose] public section
namespace PushPuzzle.Push.Partner

open PushS

/-- Extend directions along the actual ear selected by one gate inspection. -/
def bufferAtAxes (s : BufferState) (first : ℕ) (axes : List Bool) : List Bool :=
  if BufferState.gateTest s.layout first then
    if (first, first + 1) ∈ s.layout.upperPairs then
      earExtend s.layout first (first, first + 1) axes
    else if (first + 1, first + 2) ∈ s.layout.upperPairs then
      earExtend s.layout (first + 3) (first + 1, first + 2) axes
    else axes
  else axes

private theorem bufferAtAxes_length (s : BufferState) (first : ℕ) (axes : List Bool)
    (hlen : axes.length = s.layout.portCount) :
    (bufferAtAxes s first axes).length = (s.bufferAt first).layout.portCount := by
  unfold bufferAtAxes BufferState.bufferAt
  split_ifs <;> (try simp only [earExtend, earState_length, BufferState.insertEar, ear])
  all_goals exact hlen

private theorem bufferAtAxes_reachable_iff (s : BufferState) (first : ℕ)
    (hs : PortInventory s.layout)
    (axes next : List Bool) (hlen : axes.length = s.layout.portCount) (hnlen : next.length = s.layout.portCount) :
    Relation.ReflTransGen (s.bufferAt first).layout.AxisStep
        (bufferAtAxes s first axes) (bufferAtAxes s first next) ↔ Relation.ReflTransGen s.layout.AxisStep axes next := by
  unfold bufferAtAxes BufferState.bufferAt
  split_ifs with hg hl hr
  · obtain ⟨kind, hgate⟩ := BufferState.gate_of_any hg
    have hc := inventory_gate_bound hs hgate
    exact earExtend_reachable_iff hs (by omega) (inventory_gate_boundary_safe hs hgate).1 hl _ _ hlen hnlen
  · obtain ⟨kind, hgate⟩ := BufferState.gate_of_any hg
    exact earExtend_reachable_iff hs (inventory_gate_bound hs hgate) (inventory_gate_boundary_safe hs hgate).2 hr _ _ hlen hnlen
  all_goals rfl

/-- Run the same actual descending-ear layout program on its full direction array. -/
def scanAxes (s : BufferState) : List ℕ → List Bool → List Bool
  | [], axes => axes
  | first :: rest, axes => scanAxes (s.bufferAt first) rest (bufferAtAxes s first axes)

theorem scanAxes_length (s : BufferState) (positions : List ℕ) (axes : List Bool)
    (hlen : axes.length = s.layout.portCount) : (scanAxes s positions axes).length = (s.scan positions).layout.portCount := by
  induction positions generalizing s axes with
  | nil => exact hlen
  | cons first rest ih => exact ih (s.bufferAt first) _ (bufferAtAxes_length s first axes hlen)

private theorem scanAxes_reachable_iff (s : BufferState) (positions : List ℕ)
    (hs : PortInventory s.layout)
    (axes next : List Bool) (hlen : axes.length = s.layout.portCount) (hnlen : next.length = s.layout.portCount) :
    Relation.ReflTransGen (s.scan positions).layout.AxisStep (scanAxes s positions axes) (scanAxes s positions next) ↔
      Relation.ReflTransGen s.layout.AxisStep axes next := by
  induction positions generalizing s axes next with
  | nil => rfl
  | cons first rest ih =>
    exact (ih (s.bufferAt first) (s.bufferAt_inventory first hs) _ _
      (bufferAtAxes_length s first axes hlen) (bufferAtAxes_length s first next hnlen)).trans
      (bufferAtAxes_reachable_iff s first hs axes next hlen hnlen)

/-- Canonical complete axis directions for the actual internal-ear output. -/
def internalAxes (l : PortLayout) (axes : List Bool) : List Bool :=
  scanAxes (BufferState.start l) (List.range l.portCount).reverse axes

theorem internalAxes_length (l : PortLayout) (axes : List Bool) (hlen : axes.length = l.portCount) :
    (internalAxes l axes).length = (bufferInternal l).layout.portCount := scanAxes_length _ _ axes hlen

/-- The full actual gate-internal ear compiler preserves and reflects original weighted axis reachability. -/
theorem internalAxes_reachable_iff {l : PortLayout} (hl : PortInventory l) (axes next : List Bool)
    (hlen : axes.length = l.portCount) (hnlen : next.length = l.portCount) :
    Relation.ReflTransGen (bufferInternal l).layout.AxisStep (internalAxes l axes) (internalAxes l next) ↔
      Relation.ReflTransGen l.AxisStep axes next := scanAxes_reachable_iff _ _ hl axes next hlen hnlen

end PushPuzzle.Push.Partner
