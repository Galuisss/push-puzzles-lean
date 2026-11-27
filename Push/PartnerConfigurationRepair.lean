/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.PartnerConfigurationCutsReachability

/-! Exact full direction-array and weighted reachability compilation through reader-partner repair. -/

@[expose] public section
namespace PushPuzzle.Push.Partner.Cuts

open PushS

/-- Extend the direction word exactly when the actual layout program performs a common cut. -/
def cutAtAxes (s : BufferState) (cut : ℕ) (axes : List Bool) : List Bool :=
  if safeTest s.layout cut then cutExtend s.layout cut axes else axes

private theorem cutAtAxes_length (s : BufferState) (cut : ℕ) (axes : List Bool)
    (hlen : axes.length = s.layout.portCount) :
    (cutAtAxes s cut axes).length = (cutAt s cut).layout.portCount := by
  unfold cutAtAxes cutAt
  split_ifs
  · exact cutState_length _ _ _ _ _
  · exact hlen

private theorem cutAtAxes_reachable_iff (s : BufferState) (cut : ℕ) (hs : s.layout.pages.Valid)
    (hc : cut ≤ s.layout.portCount)
    (axes next : List Bool) (hlen : axes.length = s.layout.portCount) (hnlen : next.length = s.layout.portCount) :
    Relation.ReflTransGen (cutAt s cut).layout.AxisStep (cutAtAxes s cut axes) (cutAtAxes s cut next) ↔
      Relation.ReflTransGen s.layout.AxisStep axes next := by
  unfold cutAtAxes cutAt
  split_ifs with hsafe
  · exact cutExtend_reachable_iff hs hc ((safeTest_eq_true s.layout cut).mp hsafe) axes next hlen hnlen
  · rfl

/-- Execute the same finite list of actual common-cut operations on its direction array. -/
def scanAxes (s : BufferState) : List ℕ → List Bool → List Bool
  | [], axes => axes
  | cut :: rest, axes => scanAxes (cutAt s cut) rest (cutAtAxes s cut axes)

theorem scanAxes_length (s : BufferState) (positions : List ℕ) (axes : List Bool)
    (hlen : axes.length = s.layout.portCount) : (scanAxes s positions axes).length = (scan s positions).layout.portCount := by
  induction positions generalizing s axes with
  | nil => exact hlen
  | cons cut rest ih => exact ih (cutAt s cut) _ (cutAtAxes_length s cut axes hlen)

private theorem remaining_bounds {s : BufferState} {cut : ℕ} {positions : List ℕ}
    (hb : ∀ c ∈ cut :: positions, c ≤ s.layout.portCount) :
    ∀ c ∈ positions, c ≤ (cutAt s cut).layout.portCount := by
  intro c hc
  exact (hb c (List.mem_cons_of_mem cut hc)).trans (cutAt_count_ge s cut)

private theorem scanAxes_reachable_iff (s : BufferState) (positions : List ℕ)
    (hs : s.layout.pages.Valid)
    (hb : ∀ cut ∈ positions, cut ≤ s.layout.portCount) (axes next : List Bool)
    (hlen : axes.length = s.layout.portCount) (hnlen : next.length = s.layout.portCount) :
    Relation.ReflTransGen (scan s positions).layout.AxisStep (scanAxes s positions axes) (scanAxes s positions next) ↔
      Relation.ReflTransGen s.layout.AxisStep axes next := by
  induction positions generalizing s axes next with
  | nil => rfl
  | cons cut rest ih =>
    have hc := hb cut List.mem_cons_self
    exact (ih (cutAt s cut) (cutAt_valid s cut hs hc) (remaining_bounds hb) _ _
      (cutAtAxes_length s cut axes hlen) (cutAtAxes_length s cut next hnlen)).trans
      (cutAtAxes_reachable_iff s cut hs hc axes next hlen hnlen)

/-- The complete physical-axis emitter for the actual reader-partner repaired layout. -/
def repairAxes (l : PortLayout) (axes : List Bool) : List Bool :=
  let s := bufferInternal l
  scanAxes s (List.range s.layout.portCount).reverse (internalAxes l axes)

theorem repairAxes_length (l : PortLayout) (axes : List Bool) (hlen : axes.length = l.portCount) :
    (repairAxes l axes).length = (repair l).layout.portCount :=
  scanAxes_length _ _ _ (internalAxes_length l axes hlen)

/-- The complete actual repaired layout preserves and reflects the original weighted axis-configuration problem. -/
theorem repairAxes_reachable_iff {l : PortLayout} (hl : l.pages.Valid) (axes next : List Bool)
    (hlen : axes.length = l.portCount) (hnlen : next.length = l.portCount) :
    Relation.ReflTransGen (repair l).layout.AxisStep (repairAxes l axes) (repairAxes l next) ↔
      Relation.ReflTransGen l.AxisStep axes next := by
  have hs := bufferInternal_valid hl
  have hb : ∀ cut ∈ (List.range (bufferInternal l).layout.portCount).reverse,
      cut ≤ (bufferInternal l).layout.portCount := by
    intro cut hc
    exact (List.mem_range.mp (List.mem_reverse.mp hc)).le
  exact (scanAxes_reachable_iff _ _ hs hb _ _ (internalAxes_length l axes hlen) (internalAxes_length l next hnlen)).trans
    (internalAxes_reachable_iff (inventory_of_pages hl) axes next hlen hnlen)

end PushPuzzle.Push.Partner.Cuts
