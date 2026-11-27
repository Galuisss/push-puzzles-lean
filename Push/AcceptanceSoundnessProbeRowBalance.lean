/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessProbeRowDecomposition
import all Push.AcceptanceProgramProbeStockCells

/-! The actual full-row quotas give exact signed-observation totals on every allocated probe level. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram AcceptanceProbe
open scoped BigOperators

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate

/-- Every actual selected probe row consists of its fixed inventory and its real same-level observations. -/
private theorem canonical_probe_row_observed_card
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ p.levels) (hrow : p.Y j + 2 ∈ probeRows l p) :
    ((AcceptanceProbeNumerics.residual l p target t).filter fun q => q.2.val = p.Y j + 2).card =
      ((probeFixedStock l p).filter fun q => q.2.val = p.Y j + 2).card +
        ∑ i ∈ Finset.univ.filter (fun i : Fin l.portCount => level l hl i = j),
          AcceptanceProbeNumerics.observed l p hl target t i := by
  classical
  have hstock := canonical_probe_stock_decomposition l p hl hM haxes initial target hgate hr ha
  have he : ((AcceptanceProbeNumerics.residual l p target t).filter fun q => q.2.val ∈ probeRows l p).filter
      (fun q => q.2.val = p.Y j + 2) =
      (AcceptanceProbeNumerics.residual l p target t).filter (fun q => q.2.val = p.Y j + 2) := by
    ext q
    simp only [Finset.mem_filter]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · exact fun h => ⟨⟨h.1, h.2 ▸ hrow⟩, h.2⟩
  have hd := canonical_probe_stock_disjoint l p hl hM haxes target t
  have hd' : Disjoint ((probeFixedStock l p).filter fun q => q.2.val = p.Y j + 2)
      ((probeObservedStock l p hl hM haxes target t).filter fun q => q.2.val = p.Y j + 2) :=
    hd.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  calc
    _ = (((probeFixedStock l p ∪ probeObservedStock l p hl hM haxes target t).filter
        fun q => q.2.val = p.Y j + 2)).card := by rw [← hstock, he]
    _ = ((probeFixedStock l p).filter fun q => q.2.val = p.Y j + 2).card +
        ((probeObservedStock l p hl hM haxes target t).filter fun q => q.2.val = p.Y j + 2).card := by
      rw [Finset.filter_union, Finset.card_union_of_disjoint hd']
    _ = _ := by rw [probeObservedStock_row_card l p hl hM haxes target t hj hjm]

/-- Every actual probe level pays exactly its target-bit sum after cancelling the identical fixed bitmap. -/
theorem canonical_probe_row_balance
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) (j : ℕ) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin l.portCount => level l hl i = j),
      AcceptanceProbeNumerics.observed l p hl target t i =
      ∑ i ∈ Finset.univ.filter (fun i : Fin l.portCount => level l hl i = j), (target.getD i.val false).toNat := by
  classical
  let K := Finset.univ.filter fun i : Fin l.portCount => level l hl i = j
  by_cases he : K = ∅
  · change ∑ i ∈ K, _ = ∑ i ∈ K, _
    simp only [he, Finset.sum_empty]
  · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr he
    have hij : level l hl i = j := (Finset.mem_filter.mp hi).2
    have hb := probeLevel_bounds l p hl hM i
    rw [hij] at hb
    have hrow := probeCell_mem_rows l p hl hM haxes i
    change p.Y (level l hl i) + 2 ∈ probeRows l p at hrow
    rw [hij] at hrow
    have hactual := canonical_probe_row_observed_card l p hl hM haxes initial target hgate hr ha hb.1 hb.2 hrow
    have hreference := canonical_probe_row_target_ledger l p hl hM haxes initial target hr ha hb.1 hb.2 hrow
    change ((AcceptanceProbeNumerics.residual l p target t).filter fun q => q.2.val = p.Y j + 2).card = _ at hreference
    omega

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
