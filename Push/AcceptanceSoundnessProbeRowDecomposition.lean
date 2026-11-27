/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessProbeFixedStock
public import Push.AcceptanceProbeNumerics
import all Push.AcceptanceProgramProbeStockCells
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceSoundnessCentral

/-! Actual full probe rows split into the certified fixed stock and their genuine port observations. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram AcceptanceProbe
open scoped BigOperators

/-- The actual selected main-axis probe points, read directly from the real R13 residual. -/
@[expose] noncomputable def probeObservedStock (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (target : List Bool) (t : State (p.W + 1) (p.H + 1)) : Finset (Cell (p.W + 1) (p.H + 1)) :=
  (Finset.univ.filter fun i : Fin l.portCount => probeCell l p hl hM haxes i ∈ AcceptanceProbeNumerics.residual l p target t).map
    (probeEmbedding l p hl hM haxes)

private theorem observed_eq_indicator (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (target : List Bool) (t : State (p.W + 1) (p.H + 1)) (i : Fin l.portCount) :
    AcceptanceProbeNumerics.observed l p hl target t i =
      if probeCell l p hl hM haxes i ∈ AcceptanceProbeNumerics.residual l p target t then 1 else 0 := by
  classical
  let A := AcceptanceProbeNumerics.residual l p target t
  let point := probeCell l p hl hM haxes i
  have unique : ∀ q : Cell (p.W + 1) (p.H + 1),
      q.1.val = p.x i.val → q.2.val = p.Y (level l hl i) + 2 → q = point := by
    intro q hx hy
    exact Prod.ext (Fin.ext hx) (Fin.ext hy)
  by_cases hm : point ∈ A
  · have he : (A.filter fun q => q.1.val = p.x i.val ∧ q.2.val = p.Y (level l hl i) + 2) = {point} := by
      ext q
      constructor
      · intro hq
        exact Finset.mem_singleton.mpr (unique q (Finset.mem_filter.mp hq).2.1 (Finset.mem_filter.mp hq).2.2)
      · intro hq
        have hqp := Finset.mem_singleton.mp hq
        subst q
        exact Finset.mem_filter.mpr ⟨hm, rfl, rfl⟩
    change (A.filter fun q => q.1.val = p.x i.val ∧ q.2.val = p.Y (level l hl i) + 2).card = _
    rw [he, Finset.card_singleton, ite_eq_left hm]
  · have he : (A.filter fun q => q.1.val = p.x i.val ∧ q.2.val = p.Y (level l hl i) + 2) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro q hq
      obtain ⟨hq, hx, hy⟩ := Finset.mem_filter.mp hq
      exact hm (unique q hx hy ▸ hq)
    change (A.filter fun q => q.1.val = p.x i.val ∧ q.2.val = p.Y (level l hl i) + 2).card = _
    rw [he, Finset.card_empty, ite_eq_right hm]

/-- The observed main-axis stock on one allocated row counts the same-level real numeric observations. -/
theorem probeObservedStock_row_card (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (target : List Bool) (t : State (p.W + 1) (p.H + 1))
    {j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ p.levels) :
    ((probeObservedStock l p hl hM haxes target t).filter fun q => q.2.val = p.Y j + 2).card =
      ∑ i ∈ Finset.univ.filter (fun i : Fin l.portCount => level l hl i = j),
        AcceptanceProbeNumerics.observed l p hl target t i := by
  classical
  rw [probeObservedStock, Finset.filter_map, Finset.card_map]
  change (Finset.filter (fun i => (probeEmbedding l p hl hM haxes i).2.val = p.Y j + 2)
    (Finset.univ.filter fun i => probeCell l p hl hM haxes i ∈ AcceptanceProbeNumerics.residual l p target t)).card = _
  have he : (Finset.filter (fun i => (probeEmbedding l p hl hM haxes i).2.val = p.Y j + 2)
      (Finset.univ.filter fun i => probeCell l p hl hM haxes i ∈ AcceptanceProbeNumerics.residual l p target t)) =
      (Finset.univ.filter fun i : Fin l.portCount => level l hl i = j).filter
        (fun i => probeCell l p hl hM haxes i ∈ AcceptanceProbeNumerics.residual l p target t) := by
    ext i
    have hrow : (probeEmbedding l p hl hM haxes i).2.val = p.Y j + 2 ↔ level l hl i = j :=
      probeCell_row_eq_iff l p hl hM haxes i hj hjm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hrow]
    exact and_comm
  rw [he, Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  exact (observed_eq_indicator l p hl hM haxes target t i).symm

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate

/-- The complete actual probe-read input is its genuine fixed stock plus exactly the observed port points. -/
theorem canonical_probe_stock_decomposition
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    ((AcceptanceProbeNumerics.residual l p target t).filter fun q => q.2.val ∈ probeRows l p) =
      probeFixedStock l p ∪ probeObservedStock l p hl hM haxes target t := by
  classical
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  ext q
  constructor
  · intro hq
    obtain ⟨hq, hrow⟩ := Finset.mem_filter.mp hq
    by_cases hmain : q.1 ∈ l.mainColumnSet p
    · rcases (l.mainColumnSet_iff p q.1).mp hmain with h0 | hW | ⟨i, hi, hx⟩
      · exact (canonical_residual_not_frame l p hl hM haxes initial target hr ha 13 (by omega) hq
          ((Boundary.mem_frame q).mpr ⟨.west, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩⟩)).elim
      · exact (canonical_residual_not_frame l p hl hM haxes initial target hr ha 13 (by omega) hq
          ((Boundary.mem_frame q).mpr ⟨.east, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩)).elim
      · let port : Fin l.portCount := ⟨i, hi⟩
        have hy := AcceptanceProbeNumerics.canonical_probe_port_location l p hl hM haxes initial target hgate port hr ha hq hrow hx
        have hpoint : probeCell l p hl hM haxes port = q :=
          Prod.ext (Fin.ext hx.symm) (Fin.ext hy.symm)
        apply Finset.mem_union_right
        apply Finset.mem_map.mpr
        exact ⟨port, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpoint ▸ hq⟩, hpoint⟩
    · exact Finset.mem_union_left _ ((canonical_probe_nonmain_fixed_iff l p hl hM haxes initial target hgate hr ha hrow hmain).mp hq)
  · intro hq
    rcases Finset.mem_union.mp hq with hfixed | hmain
    · have hrow := (Finset.mem_filter.mp hfixed).2
      have hnmain := probeFixedStock_not_main l p hl hM haxes hfixed
      exact Finset.mem_filter.mpr
        ⟨(canonical_probe_nonmain_fixed_iff l p hl hM haxes initial target hgate hr ha hrow hnmain).mpr hfixed, hrow⟩
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hmain
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).2, probeCell_mem_rows l p hl hM haxes i⟩

omit hgate

/-- Fixed and observed pieces of the actual R13 probe stock are disjoint. -/
theorem canonical_probe_stock_disjoint (t : State (p.W + 1) (p.H + 1)) :
    Disjoint (probeFixedStock l p) (probeObservedStock l p hl hM haxes target t) := by
  classical
  apply Finset.disjoint_left.mpr
  intro q hfixed hmain
  have hn := probeFixedStock_not_main l p hl hM haxes hfixed
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hmain
  exact hn ((l.mainColumnSet_iff p _).mpr (Or.inr (Or.inr ⟨i.val, i.isLt, rfl⟩)))

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
