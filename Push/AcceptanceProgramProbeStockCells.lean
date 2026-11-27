/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProbePartners
public import Push.AcceptanceProgramStock
import all Push.AcceptanceProbePartners
import all Push.AcceptanceProgramLayout
import all PushS.PortLayoutCoordinates
import all PushS.PortWireGeometry

/-! Literal upper-axis probe cells, indexed by the actual original finite ports. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS PushS.PortLayout AcceptanceProbe
open scoped BigOperators

/-- The selected actual upper endpoint retains its positive allocated working level. -/
theorem probeLevel_bounds (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (i : Fin l.portCount) :
    1 ≤ level l hl i ∧ level l hl i ≤ p.levels :=
  l.endpoints_level_bounds p hl hM (upperEndpoint_spec l hl i).1

noncomputable section

/-- The actual Y+2 principal-axis cell of one original port's unique upper endpoint. -/
@[expose] def probeCell (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (i : Fin l.portCount) :
    Cell (p.W + 1) (p.H + 1) :=
  (⟨p.x i.val, by have h := x_add_readLength_lt_W p (i.isLt.trans_le haxes) 0; omega⟩,
    ⟨p.Y (level l hl i) + 2, by
      have hb := probeLevel_bounds l p hl hM i
      have h := readDepth_add_lt_H p (level l hl i)
      rw [readDepth_eq p hb.1 hb.2] at h
      omega⟩)

/-- Distinct actual ports have distinct physical upper probe cells. -/
@[expose] def probeEmbedding (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) :
    Fin l.portCount ↪ Cell (p.W + 1) (p.H + 1) where
  toFun := probeCell l p hl hM haxes
  inj' := by
    intro i j he
    have hx := congrArg (fun q => q.1.val) he
    change (i.val + 1) * p.D = (j.val + 1) * p.D at hx
    have hD : 0 < p.D := by have h := p.outer_distance; omega
    have he := Nat.mul_right_cancel hD hx
    exact Fin.ext (by omega)

/-- Exactly the true target bits contribute the actual upper main-axis probe points. -/
@[expose] def probeSignalStock (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (target : List Bool) :
    Finset (Cell (p.W + 1) (p.H + 1)) :=
  (Finset.univ.filter fun i : Fin l.portCount => target.getD i.val false = true).map
    (probeEmbedding l p hl hM haxes)

end

/-- Every literal probe cell lies on one of the emitter's actual upper probe rows. -/
theorem probeCell_mem_rows (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (i : Fin l.portCount) :
    (probeCell l p hl hM haxes i).2.val ∈ probeRows l p := by
  obtain ⟨he, hs, _⟩ := upperEndpoint_spec l hl i
  apply List.mem_toFinset.mpr
  exact List.mem_map.mpr ⟨upperEndpoint l hl i, List.mem_filter.mpr ⟨he, by simp [hs]⟩, rfl⟩

private theorem level_eq_of_probe_row (p : Scales.Parameters) {i j : ℕ}
    (hi : 1 ≤ i) (him : i ≤ p.levels) (hj : 1 ≤ j) (hjm : j ≤ p.levels)
    (he : p.Y i + 2 = p.Y j + 2) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have hg := depth_gap p hi h hjm
    rw [readDepth_eq p hi him, readDepth_eq p hj hjm] at hg
    omega
  · exact h
  · have hg := depth_gap p hj h him
    rw [readDepth_eq p hj hjm, readDepth_eq p hi him] at hg
    omega

/-- Physical upper probe-row equality is exactly equality of the actual allocated levels. -/
theorem probeCell_row_eq_iff (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (i : Fin l.portCount)
    {j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ p.levels) :
    (probeCell l p hl hM haxes i).2.val = p.Y j + 2 ↔ level l hl i = j := by
  constructor
  · exact level_eq_of_probe_row p (probeLevel_bounds l p hl hM i).1 (probeLevel_bounds l p hl hM i).2 hj hjm
  · intro he
    change p.Y (level l hl i) + 2 = p.Y j + 2
    rw [he]

/-- The actual true-bit probe points on one allocated row count precisely the same-level target bits. -/
theorem probeSignalStock_row_card (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (target : List Bool)
    {j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ p.levels) :
    ((probeSignalStock l p hl hM haxes target).filter fun q => q.2.val = p.Y j + 2).card =
      ∑ i ∈ Finset.univ.filter (fun i : Fin l.portCount => level l hl i = j),
        (target.getD i.val false).toNat := by
  rw [probeSignalStock, Finset.filter_map, Finset.card_map]
  change (Finset.filter (fun a => (probeEmbedding l p hl hM haxes a).2.val = p.Y j + 2)
      (Finset.univ.filter fun i : Fin l.portCount => target.getD i.val false = true)).card = _
  have he : (Finset.filter (fun a => (probeEmbedding l p hl hM haxes a).2.val = p.Y j + 2)
      (Finset.univ.filter fun i : Fin l.portCount => target.getD i.val false = true)) =
      (Finset.univ.filter fun i : Fin l.portCount => level l hl i = j).filter
        (fun i => target.getD i.val false = true) := by
    ext i
    have hrow : (probeEmbedding l p hl hM haxes i).2.val = p.Y j + 2 ↔ level l hl i = j :=
      probeCell_row_eq_iff l p hl hM haxes i hj hjm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hrow]
    exact and_comm
  rw [he, Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases target.getD i.val false <;> simp only [Bool.false_eq_true, ite_false,
    ite_true, Bool.toNat_false, Bool.toNat_true]

end PushPuzzle.Push.AcceptanceProgram
