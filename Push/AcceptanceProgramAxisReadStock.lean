/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramAxisReadStockPrefix
public import PushS.PortOrdinaryAxis
import all Push.AcceptanceProgramAxisReadStockPrefix
import all Push.AcceptanceProgramMainStockGeometry
import all Push.AcceptanceProgramGuardStockReads
import all Push.AcceptanceProgramThirdClear
import all Push.AcceptanceProgramLayout
import all PushS.PortEndpointCounts
import all PushS.PortCoreCrossing
import all PushS.PortSegments

/-! The ordinary part of the actual combined axis read pays the one complementary lower tip. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushFS.Reduction PushS PushS.PortLayout SegmentRecipe

/-- Before R15 an ordinary axis contains only its lower optional tip, exactly for a false target bit. -/
private theorem axisRead_before_stock_iff (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (target : List Bool) {upper lower : Endpoint} (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (hsu : upper.side = .upper) (hsl : lower.side = .lower) (hport : lower.port = upper.port)
    {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val = p.x upper.port) :
    q ∈ (emit (axisReadBefore l p target) (targetHoles l p target)).remaining ↔
      target.getD upper.port false = false ∧ q.2.val = p.H - (p.Y lower.level + 2) := by
  constructor
  · intro hq
    have hi := take_stock_interior l p target 15 (by omega) hq
    obtain ⟨ht, hf⟩ := Finset.mem_sdiff.mp hi
    have hq0 : q.2.val ≠ 0 := by
      intro he
      exact hf ((Boundary.mem_frame q).mpr ⟨.north, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩⟩)
    have hqH : q.2.val ≠ p.H := by
      intro he
      exact hf ((Boundary.mem_frame q).mpr ⟨.south, by simp [Boundary.edge, he]⟩)
    have hrow := q.2.isLt
    have hR : q ∈ ordinaryAxis p upper.port := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx, by omega, by omega⟩
    have hnear := (congrArg (fun E : Finset (Cell (p.W + 1) (p.H + 1)) => q ∈ E)
      (l.encodedSegments_ordinaryAxis p hl hM haxes (l.canonical target) hu hlow hsu hsl hport)).mp
        (Finset.mem_inter.mpr ⟨ht, hR⟩)
    have hxu : q.1.val = p.x upper.port := hx
    have hxl : q.1.val = p.x lower.port := by simpa only [hport] using hx
    have hnU := emit_stage_excluded (mainRound_mem_axisReadBefore l p target .upper) hq
    have hnL := emit_stage_excluded (mainRound_mem_axisReadBefore l p target .lower) hq
    have huDepth : p.Y upper.level + 2 ≤ q.2.val := by
      by_contra hn
      apply hnU
      rw [← hsu]
      apply (mainRound_column_region l p hl upper hu hxu).mpr
      simpa only [pageDepth, hsu, ite_true] using Nat.lt_of_not_ge hn
    have hlDepth : p.Y lower.level + 2 ≤ p.H - q.2.val := by
      by_contra hn
      apply hnL
      rw [← hsl]
      apply (mainRound_column_region l p hl lower hlow hxl).mpr
      simpa only [pageDepth, hsl, reduceCtorEq, ite_false] using Nat.lt_of_not_ge hn
    obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hnear
    rcases List.mem_append.mp hs with hs | hs
    · have haxis := (axis_mem p (l.canonical target) upper _).mp ((mem_pointHoles _ _).mpr ⟨s, hs, hc⟩)
      obtain ⟨hj, hjm⟩ := l.endpoints_level_bounds p hl hM hu
      rw [readDepth_eq p hj hjm] at haxis
      have hb := Bool.toNat_le ((l.canonical target).axes.getD upper.port false)
      simp only [hsu, onSide, ite_true] at haxis
      have hy : q.2.val = p.Y upper.level + 2 := by omega
      have hprobe : q.2.val ∈ probeRows l p := by
        apply List.mem_toFinset.mpr
        exact List.mem_map.mpr ⟨upper, List.mem_filter.mpr ⟨hu, by simp [hsu]⟩, hy.symm⟩
      exact False.elim (emit_stage_excluded (probe_mem_axisReadBefore l p target) hq
        ((readRows_region p .west _ (Or.inl rfl) q).mpr hprobe))
    · have haxis := (axis_mem p (l.canonical target) lower _).mp ((mem_pointHoles _ _).mpr ⟨s, hs, hc⟩)
      obtain ⟨hj, hjm⟩ := l.endpoints_level_bounds p hl hM hlow
      have hY := readDepth_add_lt_H p lower.level
      rw [readDepth_eq p hj hjm] at haxis hY
      have hbit : (l.canonical target).axes.getD lower.port false = target.getD upper.port false := by
        change target.getD lower.port false = target.getD upper.port false
        rw [hport]
      simp only [hsl, onSide, reduceCtorEq, ite_false, hbit, coordinates] at haxis
      cases hb : target.getD upper.port false
      · exact ⟨rfl, by simp only [hb, Bool.not_false, Bool.toNat_true] at haxis; omega⟩
      · simp only [hb, Bool.not_true, Bool.toNat_false, Nat.add_zero] at haxis
        omega
  · rintro ⟨hb, hy⟩
    apply lower_axis_tip_before l p hl hM haxes target lower hlow hsl
      (by simpa only [hport] using hb) (by simpa only [hport] using hx) hy

/-- The actual ordinary R15 input column has the complementary zero-or-one target inventory. -/
private theorem axisRead_before_column_card (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (target : List Bool) {upper lower : Endpoint} (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (hsu : upper.side = .upper) (hsl : lower.side = .lower) (hport : lower.port = upper.port) :
    (((emit (axisReadBefore l p target) (targetHoles l p target)).remaining).filter
      fun q => q.1.val = p.x upper.port).card = 1 - (target.getD upper.port false).toNat := by
  classical
  cases hb : target.getD upper.port false with
  | false =>
    simp only [Bool.toNat_false, Nat.sub_zero]
    have hxW := x_add_readLength_lt_W p ((l.endpoints_port_lt hl hlow).trans_le haxes) 0
    let tip : Cell (p.W + 1) (p.H + 1) :=
      (⟨p.x lower.port, by omega⟩, ⟨p.H - (p.Y lower.level + 2), by omega⟩)
    apply Finset.card_eq_one.mpr
    refine ⟨tip, Finset.ext (fun q => ?_)⟩
    constructor
    · intro hq
      obtain ⟨hq, hx⟩ := Finset.mem_filter.mp hq
      have hy := ((axisRead_before_stock_iff l p hl hM haxes target hu hlow hsu hsl hport hx).mp hq).2
      apply Finset.mem_singleton.mpr
      exact Prod.ext (Fin.ext (by change q.1.val = p.x lower.port; simpa only [hport] using hx)) (Fin.ext hy)
    · intro hq
      have hqt : q = tip := Finset.mem_singleton.mp hq
      have hx : q.1.val = p.x upper.port := by rw [hqt]; exact congrArg p.x hport
      apply Finset.mem_filter.mpr
      exact ⟨(axisRead_before_stock_iff l p hl hM haxes target hu hlow hsu hsl hport hx).mpr
        ⟨hb, by rw [hqt]⟩, hx⟩
  | true =>
    simp only [Bool.toNat_true, Nat.sub_self]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_of_forall_notMem
    intro q hq
    obtain ⟨hq, hx⟩ := Finset.mem_filter.mp hq
    have he := ((axisRead_before_stock_iff l p hl hM haxes target hu hlow hsu hsl hport hx).mp hq).1
    rw [hb] at he
    cases he

private theorem ordinary_axis_not_core (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (lower : Endpoint) (hlow : lower ∈ l.endpoints) (hsl : lower.side = .lower) : p.x lower.port ∉ cores l p := by
  intro hc
  obtain ⟨i, hi, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hc)
  have hip : i = lower.port := axis_injective p he
  obtain ⟨kind, first, hg, hm⟩ := center_gate_mem l hi
  exact l.endpoints_lower_ne_gate_middle hl hg hlow hsl (hip.symm.trans hm)

/-- The actual combined axis read consumes the complete remaining ordinary column. -/
private theorem axisRead_after_column_empty (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (_hM : l.pages.highest ≤ p.levels) (_haxes : l.portCount ≤ p.axes)
    (target : List Bool) {upper lower : Endpoint} (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (_hsu : upper.side = .upper) (hsl : lower.side = .lower) (hport : lower.port = upper.port) :
    (((emit [axisReadRound l p] (emit (axisReadBefore l p target) (targetHoles l p target)).remaining).remaining).filter
      fun q => q.1.val = p.x upper.port) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro q hq
  obtain ⟨hq, hx⟩ := Finset.mem_filter.mp hq
  apply emit_stage_excluded (List.mem_cons_self (a := axisReadRound l p)) hq
  apply (mem_readRegion _ _ q).mpr
  refine ⟨(p.x upper.port, p.H + 1), List.mem_append_left _ ?_, hx, q.2.isLt⟩
  apply (mem_prefixRequests _ _ _ _).mpr
  refine ⟨Finset.mem_sdiff.mpr ⟨?_, ?_⟩, rfl⟩
  · apply List.mem_toFinset.mpr
    exact List.mem_map.mpr ⟨upper.port, List.mem_range.mpr (l.endpoints_port_lt hl hu), rfl⟩
  · simpa only [hport] using ordinary_axis_not_core l p hl lower hlow hsl

/-- Every ordinary column pays precisely the complementary target bit in the actual R15 block. -/
theorem axisRead_target_column_loss (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (target : List Bool) {upper lower : Endpoint} (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (hsu : upper.side = .upper) (hsl : lower.side = .lower) (hport : lower.port = upper.port) :
    let T := (emit (axisReadBefore l p target) (targetHoles l p target)).remaining
    let U := (emit [axisReadRound l p] T).remaining
    (U.filter fun q => q.1.val = p.x upper.port).card + (1 - (target.getD upper.port false).toNat) =
      (T.filter fun q => q.1.val = p.x upper.port).card := by
  dsimp only
  rw [axisRead_after_column_empty l p hl hM haxes target hu hlow hsu hsl hport,
    Finset.card_empty, Nat.zero_add, axisRead_before_column_card l p hl hM haxes target hu hlow hsu hsl hport]

end PushPuzzle.Push.AcceptanceProgram
