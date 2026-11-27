/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramWireRowStockRTrimGeometry
import all Push.AcceptanceProgramTrimStock
import all Push.AcceptanceProgramLayout
import all PushS.EndpointWalking
import all PushS.PortSegments

/-! Exact whole-r-trim quotas: the public corridor plus its one canonical receiving cell. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS PushS.PortLayout

/-- The actual endpoint's public r corridor before its own work row. -/
@[expose] def endpointRCorridor (p : Scales.Parameters) (e : Endpoint) : Finset (Cell (p.W + 1) (p.H + 1)) :=
  Finset.univ.filter fun q => q.1.val = EndpointStreet.r.column p e ∧
    1 ≤ pageDepth p e.side q ∧ pageDepth p e.side q < p.Y e.level

private theorem trimBefore_interior (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (haxes : l.portCount ≤ p.axes) (target : List Bool) (side : Side) :
    (emit (trimBeforeSchedule l p target side) (targetHoles l p target)).remaining ⊆
      targetHoles l p target \ Boundary.frame := by
  rw [trimBeforeSchedule, emit_remaining_append]
  exact (emit_remaining_subset _ _).trans (by rw [sideClear_target_remaining l p hl haxes target])

private theorem r_work_slot_before_trim (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (target : List Bool)
    (e : Endpoint) (he : e ∈ l.endpoints) :
    endpointRWorkSlot l p target e ⊆
      (emit (trimBeforeSchedule l p target e.side) (targetHoles l p target)).remaining := by
  intro q hq
  obtain ⟨ht, hx, hy⟩ := Finset.mem_filter.mp hq
  obtain ⟨a, ha, hcol, hlevel, hpublic⟩ := endpoint_trim_column l p e he .r
  obtain ⟨he0, heM⟩ := l.endpoints_level_bounds p hl hM he
  obtain ⟨_, _, hc0, hcW⟩ := pageColumn_bounds l p hl hM haxes e.side ha
  have hY := readDepth_ge p he0 heM
  have hD := readDepth_add_lt_D p e.level
  rw [readDepth_eq p he0 heM] at hY hD
  have hH : p.H = 2 * p.D := rfl
  have hqH := q.2.isLt
  have hf : q ∉ Boundary.frame := by
    intro hf
    obtain ⟨d, hd⟩ := (Boundary.mem_frame q).mp hf
    rw [hcol] at hc0 hcW
    cases es : e.side <;> cases d <;>
      simp only [es, pageDepth, Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and,
        ite_true, reduceCtorEq, ite_false] at hy hd <;> omega
  cases es : e.side with
  | lower =>
    simpa only [es, trimBeforeSchedule, reduceCtorEq, ite_false, List.append_nil,
      sideClear_target_remaining l p hl haxes target] using Finset.mem_sdiff.mpr ⟨ht, hf⟩
  | upper =>
    rw [trimBeforeSchedule, ite_eq_left rfl, emit_remaining_append, sideClear_target_remaining l p hl haxes target]
    simp only [emit_remaining, allRegions, Finset.union_empty]
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_sdiff.mpr ⟨ht, hf⟩, ?_⟩
    intro hm
    obtain ⟨b, hb, _, _, hdepth⟩ := (mem_trim_region l p .lower q).mp hm
    obtain ⟨hb0, hbM, _⟩ := pageColumn_bounds l p hl hM haxes .lower hb
    have hbD := trimDepth_lt_D p hb0 hbM
    simp only [es, pageDepth, ite_true, reduceCtorEq, ite_false] at hy hdepth
    omega

/-- The target's full r-column trim quota is exactly its outer public corridor and its canonical work-hole payment. -/
theorem endpoint_r_trim_card (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (target : List Bool)
    (e : Endpoint) (he : e ∈ l.endpoints) :
    let T := (emit (trimBeforeSchedule l p target e.side) (targetHoles l p target)).remaining
    let U := (emit [trimRound l p e.side] T).remaining
    (T.filter fun q => q.1.val = EndpointStreet.r.column p e).card =
      (U.filter fun q => q.1.val = EndpointStreet.r.column p e).card + (p.Y e.level - 1) +
        endpointWorkDelta l p target e := by
  classical
  dsimp only
  let T := (emit (trimBeforeSchedule l p target e.side) (targetHoles l p target)).remaining
  let U := (emit [trimRound l p e.side] T).remaining
  let C := endpointRCorridor p e
  let R := endpointRWorkSlot l p target e
  obtain ⟨a, ha, hcol, hlevel, hpublic⟩ := endpoint_trim_column l p e he .r
  obtain ⟨he0, heM⟩ := l.endpoints_level_bounds p hl hM he
  obtain ⟨_, _, _, hcolW⟩ := pageColumn_bounds l p hl hM haxes e.side ha
  have hY := readDepth_add_lt_H p e.level
  rw [readDepth_eq p he0 heM] at hY
  have hT : T ⊆ targetHoles l p target \ Boundary.frame := trimBefore_interior l p hl haxes target e.side
  have hU : U = T \ (trimRound l p e.side).region := by
    simp only [U, emit_remaining, allRegions, Finset.union_empty]
  have hCR : C ∪ R ⊆ (trimRound l p e.side).region := by
    intro q hq
    apply endpoint_column_trim l p hl hM e he .r q
    · exact (Finset.mem_union.mp hq).elim (fun h => (Finset.mem_filter.mp h).2.1) (fun h => (Finset.mem_filter.mp h).2.1)
    · rcases Finset.mem_union.mp hq with hc | hr
      · exact (Finset.mem_filter.mp hc).2.2.2.le.trans (by omega)
      · exact (Finset.mem_filter.mp hr).2.2.le.trans (by omega)
  have hCRT : C ∪ R ⊆ T.filter fun q => q.1.val = EndpointStreet.r.column p e := by
    intro q hq
    rcases Finset.mem_union.mp hq with hc | hr
    · obtain ⟨_, hx, h0, hy⟩ := Finset.mem_filter.mp hc
      exact Finset.mem_filter.mpr ⟨corridor_before_trim l p hl hM haxes target e.side ha hpublic
        (hx.trans hcol.symm) h0 (hlevel.symm ▸ hy), hx⟩
    · exact Finset.mem_filter.mpr ⟨r_work_slot_before_trim l p hl hM haxes target e he hr, (Finset.mem_filter.mp hr).2.1⟩
  have hpart : T.filter (fun q => q.1.val = EndpointStreet.r.column p e) =
      U.filter (fun q => q.1.val = EndpointStreet.r.column p e) ∪ (C ∪ R) := by
    ext q
    constructor
    · intro hq
      obtain ⟨hqt, hx⟩ := Finset.mem_filter.mp hq
      by_cases hqu : q ∈ U
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hqu, hx⟩)
      · have hqr : q ∈ (trimRound l p e.side).region := by
          by_contra hn
          exact hqu (hU ▸ Finset.mem_sdiff.mpr ⟨hqt, hn⟩)
        obtain ⟨b, hb, _, hxb, hdb⟩ := (mem_trim_region l p e.side q).mp hqr
        have hlev := l.acceptancePageColumn_level_eq p hl e.side hb ha (hxb.symm.trans (hx.trans hcol.symm))
        have hdepth : pageDepth p e.side q < trimDepth p e.level := by rwa [hlev, hlevel] at hdb
        have hbase := hT hqt
        have hle := endpoint_r_trim_hole_depth l p hl hM haxes target e he
          (Finset.mem_sdiff.mp hbase).1 (Finset.mem_sdiff.mp hbase).2 hx hdepth
        apply Finset.mem_union_right
        by_cases hlt : pageDepth p e.side q < p.Y e.level
        · apply Finset.mem_union_left
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, hx, ?_, hlt⟩
          by_contra hn
          apply (Finset.mem_sdiff.mp hbase).2
          apply (Boundary.mem_frame q).mpr
          have hqH := q.2.isLt
          cases es : e.side
          · exact ⟨.north, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp only [es, pageDepth, ite_true] at hn; omega⟩⟩
          · exact ⟨.south, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp only [es, pageDepth, reduceCtorEq, ite_false] at hn; omega⟩⟩
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hbase).1, hx, by omega⟩)
    · intro hq
      rcases Finset.mem_union.mp hq with hu | hcr
      · obtain ⟨hu, hx⟩ := Finset.mem_filter.mp hu
        exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mp (hU ▸ hu) |>.1, hx⟩
      · exact hCRT hcr
  have hd : Disjoint (U.filter fun q => q.1.val = EndpointStreet.r.column p e) (C ∪ R) := by
    apply Finset.disjoint_left.mpr
    intro q hu hc
    exact (Finset.mem_sdiff.mp (hU ▸ (Finset.mem_filter.mp hu).1)).2 (hCR hc)
  have hdCR : Disjoint C R := by
    apply Finset.disjoint_left.mpr
    intro q hc hr
    have hc := (Finset.mem_filter.mp hc).2.2.2
    have hr := (Finset.mem_filter.mp hr).2.2
    omega
  have hcard : C.card = p.Y e.level - 1 := by
    simpa only [C, endpointRCorridor, hcol, hlevel] using
      corridor_card p e.side a hcolW (by rw [hlevel]; omega)
  rw [hpart, Finset.card_union_of_disjoint hd, Finset.card_union_of_disjoint hdCR, hcard]
  change (U.filter (fun q => q.1.val = EndpointStreet.r.column p e)).card + ((p.Y e.level - 1) + R.card) =
    (U.filter (fun q => q.1.val = EndpointStreet.r.column p e)).card + (p.Y e.level - 1) + R.card
  omega

end PushPuzzle.Push.AcceptanceProgram
