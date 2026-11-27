/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramInterlevelStockGeometry
import all Push.AcceptanceProgramRounds
import all Push.AcceptanceProgramColumns
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramInterlevelStock
import all Push.AcceptanceProgramNarrowSignals

/-! Lossless clears preserve every literal target hole that none of the preceding reads touches. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS PushS.PortLayout

/-- A hole survives every actual lossless clear until one of the literal read prefixes encounters it. -/
theorem emit_mem_of_no_reads {w h : ℕ} (stages : List Template) (E : Finset (Cell w h))
    (hz : (emit stages E).discarded = 0) {q : Cell w h} (hq : q ∈ E)
    (hr : ∀ side requests, Template.read side requests ∈ stages → q ∉ readRegion side requests) :
    q ∈ (emit stages E).remaining := by
  induction stages generalizing E with
  | nil => exact hq
  | cons stage rest ih =>
    have hr' : ∀ side requests, Template.read side requests ∈ rest → q ∉ readRegion side requests :=
      fun side requests hs => hr side requests (List.mem_cons_of_mem _ hs)
    cases stage with
    | read side requests =>
      apply ih _ hz _ hr'
      rw [emitReads_remaining]
      exact Finset.mem_sdiff.mpr ⟨hq, hr side requests (List.mem_cons_self ..)⟩
    | clear side lanes =>
      have hz' : (emit rest (E.filter fun p => side.lane p ∉ lanes)).discarded = 0 := by
        simp only [emit] at hz
        omega
      apply ih _ hz' _ hr'
      apply Finset.mem_filter.mpr
      refine ⟨hq, ?_⟩
      intro hm
      have he : (E.filter fun p => side.lane p ∈ lanes).card = 0 := by
        simp only [emit] at hz
        omega
      exact Finset.notMem_empty q ((Finset.card_eq_zero.mp he) ▸ Finset.mem_filter.mpr ⟨hq, hm⟩)

private theorem trimDepth_lt_D (p : Scales.Parameters) {j : ℕ} (hj : 1 ≤ j) :
    trimDepth p j < p.D := by
  by_cases hh : j < p.levels
  · have hb := interlevelDepth_bounds p hj hh
    simp only [trimDepth, ite_eq_left hh]
    change interlevelDepth p j < p.D
    omega
  · have hd := readDepth_add_lt_D p 0
    simp only [trimDepth, ite_eq_right hh]
    omega

/-- The first actual midpoint marker is just outside every same-column trim prefix on both pages. -/
theorem interlevelMarker_not_trim (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (side readSide : Side)
    {q : Cell (p.W + 1) (p.H + 1)} (hm : InterlevelMarker l p side q) :
    q ∉ (trimRound l p readSide).region := by
  obtain ⟨a, ha, hj, hjm, hx, hy⟩ := hm
  intro hread
  obtain ⟨b, hb, _, hxb, hd⟩ := (mem_trim_region l p readSide q).mp hread
  by_cases he : side = readSide
  · subst readSide
    have hlevel := l.acceptancePageColumn_level_eq p hl side ha hb (hx.symm.trans hxb)
    rw [hlevel] at hy
    omega
  · have hb' := l.acceptancePageColumn_level_bounds p hl hM readSide hb
    have htrim := trimDepth_lt_D p hb'.1
    have hrow := marker_row p side hj hjm hy
    have hbound := interlevelDepth_bounds p hj hjm
    have hh : p.H = 2 * p.D := rfl
    cases side <;> cases readSide <;> simp only [reduceCtorEq, not_true_eq_false] at he
    all_goals simp only [pageDepth, interlevelRow, ite_true, reduceCtorEq, ite_false] at hrow hd
    all_goals omega

private theorem privateColumn_metadata (l : PortLayout) (p : Scales.Parameters) {x : ℕ}
    (hx : x ∈ privateColumns l p) :
    ∃ a ∈ pageColumns l p .lower, a.column = x ∧ a.level = 1 := by
  obtain ⟨a, ha, hx⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
  obtain ⟨ha, hp⟩ := List.mem_filter.mp ha
  refine ⟨a, ha, hx, ?_⟩
  unfold pageColumns at ha
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨_, _, ha⟩ := List.mem_flatMap.mp ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> cases hp
  · rw [ite_eq_left rfl] at ha
    obtain ⟨_, _, ha⟩ := List.mem_flatMap.mp ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The short private-cap read stops before every true interlevel marker. -/
theorem interlevelMarker_not_private (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (side : Side) {q : Cell (p.W + 1) (p.H + 1)}
    (hm : InterlevelMarker l p side q) : q ∉ (privateRound l p).region := by
  obtain ⟨a, ha, hj, hjm, hx, hy⟩ := hm
  intro hread
  obtain ⟨hc, hd⟩ := (private_region l p q).mp hread
  have hrow := marker_row p side hj hjm hy
  have hb := interlevelDepth_bounds p hj hjm
  have hD := readDepth_add_lt_D p 1
  rw [readDepth_eq p le_rfl p.levels_pos] at hD
  have hh : p.H = 2 * p.D := rfl
  cases side with
  | upper => simp only [interlevelRow, ite_true] at hrow; omega
  | lower =>
    obtain ⟨b, hb', hxb, hbj⟩ := privateColumn_metadata l p hc
    have he := l.acceptanceLowerColumn_level p hl ha hb' (hx.symm.trans hxb.symm)
    have haj : a.level = 1 := he.trans hbj
    rw [haj] at hjm hb hrow
    have hgap := p.interlevel_margin 1 le_rfl
    simp only [interlevelRow, interlevelDepth, reduceCtorEq, ite_false] at hrow
    omega

/-- Every literal axis probe row is one of the actual selected working rows. -/
theorem probeRows_subset_workRows (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) : probeRows l p ⊆ workRows l p := by
  intro y hy
  obtain ⟨e, he, hy⟩ := List.mem_map.mp (List.mem_toFinset.mp hy)
  have hbound := l.endpoints_level_bounds p hl hM (List.mem_filter.mp he).1
  have hw := (level_work_rows l p .upper hbound.1 hbound.2).2
  exact hy ▸ hw

/-- A true interlevel marker is outside the actual principal-axis prefix on either page. -/
theorem interlevelMarker_not_main (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (side readSide : Side) {q : Cell (p.W + 1) (p.H + 1)} (hm : InterlevelMarker l p side q) :
    q ∉ (mainRound l p readSide).region := by
  obtain ⟨a, ha, _, _, hx, _⟩ := hm
  have haux := hx ▸ l.acceptancePageColumn_aux p hl hM haxes side ha
  intro hread
  obtain ⟨_, hreq, hcol, _⟩ := (mem_readRegion _ _ q).mp hread
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hreq
  have he := (List.mem_filter.mp he).1
  have hx' : q.1.val = p.x e.port := by cases readSide <;> exact hcol
  apply (Finset.mem_sdiff.mp haux).2
  apply Finset.mem_union_left
  apply List.mem_toFinset.mpr
  exact List.mem_map.mpr ⟨e.port, List.mem_range.mpr (l.endpoints_port_lt hl he), hx'.symm⟩

/-- Short lower sample probes end before upper markers and use no lower marker column. -/
theorem interlevelMarker_not_sample (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (side : Side) {q : Cell (p.W + 1) (p.H + 1)}
    (hm : InterlevelMarker l p side q) :
    q ∉ readRegion .south (prefixRequests (samples l p) fun _ => p.D - 4) := by
  obtain ⟨a, ha, hj, hjm, hx, hy⟩ := hm
  intro hread
  obtain ⟨⟨lane, span⟩, hreq, hcol, hpos⟩ := (mem_readRegion _ _ q).mp hread
  obtain ⟨hlane, hspan⟩ := (mem_prefixRequests _ _ _ _).mp hreq
  have hrow := marker_row p side hj hjm hy
  have hb := interlevelDepth_bounds p hj hjm
  have hh : p.H = 2 * p.D := rfl
  cases side with
  | upper =>
    simp only [interlevelRow, ite_true] at hrow
    simp only [prefixRank, Nat.add_sub_cancel, hspan] at hpos
    omega
  | lower =>
    change q.1.val = lane at hcol
    exact l.acceptanceLowerColumn_not_sample p hl ha (hx ▸ (hcol.symm ▸ hlane))

end PushPuzzle.Push.AcceptanceProgram
