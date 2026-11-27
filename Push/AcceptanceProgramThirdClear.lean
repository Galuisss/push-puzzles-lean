/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramSecondClear
public import Push.AcceptanceProgramStock
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramFirstClear
import all Push.AcceptanceProgramSecondClear
import all Push.AcceptanceProgramNarrowFixed
import all Push.AcceptanceProgramNarrowSignals

/-! The central flank and private-cap probes justify the third actual row clear. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS PushS.PortLayout SegmentRecipe

/-- The four literal read blocks completing preparation after its second row clear. -/
def markerPreparation (l : PortLayout) (p : Scales.Parameters) : List Template :=
  [privateRound l p, readRows p .east {p.D - 2, p.D + 2},
    .read .north (prefixRequests (guards l p) fun _ => p.D - 4), readRows p .west {p.D - 4}]

/-- The marked schedule's first thirteen blocks split at the second row clear. -/
theorem preparation_eq_secondRows (l : PortLayout) (p : Scales.Parameters) (k : ℕ) :
    preparation l p k = secondRowSchedule l p k ++ markerPreparation l p := by
  simp only [preparation, secondRowSchedule, mainAxisSchedule, firstRowSchedule, firstTrimSchedule,
    markerPreparation, mainRound, mainTop, mainBottom, privateRound, privateColumns,
    firstRowKeep, secondRowKeep, List.append_assoc, List.cons_append, List.nil_append,
    reduceCtorEq, ite_true, ite_false]

/-- Every clear in all thirteen preparation blocks has zero target loss. -/
theorem preparation_discarded_zero (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (target : List Bool) :
    (emit (preparation l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target)).discarded = 0 := by
  rw [preparation_eq_secondRows, emit_discarded_append, secondRows_discarded_zero l p hl hM ha target]
  simp only [markerPreparation, privateRound, readRows, emit, Nat.add_zero]

/-- The actual combined ordinary-axis and gate-core prefix block. -/
def axisReadRound (l : PortLayout) (p : Scales.Parameters) : Template :=
  .read .north (prefixRequests (axes l p \ cores l p) (fun _ => p.H + 1) ++
    prefixRequests (cores l p) (fun _ => p.H - p.Y 1))

/-- The four actual probe/axis blocks between preparation and the third row clear. -/
def axisTail (l : PortLayout) (p : Scales.Parameters) : List Template :=
  [readRows p .west (probeRows l p), .clear .east (probeRows l p), axisReadRound l p,
    .clear .north (axes l p \ cores l p)]

/-- Seventeen actual blocks, ending with the ordinary-axis clear. -/
def axisSchedule (l : PortLayout) (p : Scales.Parameters) (k : ℕ) : List Template :=
  preparation l p k ++ axisTail l p

/-- Exact row set retained at the third row clear. -/
def thirdRowKeep (l : PortLayout) (p : Scales.Parameters) : Finset ℕ :=
  workRows l p ∪ cutRows p ∪ {p.D + 4}

private theorem core_prefix_subset_axis (l : PortLayout) (p : Scales.Parameters) :
    (corePrefixRound l p).region (w := p.W + 1) (h := p.H + 1) ⊆ (axisReadRound l p).region := by
  rw [corePrefixRound, axisReadRound, Template.region, Template.region, readRegion_append]
  exact Finset.subset_union_right

private theorem axis_has_prep {l : PortLayout} {p : Scales.Parameters} {k : ℕ} {stage : Template}
    (hs : stage ∈ preparation l p k) : stage ∈ axisSchedule l p k :=
  List.mem_append_left _ hs

private theorem prep_has_marker {l : PortLayout} {p : Scales.Parameters} {k : ℕ} {stage : Template}
    (hs : stage ∈ markerPreparation l p) : stage ∈ preparation l p k := by
  rw [preparation_eq_secondRows]
  exact List.mem_append_right _ hs

private theorem prep_has_firstRow {l : PortLayout} {p : Scales.Parameters} {k : ℕ} {stage : Template}
    (hs : stage ∈ firstRowSchedule l p k) : stage ∈ preparation l p k := by
  rw [preparation_eq_secondRows, secondRowSchedule, mainAxisSchedule]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hs))

private theorem stock_interlevel_cut (l : PortLayout) (p : Scales.Parameters) (side : Side)
    {q : Cell (p.W + 1) (p.H + 1)} (hm : InterlevelMarker l p side q) : q.2.val ∈ cutRows p := by
  obtain ⟨a, _, hj, hjm, _, hy⟩ := hm
  rw [trimDepth, ite_eq_left hjm] at hy
  have hH0 := readDepth_add_lt_H p a.level
  have hH1 := readDepth_add_lt_H p (a.level + 1)
  rw [readDepth_eq p hj (by omega)] at hH0
  rw [readDepth_eq p (by omega) (by omega)] at hH1
  have hrow : q.2.val = if side = .upper then (p.Y a.level + p.Y (a.level + 1)) / 2
      else p.H - (p.Y a.level + p.Y (a.level + 1)) / 2 := by
    cases side <;> simp only [pageDepth, ite_true, ite_false, reduceCtorEq] at hy ⊢ <;>
      have := q.2.isLt <;> omega
  rw [hrow]
  apply List.mem_toFinset.mpr
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨a.level - 1, List.mem_range.mpr (by omega), ?_⟩
  have he : a.level - 1 + 1 = a.level := by omega
  have he' : a.level - 1 + 2 = a.level + 1 := by omega
  simp only [he, he']
  cases side <;> simp

/-- The actual axis-stage residual consists of original target holes outside the consumed frame. -/
theorem axis_remaining_source (l : PortLayout) (p : Scales.Parameters) (target : List Bool)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ (emit (axisSchedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target)).remaining) : q ∈ targetHoles l p target \ Boundary.frame := by
  rw [axisSchedule, emit_remaining_append] at hq
  have hq := emit_remaining_subset _ _ hq
  rw [preparation_eq_secondRows, emit_remaining_append] at hq
  have hq := emit_remaining_subset _ _ hq
  rw [secondRowSchedule, emit_remaining_append] at hq
  have hq := emit_remaining_subset _ _ hq
  rw [mainAxisSchedule, emit_remaining_append] at hq
  have hq := emit_remaining_subset _ _ hq
  rw [firstRowSchedule, emit_remaining_append] at hq
  have hq := emit_remaining_subset _ _ hq
  rw [firstTrimSchedule, emit_remaining_append] at hq
  have hh := emit_remaining_subset _ _ hq
  rwa [frame_remaining] at hh

/-- Actual target stock remaining after all public, private and main-axis prefixes have been read. -/
inductive AxisStock (l : PortLayout) (p : Scales.Parameters) (q : Cell (p.W + 1) (p.H + 1)) : Prop
  | work (row : q.2.val ∈ workRows l p)
  | interlevel (side : Side) (marker : InterlevelMarker l p side q)
  | half (row : q.2.val = p.H - p.Y 1 / 2) (column : q.1.val ∈ cores l p ∪ privateColumns l p)
  | central (band : p.D ≤ q.2.val + 4 ∧ q.2.val ≤ p.D + 4)

/-- The actual axis-stage residual has only working, interlevel, half-depth and central stock. -/
theorem axis_remaining_inventory (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (target : List Bool)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ (emit (axisSchedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target)).remaining) : AxisStock l p q := by
  let k := (targetHoles l p target \ Boundary.frame).card
  change q ∈ (emit (axisSchedule l p k) (targetHoles l p target)).remaining at hq
  obtain ⟨hsource, hf⟩ := Finset.mem_sdiff.mp (axis_remaining_source l p target hq)
  have hnot (stage : Template) (hs : stage ∈ axisSchedule l p k) : q ∉ stage.region :=
    emit_stage_excluded hs hq
  have htrim (side : Side) : q ∉ (trimRound l p side).region := by
    apply hnot
    apply axis_has_prep
    apply prep_has_firstRow
    simp only [firstRowSchedule, firstTrimSchedule, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false]
    cases side
    · exact Or.inl (Or.inr (Or.inr (Or.inr rfl)))
    · exact Or.inl (Or.inr (Or.inr (Or.inl rfl)))
  have hmain (side : Side) : q ∉ (mainRound l p side).region := by
    apply hnot
    apply axis_has_prep
    rw [preparation_eq_secondRows, secondRowSchedule, mainAxisSchedule]
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_right
    cases side <;> simp
  have hprivate : q ∉ (privateRound l p).region := by
    apply hnot
    apply axis_has_prep
    apply prep_has_marker
    simp only [markerPreparation, List.mem_cons]
    exact Or.inl trivial
  have hcore : q ∉ (corePrefixRound l p).region := by
    intro hc
    apply hnot (axisReadRound l p) ?_ (core_prefix_subset_axis l p hc)
    apply List.mem_append_right
    simp only [axisTail, List.mem_cons]
    exact Or.inr (Or.inr (Or.inl trivial))
  cases l.acceptanceStock p hl hM (l.canonical target) hsource hf with
  | work hy => exact .work hy
  | trim side ht => exact False.elim (htrim side ht)
  | main side hm => exact False.elim (hmain side hm)
  | privateCap hp => exact False.elim (hprivate hp)
  | coreNear hc => exact False.elim (hcore hc)
  | interlevel side hm => exact .interlevel side hm
  | half hy hx => exact .half hy hx
  | central hb => exact .central hb

set_option maxHeartbeats 800000 in
/-- Every target hole left after the actual private, marker and main-axis probes is retained by the third clear. -/
theorem target_third_rows_supported (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (target : List Bool)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ (emit (axisSchedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target)).remaining) : q.2.val ∈ thirdRowKeep l p := by
  let k := (targetHoles l p target \ Boundary.frame).card
  change q ∈ (emit (axisSchedule l p k) (targetHoles l p target)).remaining at hq
  have hsecond : q ∈ (emit (secondRowSchedule l p k) (targetHoles l p target)).remaining := by
    rw [axisSchedule, emit_remaining_append] at hq
    have hq := emit_remaining_subset _ _ hq
    rw [preparation_eq_secondRows, emit_remaining_append] at hq
    exact emit_remaining_subset _ _ hq
  have hnarrow : q.2.val ∈ secondRowKeep l p := by
    rw [secondRowSchedule, emit_remaining_append] at hsecond
    exact target_second_rows_supported l p hl hM target (emit_remaining_subset _ _ hsecond)
  have hnot (stage : Template) (hs : stage ∈ axisSchedule l p k) : q ∉ stage.region :=
    emit_stage_excluded hs hq
  cases axis_remaining_inventory l p hl hM target hq with
  | work hy => exact Finset.mem_union_left _ (Finset.mem_union_left _ hy)
  | interlevel side hm => exact Finset.mem_union_left _ (Finset.mem_union_right _ (stock_interlevel_cut l p side hm))
  | half hy hx =>
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    rw [hy]
    simp only [cutRows, List.mem_toFinset, List.mem_append, List.mem_cons]
    tauto
  | central hb =>
    by_contra hrow
    have hwork : q.2.val ∉ workRows l p := fun hw => hrow (Finset.mem_union_left _ (Finset.mem_union_left _ hw))
    have hcut : q.2.val ∉ cutRows p := fun hc => hrow (Finset.mem_union_left _ (Finset.mem_union_right _ hc))
    have hplus : q.2.val ≠ p.D + 4 := fun he => hrow (Finset.mem_union_right _ (Finset.mem_singleton.mpr he))
    have hrowNot (rows : Finset ℕ) (side : Direction) (hside : side = .west ∨ side = .east)
        (hs : readRows p side rows ∈ markerPreparation l p) : q.2.val ∉ rows := by
      intro hy
      exact hnot _ (axis_has_prep (prep_has_marker hs)) ((readRows_region p side rows hside q).mpr hy)
    have hm2 : q.2.val ∉ ({p.D - 2, p.D + 2} : Finset ℕ) :=
      hrowNot _ .east (Or.inr rfl) (by unfold markerPreparation; exact .tail _ (.head _))
    have hm4 : q.2.val ≠ p.D - 4 := by
      have hh := hrowNot {p.D - 4} .west (Or.inl rfl) (by unfold markerPreparation; exact .tail _ (.tail _ (.tail _ (.head _))))
      simpa only [Finset.mem_singleton] using hh
    have hD := readDepth_add_lt_D p 1
    rw [readDepth_eq p le_rfl p.levels_pos] at hD
    have hH : p.H = 2 * p.D := rfl
    simp only [secondRowKeep, keepRows, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hnarrow
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm2
    rcases hnarrow with ((hw | hc) | hm) | he
    · exact hwork hw
    · exact hcut hc
    · tauto
    · omega

/-- The full-row probe clear and full-column ordinary-axis clear are lossless for every stock. -/
private theorem axisTail_discarded_zero (l : PortLayout) (p : Scales.Parameters)
    (E : Finset (Cell (p.W + 1) (p.H + 1))) : (emit (axisTail l p) E).discarded = 0 := by
  have hprobe := clear_rows_after_read p [readRows p .west (probeRows l p)] E (probeRows l p)
    .west .east (Or.inl rfl) (Or.inr rfl) (List.mem_cons_self ..)
  have haxis := clear_columns_after_combined_read p
    [readRows p .west (probeRows l p), .clear .east (probeRows l p), axisReadRound l p] E
    (axes l p \ cores l p) (prefixRequests (cores l p) fun _ => p.H - p.Y 1)
    (by change axisReadRound l p ∈ _; exact .tail _ (.tail _ (.head _)))
  simp only [axisTail, axisReadRound, readRows, emit, Nat.add_zero] at hprobe haxis ⊢
  rw [hprobe, haxis, Finset.card_empty, Nat.zero_add]

/-- Every clear in the seventeen actual blocks before the third row clear is lossless. -/
private theorem axisSchedule_discarded_zero (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (target : List Bool) :
    (emit (axisSchedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target)).discarded = 0 := by
  rw [axisSchedule, emit_discarded_append, preparation_discarded_zero l p hl hM ha target,
    axisTail_discarded_zero, Nat.zero_add]

/-- The third actual row clear deletes zero canonical target holes. -/
private theorem target_third_row_clear_empty (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (target : List Bool) :
    ((emit (axisSchedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target)).remaining.filter fun q => Direction.west.lane q ∈
        Finset.range (p.H + 1) \ thirdRowKeep l p) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro q hq
  obtain ⟨hq, hline⟩ := Finset.mem_filter.mp hq
  exact (Finset.mem_sdiff.mp hline).2 (target_third_rows_supported l p hl hM target hq)

/-- The literal first eighteen blocks of the complete target schedule. -/
def thirdRowSchedule (l : PortLayout) (p : Scales.Parameters) (k : ℕ) : List Template :=
  axisSchedule l p k ++ [.clear .west (Finset.range (p.H + 1) \ thirdRowKeep l p)]

/-- Every clear in the first eighteen actual target blocks deletes zero holes. -/
theorem thirdRows_discarded_zero (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (target : List Bool) :
    (emit (thirdRowSchedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target)).discarded = 0 := by
  rw [thirdRowSchedule, emit_discarded_append, axisSchedule_discarded_zero l p hl hM ha target, Nat.zero_add]
  simp only [emit, Nat.add_zero]
  rw [target_third_row_clear_empty l p hl hM target, Finset.card_empty]

end PushPuzzle.Push.AcceptanceProgram
