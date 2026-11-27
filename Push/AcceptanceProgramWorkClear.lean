/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramThirdClear
public import Push.AcceptanceProgramCut
import all Push.AcceptanceProgramThirdClear
import all Push.AcceptanceProgramLayout

/-! Reading the remaining working rows leaves only the actual half-depth, interlevel and cut markers. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS PushS.PortLayout

/-- Six actual blocks between the third row clear and the non-street column clear. -/
def workTail (l : PortLayout) (p : Scales.Parameters) : List Template :=
  [.read .north (prefixRequests (cores l p) fun _ => p.H - p.Y 1 + 1),
    readColumns p .south (guards l p), .clear .north (guards l p),
    .read .south (prefixRequests (samples l p) fun _ => p.D - 4), readRows p .east {p.D + 4},
    readRows p .west (workRows l p \ ({0, p.H} ∪ probeRows l p))]

/-- Twenty-four actual blocks, through the complete remaining working-row read. -/
def workReadSchedule (l : PortLayout) (p : Scales.Parameters) (k : ℕ) : List Template :=
  thirdRowSchedule l p k ++ workTail l p

/-- The guard-column read pays for the only clear among these six blocks, on every stock. -/
private theorem workTail_discarded_zero (l : PortLayout) (p : Scales.Parameters)
    (E : Finset (Cell (p.W + 1) (p.H + 1))) : (emit (workTail l p) E).discarded = 0 := by
  have hguard := clear_columns_after_read p
    [.read .north (prefixRequests (cores l p) fun _ => p.H - p.Y 1 + 1), readColumns p .south (guards l p)]
    E (guards l p) .south .north (Or.inr rfl) (Or.inl rfl) (.tail _ (.head _))
  simp only [workTail, readColumns, readRows, emit, Nat.add_zero] at hguard ⊢
  rw [hguard, Finset.card_empty]

/-- The first twenty-four actual target blocks have no clear losses. -/
private theorem workRead_discarded_zero (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (target : List Bool) :
    (emit (workReadSchedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target)).discarded = 0 := by
  rw [workReadSchedule, emit_discarded_append, thirdRows_discarded_zero l p hl hM ha target,
    workTail_discarded_zero, Nat.zero_add]

private theorem work_has_axis {l : PortLayout} {p : Scales.Parameters} {k : ℕ} {stage : Template}
    (hs : stage ∈ axisSchedule l p k) : stage ∈ workReadSchedule l p k := by
  rw [workReadSchedule, thirdRowSchedule]
  exact List.mem_append_left _ (List.mem_append_left _ hs)

private theorem work_axis_remaining {l : PortLayout} {p : Scales.Parameters} {k : ℕ}
    {E : Finset (Cell (p.W + 1) (p.H + 1))} {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ (emit (workReadSchedule l p k) E).remaining) : q ∈ (emit (axisSchedule l p k) E).remaining := by
  rw [workReadSchedule, emit_remaining_append] at hq
  have hq := emit_remaining_subset _ _ hq
  rw [thirdRowSchedule, emit_remaining_append] at hq
  exact emit_remaining_subset _ _ hq

/-- No working-row hole survives the full actual working-row read. -/
private theorem workRead_no_work (l : PortLayout) (p : Scales.Parameters) (target : List Bool)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ (emit (workReadSchedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target)).remaining) : q.2.val ∉ workRows l p := by
  intro hwork
  have haxis := work_axis_remaining hq
  have hf := (Finset.mem_sdiff.mp (axis_remaining_source l p target haxis)).2
  by_cases hrow : q.2.val ∈ ({0, p.H} : Finset ℕ)
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hrow
    apply hf
    apply (Boundary.mem_frame q).mpr
    rcases hrow with he | he
    · exact ⟨.north, by simpa only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and] using he⟩
    · exact ⟨.south, by simpa only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and] using congrArg (fun n => n + 1) he⟩
  by_cases hprobe : q.2.val ∈ probeRows l p
  · have hs : readRows p .west (probeRows l p) ∈ axisSchedule l p (targetHoles l p target \ Boundary.frame).card := by
      apply List.mem_append_right
      unfold axisTail
      exact .head _
    exact emit_stage_excluded (work_has_axis hs) hq ((readRows_region p .west _ (Or.inl rfl) q).mpr hprobe)
  · have hs : readRows p .west (workRows l p \ ({0, p.H} ∪ probeRows l p)) ∈
        workReadSchedule l p (targetHoles l p target \ Boundary.frame).card := by
      apply List.mem_append_right
      unfold workTail
      exact .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))
    apply emit_stage_excluded hs hq
    apply (readRows_region p .west _ (Or.inl rfl) q).mpr
    exact Finset.mem_sdiff.mpr ⟨hwork, fun hh => (Finset.mem_union.mp hh).elim hrow hprobe⟩

/-- Exact remaining marker types after all working rows have been consumed. -/
inductive WorkStock (l : PortLayout) (p : Scales.Parameters) (q : Cell (p.W + 1) (p.H + 1)) : Prop
  | interlevel (side : Side) (marker : InterlevelMarker l p side q)
  | half (row : q.2.val = p.H - p.Y 1 / 2) (column : q.1.val ∈ cores l p ∪ privateColumns l p)
  | cut (row : q.2.val = p.D) (column : q.1.val ∈ auxiliaries l p)

/-- The actual emitted target residual now consists only of its three kinds of owned marker. -/
theorem workRead_inventory (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (target : List Bool)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ (emit (workReadSchedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target)).remaining) : WorkStock l p q := by
  have haxis := work_axis_remaining hq
  cases axis_remaining_inventory l p hl hM target haxis with
  | work hw => exact False.elim (workRead_no_work l p target hq hw)
  | interlevel side hm => exact .interlevel side hm
  | half hy hx => exact .half hy hx
  | central hb =>
    have hrows := target_third_rows_supported l p hl hM target haxis
    have hplus : q.2.val ≠ p.D + 4 := by
      intro hy
      have hs : readRows p .east {p.D + 4} ∈
          workReadSchedule l p (targetHoles l p target \ Boundary.frame).card := by
        apply List.mem_append_right
        unfold workTail
        exact .tail _ (.tail _ (.tail _ (.tail _ (.head _))))
      exact emit_stage_excluded hs hq ((readRows_region p .east _ (Or.inr rfl) q).mpr (Finset.mem_singleton.mpr hy))
    have hy : q.2.val = p.D := by
      simp only [thirdRowKeep, Finset.mem_union, Finset.mem_singleton] at hrows
      rcases hrows with (hw | hc) | he
      · exact False.elim (workRead_no_work l p target hq hw)
      · exact cut_rows_central p hc hb
      · exact False.elim (hplus he)
    obtain ⟨hs, hf⟩ := Finset.mem_sdiff.mp (axis_remaining_source l p target haxis)
    exact .cut hy (l.acceptanceOriginalAux_mem p hl hM ha (l.acceptanceCutAux p (l.canonical target) hs hf hy))

private theorem private_column_aux (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) {x : ℕ}
    (hx : x ∈ privateColumns l p) : x ∈ auxiliaries l p := by
  obtain ⟨a, ha', he⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
  exact he ▸ l.acceptancePageColumn_aux p hl hM ha .lower (List.mem_filter.mp ha').1

/-- The actual non-street column clear deletes zero target holes. -/
private theorem target_work_column_clear_empty (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (target : List Bool) :
    ((emit (workReadSchedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target)).remaining.filter fun q => Direction.north.lane q ∈
        Finset.range (p.W + 1) \ (auxiliaries l p ∪ cores l p)) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro q hq
  obtain ⟨hq, hx⟩ := Finset.mem_filter.mp hq
  have hn := (Finset.mem_sdiff.mp hx).2
  change q.1.val ∉ auxiliaries l p ∪ cores l p at hn
  cases workRead_inventory l p hl hM ha target hq with
  | interlevel side hm =>
    obtain ⟨a, ha', _, _, hx, _⟩ := hm
    exact hn (Finset.mem_union_left _ (hx.symm ▸ l.acceptancePageColumn_aux p hl hM ha side ha'))
  | half hy hx =>
    rcases Finset.mem_union.mp hx with hc | hp
    · exact hn (Finset.mem_union_right _ hc)
    · exact hn (Finset.mem_union_left _ (private_column_aux l p hl hM ha hp))
  | cut hy hx => exact hn (Finset.mem_union_left _ hx)

/-- The literal twenty-five blocks before the page-by-page marker checks. -/
def workSchedule (l : PortLayout) (p : Scales.Parameters) (k : ℕ) : List Template :=
  workReadSchedule l p k ++ [.clear .north (Finset.range (p.W + 1) \ (auxiliaries l p ∪ cores l p))]

theorem schedule_take_twentyfive (l : PortLayout) (p : Scales.Parameters) (k : ℕ) :
    (schedule l p k).take 25 = workSchedule l p k := by
  simp only [schedule, preparation, frameSchedule, workSchedule, workReadSchedule, thirdRowSchedule,
    axisSchedule, axisTail, workTail, thirdRowKeep, axisReadRound, List.cons_append, List.nil_append,
    List.take_succ_cons, List.take_zero]

/-- Every clear in the twenty-five actual blocks before the layer checks has zero target loss. -/
theorem work_discarded_zero (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (target : List Bool) :
    (emit (workSchedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target)).discarded = 0 := by
  rw [workSchedule, emit_discarded_append, workRead_discarded_zero l p hl hM ha target, Nat.zero_add]
  simp only [emit, Nat.add_zero]
  rw [target_work_column_clear_empty l p hl hM ha target, Finset.card_empty]

end PushPuzzle.Push.AcceptanceProgram
