/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceAxisReadoutOuter
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceSoundnessSupportClean
import all PushS.PortStreetSeparation
import all PushS.PortSegments

/-! The first actual row clear excludes the depth-plus-three and depth-plus-four rows of every main axis. -/

public section
namespace PushPuzzle.Push.AcceptanceAxisReadout

open PushFS PushS PushS.PortLayout AcceptanceProgram AcceptanceSoundness

private theorem Y_mod (p : Scales.Parameters) (j : ℕ) : p.Y j % 16 = 0 := by
  simp [Scales.Parameters.Y, Scales.Parameters.A, Scales.Parameters.Q, Nat.mul_mod]

private theorem H_mod (p : Scales.Parameters) : p.H % 16 = 0 := by
  simp [Scales.Parameters.H, Scales.Parameters.D, Scales.Parameters.A, Scales.Parameters.Q, Nat.mul_mod]

private theorem work_mod (l : PortLayout) (p : Scales.Parameters) {v : ℕ}
    (hv : v ∈ l.workingDepthCoordinates p) : v % 8 = 0 ∨ v % 8 = 2 ∨ v % 8 = 6 := by
  change v ∈ workingRows l (coordinates p) at hv
  obtain ⟨k, hk, hv⟩ := List.mem_flatMap.mp hv
  have hk := List.mem_range.mp hk
  change k < p.levels at hk
  have hm := Y_mod p (k + 1)
  have hY := p.Y_ge (k + 1)
  change v ∈ (if (centers l).isEmpty then
    [readDepth p (k + 1) - 2, readDepth p (k + 1), readDepth p (k + 1) + 2]
    else [readDepth p (k + 1), readDepth p (k + 1) + 2]) at hv
  rw [readDepth_eq p (by omega) (by omega)] at hv
  split at hv <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hv <;> omega

/-- Neither page retains the last two local tail rows through the first row clear. -/
private theorem depth_tail_not_firstRowKeep (l : PortLayout) (p : Scales.Parameters)
    {j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ p.levels) (side : Side) {offset : ℕ} (hoffset : offset = 3 ∨ offset = 4) :
    (if side = .upper then p.Y j + offset else p.H - (p.Y j + offset)) ∉ firstRowKeep l p := by
  let y := if side = .upper then p.Y j + offset else p.H - (p.Y j + offset)
  have hH := H_mod p
  have hjmod := Y_mod p j
  have hY := p.Y_ge j
  have hD := readDepth_add_lt_D p j
  rw [readDepth_eq p hj hjm] at hD
  have hHH : p.H = 2 * p.D := rfl
  have hymod : y % 8 = 3 ∨ y % 8 = 4 ∨ y % 8 = 5 := by dsimp only [y]; split <;> omega
  have hycentral : y < p.D - 4 ∨ p.D + 4 < y := by dsimp only [y]; split <;> omega
  intro hy
  change y ∈ firstRowKeep l p at hy
  simp only [firstRowKeep, keepRows, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with ((hw | hc) | hm) | hn
  · simp only [workRows, List.mem_toFinset, List.mem_append] at hw
    rcases hw with hw | hw
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      omega
    · obtain ⟨v, hv, he⟩ := List.mem_flatMap.mp hw
      have hm := work_mod l p hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      omega
  · simp only [cutRows, List.mem_toFinset, List.mem_append] at hc
    rcases hc with hc | hc
    · have hm := Y_mod p 1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      omega
    · obtain ⟨k, hk, he⟩ := List.mem_flatMap.mp hc
      have hm := Y_mod p (k + 1)
      have hn := Y_mod p (k + 2)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      omega
  · omega
  · obtain ⟨k, hk, he⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hn)
    have hm := Y_mod p (k + 1)
    have hb := p.Y_ge (k + 1)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    omega

/-- Every accepted terminal main axis is occupied at both depth-plus-three and depth-plus-four rows. -/
theorem canonical_main_depth_tail_occupied (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (initial target : List Bool) {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    {i j : ℕ} (hi : i < l.portCount) (hj : 1 ≤ j) (hjm : j ≤ p.levels)
    (side : Side) {offset : ℕ} (hoffset : offset = 3 ∨ offset = 4)
    (q : Cell (p.W + 1) (p.H + 1))
    (hx : q.1.val = p.x i)
    (hy : q.2.val = if side = .upper then p.Y j + offset else p.H - (p.Y j + offset)) : q ∈ t.boxes := by
  let T := targetHoles l p target
  let stages := schedule l p (T \ Boundary.frame).card
  have hs : holes (l.canonicalInstance p hl hM haxes initial target).initial = targetHoles l p initial :=
    l.physicalInstance_initial_holes p hl hM haxes (l.canonical initial) (l.canonical target)
  have hc := (program_clean_execution l p hl hM haxes initial target hr hs ha).2
  change Scan.ClearsEmpty (instructions (emit stages T).rounds) (holes t) at hc
  have hx0 := readLength_add_lt_x p i 0
  have hxW := x_add_readLength_lt_W p (hi.trans_le haxes) 0
  have hY := p.Y_ge j
  have hD := readDepth_add_lt_D p j
  rw [readDepth_eq p hj hjm] at hD
  have hH : p.H = 2 * p.D := rfl
  have hy0 : 0 < q.2.val ∧ q.2.val < p.H := by split at hy <;> omega
  have haxis : p.x i ∈ axes l p := List.mem_toFinset.mpr (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
  have haux : p.x i ∉ auxiliaries l p :=
    fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_union_left _ haxis)
  have htrim (s : Side) : ¬ReadTouches (trimRound l p s) q := by
    cases s <;> intro ht
    all_goals
      obtain ⟨request, hreq, heq⟩ := ht
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hreq
      have hacol := l.acceptancePageColumn_aux p hl hM haxes _ (List.mem_filter.mp ha).1
      apply haux
      change q.1.val = a.column at heq
      exact (hx.symm.trans heq).symm ▸ hacol
  have hpref : stages.take 5 =
      [.read .south [(0, p.H + 1), (p.W, p.H + 1)],
        .read .west [(0, p.W + 1), (p.H, p.W + 1)],
        .clear .north (sideBands p (T \ Boundary.frame).card), trimRound l p .lower, trimRound l p .upper] := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.take_succ_cons, List.take_zero]
  have hunread : ∀ stage ∈ stages.take 5, ¬ReadTouches stage q := by
    rw [hpref]
    intro stage hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl
    · rintro ⟨request, hr, heq⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> change q.1.val = _ at heq <;> omega
    · rintro ⟨request, hr, heq⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> change q.2.val = _ at heq <;> omega
    · exact fun h => h
    · exact htrim .lower
    · exact htrim .upper
  by_contra hbox
  have hq : q ∈ holes t := by simpa only [mem_holes] using hbox
  have hq5 := clean_unread_survives (stages.take 5) T (holes t) (roundResidual stages T (holes t) 5)
    (roundResidual_clean stages T (holes t) 5 hc) (roundResidual_eval stages T (holes t) 5 hc) hq hunread
  have hstage : stages[5]? = some (.clear .west (Finset.range (p.H + 1) \ firstRowKeep l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, firstRowKeep, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hkeep := (roundResidual_clear_keeps stages T (holes t) 5 hc hstage hq5).2
  apply hkeep
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr q.2.isLt, ?_⟩
  change q.2.val ∉ firstRowKeep l p
  rw [hy]
  exact depth_tail_not_firstRowKeep l p hj hjm side hoffset

/-- The depth-plus-four cell used to exclude terminal train contact is occupied. -/
theorem canonical_main_depth_four_occupied (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (initial target : List Bool) {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    {i j : ℕ} (hi : i < l.portCount) (hj : 1 ≤ j) (hjm : j ≤ p.levels)
    (side : Side) (q : Cell (p.W + 1) (p.H + 1))
    (hx : q.1.val = p.x i)
    (hy : q.2.val = if side = .upper then p.Y j + 4 else p.H - (p.Y j + 4)) : q ∈ t.boxes :=
  canonical_main_depth_tail_occupied l p hl hM haxes initial target hr ha hi hj hjm side (Or.inr rfl) q hx hy

end PushPuzzle.Push.AcceptanceAxisReadout
