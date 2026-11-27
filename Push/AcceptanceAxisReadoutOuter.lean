/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceAxisReadout
public import Push.AcceptanceSoundnessSupportResidual
public import Push.AcceptanceSoundnessSupportCoordinates
public import Push.AcceptanceProgramColumns
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceSoundnessSupportClean

/-! The actual first row clear fixes every genuine endpoint's terminal outer rod at the frame. -/

public section
namespace PushPuzzle.Push.AcceptanceAxisReadout

open PushFS PushS PushS.PortLayout AcceptanceProgram AcceptanceSoundness

private theorem neighbor_not_firstRowKeep (l : PortLayout) (p : Scales.Parameters)
    (q : Cell (p.W + 1) (p.H + 1)) (hy : q.2.val = 1 ∨ q.2.val + 1 = p.H) :
    q.2.val ∉ firstRowKeep l p := by
  have hH : p.H = 2 * p.D := rfl
  have hD := p.outer_distance
  have hHeven : p.H % 2 = 0 := by simp [Scales.Parameters.H]
  have hDeven : p.D % 2 = 0 := by
    simp [Scales.Parameters.D, Scales.Parameters.A, Scales.Parameters.Q, Nat.mul_mod]
  have hodd : q.2.val % 2 = 1 := by omega
  intro hq
  simp only [firstRowKeep, keepRows, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with ((hw | hc) | hm) | hn
  · have heven := l.workingRowSet_even p ((working_rows_iff l p q.2).mp hw)
    omega
  · have heven := cut_rows_even p hc
    omega
  · rcases hm with hm | hm | hm | hm <;> omega
  · obtain ⟨k, hk, hn⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hn)
    have hkm := List.mem_range.mp hk
    have hY := p.Y_ge (k + 1)
    have hmargin := readDepth_add_lt_D p (k + 1)
    rw [readDepth_eq p (by omega) (by omega)] at hmargin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with hn | hn | hn | hn <;> omega

/-- No accepted actual source endpoint has a hole adjacent to its frame on any original main axis. -/
theorem canonical_main_frame_neighbor_empty (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (initial target : List Bool) {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    {i : ℕ} (hi : i < l.portCount) (q : Cell (p.W + 1) (p.H + 1))
    (hx : q.1.val = p.x i) (hy : q.2.val = 1 ∨ q.2.val + 1 = p.H) : q ∉ holes t := by
  let T := targetHoles l p target
  let stages := schedule l p (T \ Boundary.frame).card
  have hs : holes (l.canonicalInstance p hl hM haxes initial target).initial = targetHoles l p initial :=
    l.physicalInstance_initial_holes p hl hM haxes (l.canonical initial) (l.canonical target)
  have hc := (program_clean_execution l p hl hM haxes initial target hr hs ha).2
  change Scan.ClearsEmpty (instructions (emit stages T).rounds) (holes t) at hc
  have hx0 := readLength_add_lt_x p i 0
  have hxW := x_add_readLength_lt_W p (hi.trans_le haxes) 0
  have hD := p.outer_distance
  have hH : p.H = 2 * p.D := rfl
  have haxis : p.x i ∈ axes l p := List.mem_toFinset.mpr (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
  have haux : p.x i ∉ auxiliaries l p :=
    fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_union_left _ haxis)
  have htrim (side : Side) : ¬ReadTouches (trimRound l p side) q := by
    cases side <;> intro ht
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
  intro hq
  have hq5 := clean_unread_survives (stages.take 5) T (holes t) (roundResidual stages T (holes t) 5)
    (roundResidual_clean stages T (holes t) 5 hc) (roundResidual_eval stages T (holes t) 5 hc) hq hunread
  have hstage : stages[5]? = some (.clear .west (Finset.range (p.H + 1) \ firstRowKeep l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, firstRowKeep, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hkeep := (roundResidual_clear_keeps stages T (holes t) 5 hc hstage hq5).2
  apply hkeep
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr q.2.isLt, neighbor_not_firstRowKeep l p q hy⟩

/-- Every genuine terminal endpoint word starts its outer rod at the frame in an accepted real source computation. -/
theorem canonical_endpoint_shift_zero (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (initial target : List Bool) {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    {e : Endpoint} (he : e ∈ l.endpoints) {parameter shift : ℕ}
    (word : EndpointAxisReadout p e t parameter shift) : shift = 0 := by
  have hp := (l.endpoints_port_lt hl he).trans_le haxes
  have hxW := x_add_readLength_lt_W p hp 0
  have hD := readDepth_add_lt_D p e.level
  have hH : p.H = 2 * p.D := rfl
  let q : Cell (p.W + 1) (p.H + 1) :=
    (⟨p.x e.port, by omega⟩, ⟨if e.side = .upper then 1 else p.H - 1, by split <;> omega⟩)
  have hd : (if e.side = .upper then q.2.val else p.H - q.2.val) = 1 := by
    dsimp only [q]
    split_ifs <;> omega
  have hq := canonical_main_frame_neighbor_empty l p hl hM haxes initial target hr ha
    (l.endpoints_port_lt hl he) q rfl (by dsimp only [q]; split <;> omega)
  by_contra hn
  apply hq
  apply (word.axis_holes q rfl (by rw [hd]; omega)).mpr
  exact Or.inl (by rw [hd]; omega)

end PushPuzzle.Push.AcceptanceAxisReadout
