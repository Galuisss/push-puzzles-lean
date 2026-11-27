/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupportDepthStock
public import Push.AcceptanceProgramHalfStock
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgram
import all PushS.PortLayoutCoordinates

/-! The actual private read must pass the first available half-depth hole before paying any positive quota. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS AcceptanceProgram

/-- Retaining the first available real hole on a selected column forces its reference front quota to be zero. -/
private theorem south_round_retained_front_zero {w h : ℕ} (cols : Finset ℕ) (span : ℕ → ℕ)
    (T E F : Finset (Cell w h)) {a : Cell w h} (hx : a.1.val ∈ cols)
    (he : Scan.eval (instructions (emit [.read .south (prefixRequests cols span)] T).rounds) E = some F)
    (ha : a ∈ F) (hmin : ∀ b ∈ E, b.1.val = a.1.val → prefixRank .south a ≤ prefixRank .south b) :
    (T.filter fun b => b.1.val = a.1.val ∧ prefixRank .south b < span a.1.val).card = 0 := by
  have heq : E.filter (fun b => b.1.val = a.1.val) = F.filter (fun b => b.1.val = a.1.val) := by
    apply Finset.Subset.antisymm
    · intro b hb
      obtain ⟨hbE, hbx⟩ := Finset.mem_filter.mp hb
      apply Finset.mem_filter.mpr
      refine ⟨?_, hbx⟩
      by_contra hn
      have hlt := round_deleted_before_retained .south (prefixRequests cols span) T he ha hbE hn hbx.symm
      have hle := hmin b hbE hbx
      omega
    · exact Finset.filter_subset_filter _ (scan_subset he)
  have hloss := south_round_front_loss cols span T E F hx he
  rw [heq] at hloss
  omega

/-- Any private half-depth hole retained by the real private read would force that emitted column's front quota to vanish. -/
private theorem canonical_private_half_retained_front_zero (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 10)
    (hx : q.1.val ∈ privateColumns l p) (hy : q.2.val = p.H - p.Y 1 / 2) :
    (((emit ((schedule l p (targetHoles l p target \ Boundary.frame).card).take 9)
      (targetHoles l p target)).remaining).filter fun b =>
        b.1.val = q.1.val ∧ prefixRank .south b < p.Y 1 + 3).card = 0 := by
  let T := targetHoles l p target
  let E := PushS.holes t
  let stages := schedule l p (T \ Boundary.frame).card
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have hi : stages[9]? = some (privateRound l p) := by
    simp only [stages, schedule, preparation, frameSchedule, privateRound, privateColumns,
      List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have he := (roundResidual_step stages T E 9 hc hi).1
  have hqrank : prefixRank .south q = p.Y 1 / 2 := by
    have hb := PortLayout.readDepth_add_lt_H p 1
    rw [PortLayout.readDepth_eq p le_rfl p.levels_pos] at hb
    simp only [prefixRank, Nat.add_sub_cancel, hy]
    omega
  apply south_round_retained_front_zero (privateColumns l p) (fun _ => p.Y 1 + 3) _ _ _ hx he hq
  intro b hb _
  rw [hqrank]
  exact canonical_private_input_depth l p hl hM haxes initial target hr ha hb

/-- The actual positive private read has already consumed every half-depth hole on its columns. -/
private theorem canonical_private_half_consumed (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val ∈ privateColumns l p)
    (hy : q.2.val = p.H - p.Y 1 / 2) :
    q ∉ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 10 := by
  intro hq
  have hz := canonical_private_half_retained_front_zero l p hl hM haxes initial target hr ha hq hx hy
  have href := half_before_private l p hl hM haxes target hy (Finset.mem_union_right _ hx)
  have hfront : prefixRank .south q < p.Y 1 + 3 := by
    simp only [prefixRank, Nat.add_sub_cancel, hy]
    omega
  have hempty := Finset.card_eq_zero.mp hz
  apply Finset.notMem_empty q
  rw [← hempty]
  exact Finset.mem_filter.mpr ⟨href, rfl, hfront⟩

/-- The real half-row quota can be paid only by the gate-core markers left after the private cap read. -/
theorem canonical_half_input_core_stock (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 26) (hy : q.2.val = p.H - p.Y 1 / 2) : q.1.val ∈ cores l p := by
  rcases Finset.mem_union.mp (canonical_half_input_stock l p hl hM haxes initial target hr ha hq hy) with hcore | hprivate
  · exact hcore
  · have hc := (program_clean_execution l p hl hM haxes initial target hr
      (canonical_initial_holes l p hl hM haxes initial target) ha).2
    exact False.elim (canonical_private_half_consumed l p hl hM haxes initial target hr ha hprivate hy
      (roundResidual_antitone _ _ _ hc (by omega : 10 ≤ 26) hq))

end PushPuzzle.Push.AcceptanceSoundness
