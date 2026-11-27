/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupportPrivateStock
public import Push.AcceptanceProgramPrivateStockFour
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgram

/-! The real four-hole private read saturates all four physical private positions. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS AcceptanceProgram

/-- The actual private read deletes exactly its four canonical physical slots on each selected private column. -/
private theorem canonical_private_read_slots (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (x : Fin (p.W + 1)) (hx : x.val ∈ privateColumns l p) :
    privateSlots p x =
      ((roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target) (PushS.holes t) 9).filter fun q => q.1.val = x.val) \
      ((roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target) (PushS.holes t) 10).filter fun q => q.1.val = x.val) := by
  let T := targetHoles l p target
  let E := PushS.holes t
  let stages := schedule l p (T \ Boundary.frame).card
  let A := roundResidual stages T E 9
  let F := roundResidual stages T E 10
  let paid := A.filter (fun q => q.1.val = x.val) \ F.filter (fun q => q.1.val = x.val)
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have hi : stages[9]? = some (privateRound l p) := by
    simp only [stages, schedule, preparation, frameSchedule, privateRound, privateColumns,
      List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have he := (roundResidual_step stages T E 9 hc hi).1
  have hsubset : paid ⊆ privateSlots p x := by
    intro q hq
    obtain ⟨hqA, hqF⟩ := Finset.mem_sdiff.mp hq
    obtain ⟨hqA, hqx⟩ := Finset.mem_filter.mp hqA
    have hqF' : q ∉ F := fun h => hqF (Finset.mem_filter.mpr ⟨h, hqx⟩)
    have hslot := canonical_private_payment_slot l p hl hM haxes initial target hr ha (hqx ▸ hx) hqA hqF'
    simpa only [Fin.ext hqx] using hslot
  have hloss := south_round_front_loss (privateColumns l p) (fun _ => p.Y 1 + 3)
    (emit (stages.take 9) T).remaining A F hx he
  have hfront := private_front_card_ge_four l p hl hM haxes target x.val hx
  have hcard := Finset.card_sdiff_add_card_eq_card
    (Finset.filter_subset_filter (fun q => q.1.val = x.val) (scan_subset he))
  have hslots := privateSlots_card_le_four p x
  have hpaid : 4 ≤ paid.card := by
    dsimp only [paid, A, F, stages, T, E] at hcard hloss ⊢
    simp only [Nat.reduceAdd] at hcard hloss
    omega
  exact (Finset.eq_of_subset_of_card_le hsubset (hslots.trans hpaid)).symm

/-- All four actual private positions, including the private half-depth marker, are terminal holes. -/
theorem canonical_private_slot_terminal (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val ∈ privateColumns l p)
    (hy : pageDepth p .lower q ∈ privateDepths p) : q ∈ PushS.holes t := by
  have hslot : q ∈ privateSlots p q.1 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, hy⟩
  rw [canonical_private_read_slots l p hl hM haxes initial target hr ha q.1 hx] at hslot
  have hq9 := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hslot).1).1
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  exact scan_subset (roundResidual_eval _ _ _ 9 hc) hq9

end PushPuzzle.Push.AcceptanceSoundness
