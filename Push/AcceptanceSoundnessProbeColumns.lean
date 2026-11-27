/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessMainResidual
import all Push.AcceptanceSoundnessSupportLanes
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgram

/-! The actual probe-row block partitions each principal-column inventory before its final axis read. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

/-- A clean compact clear has identical physical input and output inventories. -/
private theorem roundResidual_clear_eq {w h : ℕ} (stages : List Template) (T E : Finset (Cell w h))
    (n : ℕ)
    (hc : Scan.ClearsEmpty (instructions (emit stages T).rounds) E)
    {side : Direction} {lanes : Finset ℕ} (hi : stages[n]? = some (.clear side lanes)) :
    roundResidual stages T E (n + 1) = roundResidual stages T E n :=
  Finset.Subset.antisymm (roundResidual_succ_subset stages T E n hc)
    (fun _ h => (roundResidual_clear_keeps stages T E n hc hi h).1)

/-- The actual pre-probe inventory on one physical principal column and all selected probe rows. -/
def probeColumnStock (l : PortLayout) (p : Scales.Parameters) (target : List Bool)
    (E : Finset (Cell (p.W + 1) (p.H + 1))) (port : ℕ) : Finset (Cell (p.W + 1) (p.H + 1)) :=
  (roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
    (targetHoles l p target) E 13).filter fun q => q.1.val = p.x port ∧ q.2.val ∈ probeRows l p

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)

local notation "I" => l.canonicalInstance p hl hM haxes initial target

/-- The true probe-row read removes precisely all of its input holes on the selected rows. -/
private theorem canonical_probe_read_stock {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 14 =
      (roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target) (PushS.holes t) 13).filter fun q => q.2.val ∉ probeRows l p := by
  let T := targetHoles l p target
  let E := PushS.holes t
  let stages := schedule l p (T \ Boundary.frame).card
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have i13 : stages[13]? = some (readRows p .west (probeRows l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have i14 : stages[14]? = some (.clear .east (probeRows l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  apply Finset.Subset.antisymm
  · intro q hq
    exact Finset.mem_filter.mpr ⟨roundResidual_succ_subset stages T E 13 hc hq,
      (roundResidual_clear_keeps stages T E 14 hc i14 hq).2⟩
  · intro q hq
    obtain ⟨hq, hy⟩ := Finset.mem_filter.mp hq
    exact roundResidual_unread_keeps stages T E 13 hc i13 hq
      (fun ht => hy (row_touches p .west _ (Or.inl rfl) ht))

/-- Every principal column splits exactly into its actual paid probe stock and the stock passed to the axis read. -/
theorem canonical_probe_column_card (port : ℕ) {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    ((roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 15).filter fun q => q.1.val = p.x port).card +
      (probeColumnStock l p target (PushS.holes t) port).card =
      ((roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target) (PushS.holes t) 13).filter fun q => q.1.val = p.x port).card := by
  let T := targetHoles l p target
  let E := PushS.holes t
  let stages := schedule l p (T \ Boundary.frame).card
  let C := (roundResidual stages T E 13).filter fun q => q.1.val = p.x port
  let P := probeColumnStock l p target E port
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have i14 : stages[14]? = some (.clear .east (probeRows l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have he : (roundResidual stages T E 15).filter (fun q => q.1.val = p.x port) = C \ P := by
    rw [roundResidual_clear_eq stages T E 14 hc i14, canonical_probe_read_stock l p hl hM haxes initial target hr ha]
    ext q
    simp only [C, P, probeColumnStock, Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨h, hn⟩, hx⟩
      exact ⟨⟨h, hx⟩, fun hb => hn hb.2.2⟩
    · rintro ⟨⟨h, hx⟩, hn⟩
      exact ⟨⟨h, fun hb => hn ⟨h, hx, hb⟩⟩, hx⟩
  have hsub : P ⊆ C := by
    intro q hq
    obtain ⟨hq, hx, _⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨hq, hx⟩
  change ((roundResidual stages T E 15).filter fun q => q.1.val = p.x port).card + P.card = C.card
  rw [he]
  exact Finset.card_sdiff_add_card_eq_card hsub

/-- Zero-loss ordinary-axis clearing forces the preceding real axis read to exhaust each selected ordinary column. -/
theorem canonical_ordinary_axis_read_output_empty {port : ℕ} (hp : p.x port ∈ axes l p \ cores l p)
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    ((roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 16).filter fun q => q.1.val = p.x port) = ∅ := by
  let T := targetHoles l p target
  let E := PushS.holes t
  let stages := schedule l p (T \ Boundary.frame).card
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have i16 : stages[16]? = some (.clear .north (axes l p \ cores l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  apply Finset.eq_empty_of_forall_notMem
  intro q hq
  obtain ⟨hq, hx⟩ := Finset.mem_filter.mp hq
  have hkeep := (roundResidual_clear_keeps stages T E 16 hc i16 hq).2
  change q.1.val ∉ axes l p \ cores l p at hkeep
  exact hkeep (hx ▸ hp)

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
