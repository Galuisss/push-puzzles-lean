/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessCentral
public import Push.AcceptanceProgramComplete
import all Push.Scan
import all Push.AcceptanceProgramPrefix

/-! Actual read attribution and retained-hole barriers in an accepted destructive scan. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS AcceptanceProgram

/-- Actual canonical reachability supplies full payment and zero deletion by every clear. -/
theorem program_clean_execution (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {B : Board (p.W + 1) (p.H + 1)} {cap : Option ℕ} {s t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable B cap s t) (hs : PushS.holes s = targetHoles l p initial)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    Scan.eval (instructions (program l p target).rounds) (PushS.holes t) = some ∅ ∧
      Scan.ClearsEmpty (instructions (program l p target).rounds) (PushS.holes t) := by
  obtain ⟨F, hF⟩ := ha
  have hquota := program_source_quota l p hl hM haxes initial target
  have hcard := PushS.card_holes_reachable hr
  rw [hs] at hcard
  have hpaid : Scan.quota (instructions (w := p.W + 1) (h := p.H + 1) (program l p target).rounds) =
      (PushS.holes t).card := hquota.trans hcard.symm
  obtain ⟨rfl, hclear⟩ := Scan.full_quota hF hpaid
  exact ⟨hF, hclear⟩

private theorem consume_ordered {α : Type*} [DecidableEq α] (key : α → ℕ)
    {cells : List α} (horder : cells.Pairwise (fun a b => key a < key b)) {quota : ℕ} {E F : Finset α}
    (he : Scan.consume cells quota E = some F) {a b : α} (ha : a ∈ F) (hac : a ∈ cells)
    (hb : b ∈ E) (hbc : b ∈ cells) (hbf : b ∉ F) : key b < key a := by
  induction cells generalizing quota E with
  | nil => exact (List.not_mem_nil hac).elim
  | cons c rest ih =>
    cases quota with
    | zero => exact (hbf ((Option.some.inj he) ▸ hb)).elim
    | succ quota =>
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp horder
      by_cases hc : c ∈ E
      · simp only [Scan.consume, ite_eq_left hc] at he
        have hsub := Scan.consume_subset he
        have hac' : a ∈ rest := (List.mem_cons.mp hac).resolve_left (by
          intro heq
          subst a
          exact (Finset.mem_erase.mp (hsub ha)).1 rfl)
        rcases List.mem_cons.mp hbc with rfl | hbc
        · exact hhead a hac'
        · by_cases hcb : b = c
          · subst b
            exact hhead a hac'
          · exact ih htail he hac' (Finset.mem_erase.mpr ⟨hcb, hb⟩) hbc
      · simp only [Scan.consume, ite_eq_right hc] at he
        have hsub := Scan.consume_subset he
        have hac' : a ∈ rest := (List.mem_cons.mp hac).resolve_left (by intro heq; exact hc (heq ▸ hsub ha))
        have hbc' : b ∈ rest := (List.mem_cons.mp hbc).resolve_left (by intro heq; exact hc (heq ▸ hb))
        exact ih htail he hac' hb hbc'

private theorem line_rank_order {w h : ℕ} (side : Direction) (lane : ℕ) :
    (Scan.lineCells (w := w) (h := h) side lane).Pairwise (fun a b => prefixRank side a < prefixRank side b) := by
  cases side <;> simp only [Scan.lineCells]
  all_goals
    split
    next hbound =>
      apply List.pairwise_iff_get.mpr
      intro i j hij
      simp only [List.get_eq_getElem, List.getElem_reverse, List.getElem_ofFn, prefixRank]
      have hij' : i.val < j.val := hij
      have hi := i.isLt
      have hj := j.isLt
      simp only [List.length_reverse, List.length_ofFn] at hi hj
      first | omega | (simp only [List.length_ofFn]; omega)
    next hbound => exact List.Pairwise.nil

/-- A retained hole on a read line bounds every hole actually paid by that read. -/
theorem read_deleted_before_retained {w h : ℕ} {side : Direction} {lane quota : ℕ}
    {E F : Finset (Cell w h)} (he : (Scan.Instruction.read side lane quota).eval E = some F)
    {a b : Cell w h} (ha : a ∈ F) (haline : side.lane a = lane) (hb : b ∈ E) (hbf : b ∉ F) :
    prefixRank side b < prefixRank side a := by
  have hbline : side.lane b = lane := by
    by_contra hn
    exact hbf ((Scan.Instruction.read_outside he hn).mpr hb)
  exact consume_ordered (prefixRank side) (line_rank_order side lane) he ha
    ((Scan.mem_lineCells side lane a).mpr haline) hb ((Scan.mem_lineCells side lane b).mpr hbline) hbf

end PushPuzzle.Push.AcceptanceSoundness
