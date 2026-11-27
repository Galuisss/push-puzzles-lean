/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicTwoRoundCompletenessDock
public import Push.CyclicTwoRoundSoundness
import all Push.CyclicInventory
import all Push.Scan
import all Push.CyclicTwoRoundSoundness

/-! Concrete completeness of the two-round cyclic reader. -/

public section
namespace PushPuzzle.Push.Cyclic

open PushFS PushS

private theorem eval_append {w h : ℕ} (a b : List (Scan.Instruction w h)) (E : Finset (Cell w h)) :
    Scan.eval (a ++ b) E = (Scan.eval a E).bind (Scan.eval b) := by
  induction a generalizing E with
  | nil => rfl
  | cons i a ih => simp only [List.cons_append, Scan.eval, ih, Option.bind_assoc]

private theorem lines_payable {w h : ℕ} (side : Direction) {requests : List (ℕ × ℕ)}
    {E F : Finset (Cell w h)} (heval : Scan.eval (Scan.lines side requests) E = some F)
    {a : ℕ × ℕ} (ha : a ∈ requests) : a.2 ≤ (E.filter fun q => side.lane q = a.1).card := by
  induction requests generalizing E with
  | nil => simp only [List.not_mem_nil] at ha
  | cons b rest ih =>
    simp only [Scan.lines, List.map_cons, Scan.eval, Option.bind_eq_some_iff] at heval
    obtain ⟨G, hread, hrest⟩ := heval
    rcases List.mem_cons.mp ha with rfl | ha
    · exact (Scan.Instruction.read_accepts_iff side a.1 a.2 E).mp ⟨G, hread⟩
    · exact (ih hrest ha).trans (Finset.card_le_card (Finset.filter_subset_filter _
        (Scan.Instruction.eval_subset hread)))

private theorem source_row_le (r : ColumnScan.Input) (E : Finset (Cell r.width r.height))
    (t : State (nextSource r).width (nextSource r).height)
    (hh : ∀ p ∈ E, sourceEmbed r p ∈ holes t) (i : Fin r.height) :
    (E.filter fun p => p.2 = i).card ≤ ((holes t).filter fun q => q.1.val = i.val).card := by
  have hsub : ((E.filter fun p => p.2 = i).image (sourceEmbed r)) ⊆
      (holes t).filter (fun q => q.1.val = i.val) := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hp, hpi⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨hh p hp, (sourceEmbed_x r p).trans (congrArg Fin.val hpi)⟩
  have hc := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injective _ (sourceEmbed_injective r)] at hc

private theorem reserve_column_le (r : ColumnScan.Input)
    (t : State (nextSource r).width (nextSource r).height)
    (hh : ∀ q : Fin (r.width + 2) × Fin ((wideReader r).outputHeight - r.height),
      reserveEmbed r q ∈ holes t) (i : ℕ) (hlo : r.height ≤ i) (hhi : i < (wideReader r).outputHeight) :
    r.width + 2 ≤ ((holes t).filter fun q => q.1.val = i).card := by
  let level : Fin ((wideReader r).outputHeight - r.height) := ⟨i - r.height, by omega⟩
  let f : Fin (r.width + 2) → Cell (nextSource r).width (nextSource r).height :=
    fun j => reserveEmbed r (j, level)
  have hinj : Function.Injective f := fun a b he => congrArg Prod.fst (reserveEmbed_injective r he)
  have hsub : (Finset.univ.image f) ⊆ (holes t).filter (fun q => q.1.val = i) := by
    intro q hq
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hq
    apply Finset.mem_filter.mpr ⟨hh _, ?_⟩
    change r.height + (i - r.height) = i
    omega
  have hc := Finset.card_le_card hsub
  simpa only [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] using hc

private theorem nextQuotas_getD (r : ColumnScan.Input) (rows : List ℕ)
    (hlen : rows.length = r.height) (i : ℕ) :
    (nextQuotas r rows).getD i 0 = if i < r.height then rows.getD i 0
      else if i < (wideReader r).outputHeight then r.width + 2 else 0 := by
  have hh : r.height ≤ (wideReader r).outputHeight := by
    change r.height ≤ r.height + (wideReader r).length
    omega
  rw [nextQuotas, List.append_assoc]
  split_ifs with hlo hhi
  · exact List.getD_append _ _ _ _ (by rwa [hlen])
  · rw [List.getD_append_right _ _ _ _ (by omega), hlen,
      List.getD_append _ _ _ _ (by simp only [List.length_replicate]; omega)]
    exact List.getD_replicate _ (by omega)
  · rw [List.getD_append_right _ _ _ _ (by omega), hlen,
      List.getD_append_right _ _ _ _ (by simp only [List.length_replicate]; omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_getD_replicate_default_eq]

/-- A single actual source corner computation accepted by both static rounds solves the literal two-stage reader. -/
theorem twoRound_complete (r : ColumnScan.Input) (rows : List ℕ)
    (hlen : rows.length = r.height) (hb : rows.sum ≤ r.sourceHoles)
    {s : State r.width r.height} (hr : Reachable r.sourceBoard none r.initial.toState s)
    (hcorner : s.player = r.sourceCorner) (haccept : Scan.Accepts (twoRoundProgram r rows) (holes s)) :
    (nextInput r rows hlen hb).compile.Solvable := by
  obtain ⟨F, hF⟩ := haccept
  change Scan.eval (Scan.columns (Scan.ofQuotas r.quotas) ++ Scan.lines .west (Scan.ofQuotas rows))
    (holes s) = some F at hF
  rw [eval_append, Option.bind_eq_some_iff] at hF
  obtain ⟨E, hE, hrows⟩ := hF
  obtain ⟨t, ht, htp, hsource, hreserve⟩ := first_round_ready r hr hcorner hE
  apply (nextInput r rows hlen hb).compile_solvable_of_source_corner_quotas
    (s := t) (by rw [nextInput_initial]; exact ht.reboard rfl)
    (htp.trans (nextInput_corner r rows hlen hb).symm)
  intro i
  let lane : Fin (nextSource r).width := i
  change (nextQuotas r rows).getD i.val 0 ≤ ((holes t).filter fun q => q.1 = lane).card
  rw [nextQuotas_getD r rows hlen]
  simp only [Fin.ext_iff]
  dsimp only [lane]
  split_ifs with hlo hhi
  · let j : Fin rows.length := ⟨i.val, by rwa [hlen]⟩
    have hq := lines_payable .west hrows (Scan.ofQuotas_mem rows j)
    have hindex : rows.getD i.val 0 = rows[j] := by
      simpa only [Fin.getElem_fin] using List.getD_eq_getElem rows 0 j.isLt
    rw [hindex]
    have hs := source_row_le r E t hsource (⟨i.val, hlo⟩ : Fin r.height)
    have hf : E.filter (fun p => p.2 = (⟨i.val, hlo⟩ : Fin r.height)) =
        E.filter (fun p => Direction.west.lane p = j.val) := by
      ext p
      simp only [Finset.mem_filter, Direction.lane, Fin.ext_iff, j]
      constructor
      · intro hp; exact Finset.mem_filter.mpr hp
      · intro hp; exact Finset.mem_filter.mp hp
    rw [hf] at hs
    exact hq.trans hs
  · exact reserve_column_le r t hreserve i.val (by omega) hhi
  · exact Nat.zero_le _

end PushPuzzle.Push.Cyclic
