/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupportCutPayment
public import Push.ScanColumns
import all Push.AcceptanceSoundnessSupportRounds
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceProgramRounds
import all Push.AcceptanceProgramRegions
import all Push.AcceptanceProgramLayout
import all Push.Scan
import all Push.ScanColumns

/-! A real one-hole finishing payment at the central marker certifies that its lower column was already empty. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS AcceptanceProgram

private theorem prefix_region_iff {w h : ℕ} (side : Direction) (lanes : Finset ℕ) (span : ℕ → ℕ) (q : Cell w h) :
    q ∈ readRegion side (prefixRequests lanes span) ↔ side.lane q ∈ lanes ∧ prefixRank side q < span (side.lane q) := by
  rw [mem_readRegion]
  constructor
  · rintro ⟨a, ha, hx, hy⟩
    obtain ⟨hlane, hspan⟩ := (mem_prefixRequests _ _ _ _).mp ha
    rw [hx]
    exact ⟨hlane, by simpa only [hspan] using hy⟩
  · rintro ⟨hx, hy⟩
    exact ⟨(side.lane q, span (side.lane q)), (mem_prefixRequests _ _ _ _).mpr ⟨hx, rfl⟩, rfl, hy⟩

/-- The actual same-direction read loses exactly the canonical front inventory on each selected column. -/
theorem south_round_front_loss {w h : ℕ} (lanes : Finset ℕ) (span : ℕ → ℕ)
    (T E F : Finset (Cell w h)) {x : ℕ} (hx : x ∈ lanes)
    (he : Scan.eval (instructions (emit [.read .south (prefixRequests lanes span)] T).rounds) E = some F) :
    (F.filter fun q => q.1.val = x).card +
      (T.filter fun q => q.1.val = x ∧ prefixRank .south q < span x).card =
        (E.filter fun q => q.1.val = x).card := by
  let requests := prefixRequests lanes span
  let quotas := (emitReads .south requests T).quotas
  let R := (emitReads .south requests T).remaining
  have hn : (quotas.map Prod.fst).Nodup := by
    rw [show quotas.map Prod.fst = requests.map Prod.fst from emitted_lanes .south requests T]
    simp only [requests, prefixRequests, List.map_map, Function.comp_def]
    simp
  have hxq : x ∈ quotas.map Prod.fst := by
    rw [show quotas.map Prod.fst = requests.map Prod.fst from emitted_lanes .south requests T]
    simp only [requests, prefixRequests, List.map_map, Function.comp_def]
    simpa using hx
  obtain ⟨a, ha, hax⟩ := List.mem_map.mp hxq
  have hactual : Scan.eval (Scan.columns quotas) E = some F := by
    simpa only [emit, instructions, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      Round.instructions, Scan.columns, Scan.lines] using he
  have htarget : Scan.eval (Scan.columns quotas) T = some R := emitReads_eval .south requests T
  have hA := Scan.columns_card hn hactual ha
  have hT := Scan.columns_card hn htarget ha
  have hR : R.filter (fun q => q.1.val = x) =
      (T.filter fun q => q.1.val = x).filter fun q => ¬prefixRank .south q < span x := by
    dsimp only [R]
    rw [emitReads_remaining]
    ext q
    simp only [Finset.mem_filter, Finset.mem_sdiff, prefix_region_iff, requests, Direction.lane]
    by_cases heq : q.1.val = x
    · simp only [heq, hx, true_and, and_true]
    · simp only [heq, and_false, false_and]
  have hfront' : ((T.filter fun q => q.1.val = x).filter fun q => prefixRank .south q < span x).card =
      (T.filter fun q => q.1.val = x ∧ prefixRank .south q < span x).card := by
    rw [Finset.filter_filter]
  have hpart := Finset.card_filter_add_card_filter_not (s := T.filter fun q => q.1.val = x)
    (fun q => prefixRank .south q < span x)
  rw [hfront', ← hR] at hpart
  simp only [hax] at hA hT
  omega

/-- A canonical one-hole front gives the same single-hole loss on the real selected column. -/
private theorem south_round_single_front_loss {w h : ℕ} (lanes : Finset ℕ) (span : ℕ → ℕ)
    (T E F : Finset (Cell w h)) {x : ℕ} (hx : x ∈ lanes)
    (hfront : (T.filter fun q => q.1.val = x ∧ prefixRank .south q < span x).card = 1)
    (he : Scan.eval (instructions (emit [.read .south (prefixRequests lanes span)] T).rounds) E = some F) :
    (F.filter fun q => q.1.val = x).card + 1 = (E.filter fun q => q.1.val = x).card := by
  simpa only [hfront] using south_round_front_loss lanes span T E F hx he

/-- Deleting a real selected-column hole forces a positive reference front inventory. -/
private theorem south_round_front_positive {w h : ℕ} (lanes : Finset ℕ) (span : ℕ → ℕ)
    (T E F : Finset (Cell w h)) {q : Cell w h} (hx : q.1.val ∈ lanes)
    (he : Scan.eval (instructions (emit [.read .south (prefixRequests lanes span)] T).rounds) E = some F)
    (hq : q ∈ E) (hqF : q ∉ F) :
    0 < (T.filter fun r => r.1.val = q.1.val ∧ prefixRank .south r < span q.1.val).card := by
  have hloss := south_round_front_loss lanes span T E F hx he
  have hsub : F.filter (fun r => r.1.val = q.1.val) ⊆ (E.filter fun r => r.1.val = q.1.val).erase q := by
    intro r hr
    have hrf := (Finset.mem_filter.mp hr).1
    apply Finset.mem_erase.mpr
    refine ⟨fun heq => hqF (heq ▸ hrf), ?_⟩
    exact Finset.mem_filter.mpr ⟨scan_subset he hrf, (Finset.mem_filter.mp hr).2⟩
  have hcard := Finset.card_le_card hsub
  have herase := Finset.card_erase_add_one (s := E.filter fun r => r.1.val = q.1.val) (a := q)
    (Finset.mem_filter.mpr ⟨hq, rfl⟩)
  omega

/-- If a real south round deletes one specified hole and loses only one hole on that column,
that hole was already the southernmost input hole, and the output is strictly north of it. -/
private theorem south_round_cut_exhausted {w h : ℕ} (requests : List (ℕ × ℕ)) (T E F : Finset
    (Cell w h))
    (he : Scan.eval (instructions (emit [.read .south requests] T).rounds) E = some F)
    {q : Cell w h} (hq : q ∈ E) (hqF : q ∉ F)
    (hloss : (F.filter fun r => r.1 = q.1).card + 1 = (E.filter fun r => r.1 = q.1).card) :
    (∀ r ∈ E, r.1 = q.1 → r.2.val ≤ q.2.val) ∧
      (∀ r ∈ F, r.1 = q.1 → r.2.val < q.2.val) := by
  have hsub : F ⊆ E := scan_subset he
  have hsubcol : F.filter (fun r => r.1 = q.1) ⊆ E.filter (fun r => r.1 = q.1) := Finset.filter_subset_filter _ hsub
  have hcard := Finset.card_sdiff_add_card_eq_card hsubcol
  have hqdiff : q ∈ E.filter (fun r => r.1 = q.1) \ F.filter (fun r => r.1 = q.1) := by simp [hq, hqF]
  have hsingleton : E.filter (fun r => r.1 = q.1) \ F.filter (fun r => r.1 = q.1) = {q} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr hqdiff)
    simp only [Finset.card_singleton]
    omega
  have hlower (r : Cell w h) (hr : r ∈ E) (hx : r.1 = q.1) : r.2.val ≤ q.2.val := by
    by_contra hy
    have hrf : r ∈ F := by
      by_contra hnot
      have hd : r ∈ E.filter (fun r => r.1 = q.1) \ F.filter (fun r => r.1 = q.1) := by simp [hr, hx, hnot]
      rw [hsingleton, Finset.mem_singleton] at hd
      cases hd
      omega
    have horder := round_deleted_before_retained .south requests T he hrf hq hqF (congrArg Fin.val hx)
    have hqbound := q.2.isLt
    have hrbound := r.2.isLt
    simp only [prefixRank] at horder
    omega
  refine ⟨hlower, ?_⟩
  intro r hr hx
  have hy := hlower r (hsub hr) hx
  have hne : r ≠ q := by intro heq; exact hqF (heq ▸ hr)
  have hny : r.2 ≠ q.2 := fun heq => hne (Prod.ext hx heq)
  have hny' : r.2.val ≠ q.2.val := fun heq => hny (Fin.ext heq)
  omega

/-- A reference front containing at most one hole and a real deletion certify the real column's entire south side. -/
theorem south_round_front_at_most_one_exhausted {w h : ℕ} (lanes : Finset ℕ) (span : ℕ → ℕ)
    (T E F : Finset (Cell w h)) {q : Cell w h} (hx : q.1.val ∈ lanes)
    (he : Scan.eval (instructions (emit [.read .south (prefixRequests lanes span)] T).rounds) E = some F)
    (hq : q ∈ E) (hqF : q ∉ F)
    (hbound : (T.filter fun r => r.1.val = q.1.val ∧ prefixRank .south r < span q.1.val).card ≤ 1) :
    (∀ r ∈ E, r.1 = q.1 → r.2.val ≤ q.2.val) ∧
      (∀ r ∈ F, r.1 = q.1 → r.2.val < q.2.val) := by
  have hpositive := south_round_front_positive lanes span T E F hx he hq hqF
  have hone : (T.filter fun r => r.1.val = q.1.val ∧ prefixRank .south r < span q.1.val).card = 1 := by omega
  have hloss := south_round_single_front_loss lanes span T E F hx hone he
  apply south_round_cut_exhausted (prefixRequests lanes span) T E F he hq hqF
  simpa only [Fin.ext_iff] using hloss

end PushPuzzle.Push.AcceptanceSoundness
