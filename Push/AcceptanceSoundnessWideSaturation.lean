/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessWideColumn
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceSoundnessSupportSouthPayment
import all Push.AcceptanceProgramRegions

/-! A real lane's reference quota saturates its complete available fixed stock. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS AcceptanceProgram

/-- A canonical prefix block loses exactly its selected physical front on each requested lane. -/
theorem prefix_round_reference_card {w h : ℕ} (side : Direction) (cols : Finset ℕ) (span : ℕ → ℕ)
    (T : Finset (Cell w h)) (x : ℕ) (hx : x ∈ cols) :
    ((emit [.read side (prefixRequests cols span)] T).remaining.filter fun q => side.lane q = x).card +
      (T.filter fun q => side.lane q = x ∧ prefixRank side q < span x).card =
        (T.filter fun q => side.lane q = x).card := by
  have hremain : (emit [.read side (prefixRequests cols span)] T).remaining.filter (fun q => side.lane q = x) =
      (T.filter fun q => side.lane q = x).filter fun q => ¬prefixRank side q < span x := by
    rw [emit_remaining]
    ext q
    simp only [allRegions, Finset.union_empty, Template.region, Finset.mem_filter, Finset.mem_sdiff,
      prefix_region_iff]
    by_cases hq : side.lane q = x
    · simp only [hq, hx, true_and, and_true]
    · simp only [hq, and_false, false_and]
  have hpart := Finset.card_filter_add_card_filter_not (s := T.filter fun q => side.lane q = x)
    (fun q => prefixRank side q < span x)
  have hfront : ((T.filter fun q => side.lane q = x).filter fun q => prefixRank side q < span x) =
      T.filter fun q => side.lane q = x ∧ prefixRank side q < span x := Finset.filter_filter ..
  rw [hfront, ← hremain] at hpart
  omega

/-- A bounded real lane-payment stock is exactly saturated when its reference loss covers the stock's cardinality. -/
theorem round_lane_saturation {w h : ℕ} (side : Direction) (requests : List (ℕ × ℕ))
    (T E F S : Finset (Cell w h)) (lane : ℕ)
    (he : Scan.eval (instructions (emit [.read side requests] T).rounds) E = some F)
    (hstock : E.filter (fun q => side.lane q = lane) \ F.filter (fun q => side.lane q = lane) ⊆ S)
    (href : ((emit [.read side requests] T).remaining.filter fun q => side.lane q = lane).card + S.card ≤
      (T.filter fun q => side.lane q = lane).card) :
    S = E.filter (fun q => side.lane q = lane) \ F.filter (fun q => side.lane q = lane) := by
  have hsame := round_reference_lane_loss side requests T E F lane he
  have hsub := Finset.filter_subset_filter (fun q => side.lane q = lane) (scan_subset he)
  have hpart := Finset.card_sdiff_add_card_eq_card hsub
  have hcard : S.card ≤ (E.filter (fun q => side.lane q = lane) \ F.filter (fun q => side.lane q = lane)).card := by omega
  exact (Finset.eq_of_subset_of_card_le hstock hcard).symm

end PushPuzzle.Push.AcceptanceSoundness
