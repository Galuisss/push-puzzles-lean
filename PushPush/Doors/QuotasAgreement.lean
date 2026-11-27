/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.QuotasStock
public import Push.ScanComposition
public import Push.ScanColumns

/-! Actual prefix quotas depend only on holes touched by their literal coordinate regions. -/

public section
namespace PushPuzzle.PushPush.Doors

open PushFS (Cell Direction)
open Push.AcceptanceProgram

variable {w h : ℕ}

private theorem read_quotas_agree (side : Direction) (requests : List (ℕ × ℕ))
    (E F : Finset (Cell w h))
    (hag : ∀ p ∈ readRegion side requests, p ∈ E ↔ p ∈ F) :
    (emitReads side requests E).quotas = (emitReads side requests F).quotas := by
  induction requests generalizing E F with
  | nil => rfl
  | cons request requests ih =>
    rcases request with ⟨lane, span⟩
    let front := (Push.Scan.lineCells (w := w) (h := h) side lane).take span
    have he : (E.filter fun p => p ∈ front) = F.filter fun p => p ∈ front := by
      ext p
      simp only [Finset.mem_filter]
      by_cases hp : p ∈ front
      · have hr : p ∈ readRegion side ((lane, span) :: requests) :=
          Finset.mem_union_left _ (List.mem_toFinset.mpr hp)
        exact and_congr_left (fun _ => hag p hr)
      · simp only [hp, and_false]
    have ht := ih (E \ front.toFinset) (F \ front.toFinset) (by
      intro p hp
      have hr : p ∈ readRegion side ((lane, span) :: requests) := Finset.mem_union_right _ hp
      simp only [Finset.mem_sdiff]
      exact and_congr_left (fun _ => hag p hr))
    change (lane, (E.filter fun p => p ∈ front).card) :: _ =
      (lane, (F.filter fun p => p ∈ front).card) :: _
    rw [he, ht]

/-- Two stocks agreeing on the complete requested region emit exactly the same actual quotas. -/
theorem emit_rounds_agree (stages : List Template) (E F : Finset (Cell w h))
    (hag : ∀ p ∈ allRegions stages, p ∈ E ↔ p ∈ F) :
    (Push.AcceptanceProgram.emit stages E).rounds = (Push.AcceptanceProgram.emit stages F).rounds := by
  induction stages generalizing E F with
  | nil => rfl
  | cons stage stages ih =>
    cases stage with
    | read side requests =>
      have hq := read_quotas_agree side requests E F
        (fun p hp => hag p (Finset.mem_union_left _ hp))
      have ht := ih (emitReads side requests E).remaining (emitReads side requests F).remaining (by
        intro p hp
        rw [emitReads_remaining, emitReads_remaining]
        simp only [Finset.mem_sdiff]
        exact and_congr_left (fun _ => hag p (Finset.mem_union_right _ hp)))
      change Round.read side (emitReads side requests E).quotas :: _ =
        Round.read side (emitReads side requests F).quotas :: _
      rw [hq, ht]
    | clear side lanes =>
      have ht := ih (E.filter fun p => side.lane p ∉ lanes)
        (F.filter fun p => side.lane p ∉ lanes) (by
          intro p hp
          simp only [Finset.mem_filter]
          exact and_congr_left (fun _ => hag p (Finset.mem_union_right _ hp)))
      change Round.clear side lanes :: _ = Round.clear side lanes :: _
      rw [ht]

namespace Source.Stock

variable {I : Instance}

/-- Every parked register assignment pays the very same first six physical rounds. -/
theorem quotaPrefix_rounds_equal (S T : Stock I)
    (hs : S.signal = atRow false I (layout false I).stop)
    (ht : T.signal = atRow false I (layout false I).stop) :
    (Push.AcceptanceProgram.emit ((layout false I).quotaTemplates.take 6) (S.boxes false)ᶜ).rounds =
    (Push.AcceptanceProgram.emit ((layout false I).quotaTemplates.take 6) (T.boxes false)ᶜ).rounds :=
  emit_rounds_agree _ _ _ (fun p hp => S.prefix_holes_agree T hs ht p hp)

end Source.Stock
end PushPuzzle.PushPush.Doors
