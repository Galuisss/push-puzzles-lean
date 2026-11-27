/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.CompilerBounds
public import Push.AcceptanceProgramPolyTimeEmissionCorrect

/-! Seven actual full-quota read rounds protecting the door work board. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Layout

open PushFS (Cell Direction)
open Push.AcceptanceProgram

/-- Every original rack-box row, including the two neighbours of each divider. -/
def rackProbeRows (L : Layout) : List ℕ := L.rackList.map Prod.snd

/-- Divider, endpoint-cap and accepting-signal rows. -/
def markerRows (L : Layout) : List ℕ :=
  (L.dividers ++ L.caps ++ [L.stop]).map (fun y => y + L.shift)

/-- The forbidden neighbouring rows of all chamber dividers. -/
def dividerNeighbors (L : Layout) : List ℕ :=
  L.dividers.flatMap fun y => [y + L.shift - 1, y + L.shift + 1]

/-- The right-hand probes stop immediately before the protected rack or working-column box. -/
def probeRequests (L : Layout) : List (ℕ × ℕ) :=
  (L.rackProbeRows.map fun y => (y, L.width - L.rackX - 1)) ++
    (L.markerRows.map fun y => (y, L.width - L.rackX))

/-- Full final-column reads remove every remaining original data hole. -/
def finalRequests (L : Layout) : List (ℕ × ℕ) :=
  (List.range L.width).map fun x => (x, L.height)

/-- South, west, north, east, south, west and north, with two empty rotation rounds. -/
def quotaTemplates (L : Layout) : List Template :=
  [.read .south [(0, L.height), (L.width - 1, L.height)],
    .read .west [(0, L.width), (L.height - 1, L.width)],
    .read .north [], .read .east L.probeRequests, .read .south [],
    .read .west (L.dividerNeighbors.map fun y => (y, L.rackX)),
    .read .north L.finalRequests]

/-- One representative stable door assignment with the signal at the real accepting output. -/
def referenceHoles (L : Layout) : Finset (Cell L.width L.height) := (L.raster L.goalsRaw)ᶜ

/-- The literal compact quotas emitted from that complete finite reference bitmap. -/
def quotaProgram (L : Layout) : Emission L.width L.height :=
  Push.AcceptanceProgram.emit L.quotaTemplates L.referenceHoles

private theorem finalRegion_univ (L : Layout) :
    readRegion (w := L.width) (h := L.height) .north L.finalRequests = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro p
  apply (mem_readRegion _ _ p).mpr
  refine ⟨(p.1.val, L.height), ?_, rfl, p.2.isLt⟩
  exact List.mem_map.mpr ⟨p.1.val, List.mem_range.mpr p.1.isLt, rfl⟩

private theorem quotaRegions_univ (L : Layout) :
    allRegions (w := L.width) (h := L.height) L.quotaTemplates = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro p
  apply (mem_allRegions _ p).mpr
  refine ⟨.read .north L.finalRequests, ?_, ?_⟩
  · simp [quotaTemplates]
  · change p ∈ readRegion .north L.finalRequests
    rw [L.finalRegion_univ]
    exact Finset.mem_univ _

private theorem quotaProgram_remaining (L : Layout) : L.quotaProgram.remaining = ∅ := by
  rw [quotaProgram, emit_remaining, L.quotaRegions_univ]
  ext p
  simp

private theorem quotaProgram_discarded (L : Layout) : L.quotaProgram.discarded = 0 := rfl

/-- Every original reference hole pays exactly one actual quota unit. -/
theorem quotaProgram_quota (L : Layout) :
    Push.Scan.quota (instructions (w := L.width) (h := L.height) L.quotaProgram.rounds) =
      L.referenceHoles.card := by
  have he := emit_accounting L.quotaTemplates L.referenceHoles
  change L.quotaProgram.remaining.card + (L.quotaProgram.rounds.map Round.quota).sum +
    L.quotaProgram.discarded = _ at he
  rw [L.quotaProgram_remaining, Finset.card_empty, L.quotaProgram_discarded,
    Nat.zero_add, Nat.add_zero, ← quota_instructions] at he
  exact he

/-- The reference's target inventory has the same full-hole budget as the real initial board. -/
theorem Balanced.quotaProgram_initial {L : Layout} (h : L.Balanced) :
    Push.Scan.quota (instructions (w := L.width) (h := L.height) L.quotaProgram.rounds) =
      (L.initial.boxesᶜ).card := by
  rw [L.quotaProgram_quota]
  unfold referenceHoles
  rw [Finset.card_compl, Finset.card_compl, ← h.card_eq]
  rfl

end PushPuzzle.PushPush.Doors.Layout
