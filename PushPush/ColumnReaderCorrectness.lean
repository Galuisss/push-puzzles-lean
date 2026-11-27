/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.ColumnReaderMinimum
public import PushPush.ColumnReaderLift
public import PushPush.ColumnReaderRuns

/-! Complete physical correctness of one maximum-sliding committed column reader. -/

@[expose] public section
namespace PushPuzzle.PushPush.ColumnReader

open PushFS (Cell State)

variable (r : Push.ColumnScan.Input)

/-- All quotas are paid in one source configuration reached at its corner by maximum sliding. -/
def CornerQuotas : Prop := ∃ s : State r.width r.height,
  Reachable r.initial.toState s ∧ s.player = r.sourceCorner ∧
    ∀ i : Fin r.width, r.quotas.getD i.val 0 ≤ (s.boxesᶜ.filter fun p => p.1 = i).card

theorem compile_solvable_of_source {s : State r.width r.height}
    (hr : Reachable r.initial.toState s) (hp : s.player = r.sourceCorner)
    (hq : ∀ i : Fin r.width, r.quotas.getD i.val 0 ≤ (s.boxesᶜ.filter fun p => p.1 = i).card) :
    PushPush.Instance.Solvable r.compile := by
  have hv := hr.valid (Finset.notMem_compl.mpr r.initial.player_empty)
  let U : PushS.HoleState r.width r.height := ⟨s.player, s.boxesᶜ, Finset.mem_compl.mpr hv⟩
  have hU : U.toState = s := by
    apply State.ext
    · rfl
    · simp only [PushS.HoleState.toState, U, compl_compl]
  have hcard : U.empty.card = r.initial.empty.card := by
    change s.boxesᶜ.card = r.initial.empty.card
    have he := hr.card_boxes
    change s.boxes.card = r.initial.emptyᶜ.card at he
    simp only [Finset.card_compl] at he ⊢
    have hle := Finset.card_le_univ r.initial.empty
    have hlet := Finset.card_le_univ s.boxes
    omega
  let R := r.withInitial U hcard
  have hread : PushPush.Instance.Solvable R.compile := by
    apply compile_solvable_of_quotas R hp
    intro i
    rw [sourceColumn_eq, Finset.card_image_of_injective _ R.embed_injective]
    exact hq i
  change PushPush.Instance.Solvable (r.withInitial U hcard).compile at hread
  rw [r.withInitial_compile U hcard] at hread
  obtain ⟨t, ht, htplayer⟩ := hread
  have hprefix := lift_source_initial r hr hp
  refine ⟨t, hprefix.trans ?_, htplayer⟩
  change @Reachable r.outputWidth r.outputHeight (r.liftState U.toState) t at ht
  rw [hU] at ht
  exact ht

/-- The single physical destination tests precisely the simultaneous source corner quotas. -/
theorem compile_solvable_iff : PushPush.Instance.Solvable r.compile ↔ CornerQuotas r := by
  constructor
  · rintro ⟨t, hr, hp⟩
    exact source_corner_quotas r hr hp
  · rintro ⟨s, hr, hp, hq⟩
    exact compile_solvable_of_source r hr hp hq

end PushPuzzle.PushPush.ColumnReader
