/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ColumnScanSourceLiftLayout
public import PushFS.WallCongruence

/-! A real source computation to a corner satisfying the quotas completes the physical reader. -/

public section
namespace PushPuzzle.Push.ColumnScan.Input

open PushFS PushS

variable (r : Input)

/-- Any actual source computation reaching its corner with enough holes in every column solves the reader. -/
theorem compile_solvable_of_source_corner_quotas {s : State r.width r.height}
    (hr : Reachable r.sourceBoard none r.initial.toState s)
    (hcorner : s.player = r.sourceCorner)
    (hquotas : ∀ i : Fin r.width,
      r.quotas.getD i.val 0 ≤ ((holes s).filter fun p => p.1 = i).card) : r.compile.Solvable := by
  have hv := hr.valid (r.initial.valid r.sourceBoard rfl)
  let U : HoleState r.width r.height := ⟨s.player, holes s, player_mem_holes hv⟩
  have hU : U.toState = s := by
    apply State.ext
    · rfl
    · simp only [HoleState.toState, U, holes, compl_compl]
  have hcard : U.empty.card = r.initial.empty.card := by
    change (holes s).card = r.initial.empty.card
    rw [card_holes_reachable hr, r.initial.holes_toState]
  have hreader : (r.withInitial U hcard).compile.Solvable := by
    apply (r.withInitial U hcard).compile_solvable_of_column_quotas
    · exact hcorner
    · exact hquotas
  rw [r.withInitial_compile U hcard] at hreader
  obtain ⟨t, hread, ht⟩ := hreader
  have hprefix : Reachable r.compile.board none r.compile.initial (r.liftState U.toState) := by
    rw [hU]
    exact r.lift_source_initial_reachable hr
  exact ⟨t, hprefix.trans (hread.reboard rfl), ht⟩

end PushPuzzle.Push.ColumnScan.Input
