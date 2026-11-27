/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Closure

/-!
# Permanent empty walks protected by frozen boundary cells

To consume a hole, a push must reach its occupied predecessor and the cell immediately
behind that predecessor. A known blocker at either cell prevents the consumption.
-/

public section

namespace PushPuzzle.PushS.Freeze


open PushFS

/-- Each outward boundary of the empty region meets a blocker at its first or second cell.
The region `H` is already known to remain empty. -/
structure EmptyBoundary {w h : ℕ} (P H G : Finset (Cell w h)) : Prop where
  /-- A push entering the empty region from an occupied predecessor crosses a blocker. -/
  guard : ∀ d p a b, p ∈ P → p ∉ H → Adjacent d a p → a ∉ P → Adjacent d b a → a ∈ G ∨ b ∈ G

variable {w h : ℕ} {P H G : Finset (Cell w h)} {B : Board w h} {cap : Option ℕ}
  {d : Direction} {s t : State w h}

private theorem guarded_push_holes (hguard : EmptyBoundary P H G) {n : ℕ}
    (run : Run B d s n) (hn : 0 < n)
    (hb : t.boxes = insert (run.cell ⟨n + 1, by omega⟩) (s.boxes.erase (run.cell 1)))
    (havoid : ∀ i, run.cell i ∉ G) (hP : P ⊆ holes s) (hH : H ⊆ holes t) : P ⊆ holes t := by
  intro p hp
  apply (mem_holes _).mpr
  intro hbox
  rw [hb] at hbox
  rcases Finset.mem_insert.mp hbox with he | hbox
  · subst p
    by_cases hlast : run.cell ⟨n + 1, by omega⟩ ∈ H
    · exact (mem_holes _).mp (hH hlast) (hb ▸ Finset.mem_insert_self _ _)
    · cases n with
      | zero => omega
      | succ m =>
        let a : Fin (m + 3) := ⟨m + 1, by omega⟩
        let b : Fin (m + 3) := ⟨m, by omega⟩
        have ha : run.cell a ∉ P := fun h =>
          (mem_holes _).mp (hP h) (run.occupied_at a (by dsimp [a]; omega) (by dsimp [a]; omega))
        have hpa : Adjacent d (run.cell a) (run.cell ⟨m + 2, by omega⟩) :=
          run.adjacent ⟨m + 1, by omega⟩
        have hab : Adjacent d (run.cell b) (run.cell a) := run.adjacent ⟨m, by omega⟩
        exact (hguard.guard d _ _ _ hp hlast hpa ha hab).elim (havoid a) (havoid b)
  · exact (mem_holes _).mp (hP hp) (Finset.mem_of_mem_erase hbox)

/-- An actual step avoiding the frozen boundary preserves all protected empty cells. -/
theorem EmptyBoundary.step_holes (hguard : EmptyBoundary P H G)
    (hm : AvoidingStep B cap G s t) (hP : P ⊆ holes s) (hH : H ⊆ holes t) : P ⊆ holes t := by
  obtain ⟨e, hmove⟩ := hm.1
  cases hmove with
  | walk _ _ _ _ hb => simpa only [holes, hb] using hP
  | push _ hn _ run hp hb => exact guarded_push_holes hguard run hn hb (hm.2 e _ run hn hp hb) hP hH

/-- The protected walks remain empty throughout any trajectory preserving the earlier holes
and avoiding the established frozen blockers. -/
theorem EmptyBoundary.reachable_holes (hguard : EmptyBoundary P H G)
    (hr : Relation.ReflTransGen (fun u v => AvoidingStep B cap G u v ∧ H ⊆ holes v) s t)
    (hP : P ⊆ holes s) : P ⊆ holes t := by
  induction hr with
  | refl => exact hP
  | tail _ hm ih => exact hguard.step_holes hm.1 ih hm.2

end PushPuzzle.PushS.Freeze
