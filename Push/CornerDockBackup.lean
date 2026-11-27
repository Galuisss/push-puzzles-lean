/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CornerDockBackupCanonical
public import Push.CornerDockBackupRows

/-! Complete backup-row sweeps, including the actual trip from and back to the southwest corner. -/

public section
namespace PushPuzzle.Push.CornerDock.Backup

open PushFS PushS

/-- The junction of the western return path and the vertical exit corridor. -/
@[expose] def junction (r : Input) : Cell r.outputWidth r.outputHeight :=
  (r.entry.1, ⟨r.height, by have := r.distance_pos; dsimp [Input.outputHeight]; omega⟩)

private def westJunction (r : Input) : Cell r.outputWidth r.outputHeight :=
  (r.target.1, (junction r).2)

private theorem junction_walks (r : Input) (s : HoleState r.outputWidth r.outputHeight)
    (hp : s.player = r.target)
    (hw : ∀ q : Cell r.outputWidth r.outputHeight, q.1.val = 0 → r.height ≤ q.2.val → q ∈ s.empty)
    (hj : junction r ∈ s.empty) :
    Reachable r.compile.board none s.toState (s.walk (junction r) hj).toState ∧
      Reachable r.compile.board none (s.walk (junction r) hj).toState s.toState := by
  have he : westJunction r ∈ s.empty := hw _ rfl le_rfl
  have hv := s.walk_vertical (westJunction r) he (by
    rw [hp]; rfl) (by
      intro q hx hlo _
      apply hw q
      · exact (congrArg Fin.val hx).trans (by rw [hp]; rfl)
      · have hh : r.height ≤ r.outputHeight - 1 := by
          have := r.distance_pos; dsimp [Input.outputHeight]; omega
        rw [hp] at hlo
        change min (r.outputHeight - 1) r.height ≤ q.2.val at hlo
        rwa [Nat.min_eq_right hh] at hlo) r.compile.board r.compile.walls_empty none
  have heast := (s.walk (westJunction r) he).walk_move hj (d := .east)
    ⟨rfl, rfl⟩ r.compile.board r.compile.walls_empty none
  have hwest := (s.walk (junction r) hj).walk_move he (d := .west)
    ⟨rfl, rfl⟩ r.compile.board r.compile.walls_empty none
  exact ⟨hv.1.tail ⟨.east, heast⟩, (Relation.ReflTransGen.single ⟨.west, hwest⟩).trans hv.2⟩

/-- Fill distinct corridor-accessible rows using only their actual eastern inventories, then return to the corner. -/
theorem run_rows (r : Input) (s : HoleState r.outputWidth r.outputHeight)
    (hp : s.player = r.target) (source : State r.width r.height) (hready : Ready r source s)
    (rows : List (Fin r.outputHeight)) (hnd : rows.Nodup)
    (hrows : ∀ row ∈ rows, r.goalY.val ≤ row.val ∧ row.val ≤ r.height)
    (n cut keep : ℕ) (hcut : 1 + n < cut)
    (hcount : ∀ row ∈ rows, n + keep ≤ (rowStock s row cut).card) :
    ∃ t : HoleState r.outputWidth r.outputHeight,
      Reachable r.compile.board none s.toState t.toState ∧ t.player = r.target ∧
      (∀ row ∈ rows, ∀ q : Cell r.outputWidth r.outputHeight, q.2 = row →
        1 ≤ q.1.val → q.1.val ≤ 1 + n → q ∈ t.empty) ∧
      (∀ q : Cell r.outputWidth r.outputHeight, q.2 ∉ rows ∨ q.1.val ≤ 1 → (q ∈ t.empty ↔ q ∈ s.empty)) ∧
      ∀ row ∈ rows, keep ≤ (rowStock t row cut).card := by
  have hj : junction r ∈ s.empty := hready.corridor _ rfl (Nat.le_of_lt r.goalY.isLt) le_rfl
  let a := s.walk (junction r) hj
  have hgo := (junction_walks r s hp hready.western hj).1
  obtain ⟨b, hb, hbp, hfilled, hframe, hkeep⟩ := fill_rows_return a rows n cut keep hnd hcut hcount (by
    intro row hr q hqx hlo hhi
    obtain ⟨hrowlo, hrowhi⟩ := hrows row hr
    apply hready.corridor q (congrArg Fin.val hqx)
    · change min r.height row.val ≤ q.2.val at hlo
      omega
    · change q.2.val ≤ max r.height row.val at hhi
      omega) r.compile.board r.compile.walls_empty
  have hwestern : ∀ q : Cell r.outputWidth r.outputHeight,
      q.1.val = 0 → r.height ≤ q.2.val → q ∈ b.empty := by
    intro q hx hy
    exact (hframe q (Or.inr (by change q.1.val ≤ 1; omega))).mpr (hready.western q hx hy)
  have htarget : r.target ∈ b.empty := hwestern _ rfl (by
    change r.height ≤ r.outputHeight - 1
    have := r.distance_pos; dsimp [Input.outputHeight]; omega)
  let c := b.walk r.target htarget
  have hjb : junction r ∈ c.empty := by
    apply (hframe _ (Or.inr le_rfl)).mpr
    exact hj
  have hback := (junction_walks r c rfl hwestern hjb).2
  have he : (c.walk (junction r) hjb).toState = b.toState := by
    apply State.ext
    · exact hbp.symm
    · rfl
  rw [he] at hback
  exact ⟨c, (hgo.trans hb).trans hback, rfl, hfilled, hframe, hkeep⟩

end PushPuzzle.Push.CornerDock.Backup
