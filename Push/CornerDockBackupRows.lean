/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CornerDockBackupRow

/-! Visit distinct backup rows through one preserved vertical corridor and return to its starting cell. -/

public section
namespace PushPuzzle.Push.CornerDock.Backup

open PushFS PushS

variable {w h : ℕ}

/-- Eastern inventory in a designated row, independent of the current player. -/
@[expose] def rowStock (s : HoleState w h) (row : Fin h) (cut : ℕ) : Finset (Cell w h) :=
  s.empty.filter fun q => q.2 = row ∧ cut ≤ q.1.val

private theorem rowStock_frame (s t : HoleState w h) (row : Fin h) (cut : ℕ)
    (hf : ∀ q : Cell w h, q.2 = row → (q ∈ t.empty ↔ q ∈ s.empty)) :
    rowStock t row cut = rowStock s row cut := by
  ext q
  simp only [rowStock, Finset.mem_filter]
  by_cases hy : q.2 = row
  · rw [hf q hy]
  · simp only [hy, false_and, and_false]

/-- Reach a selected row by walking, fill its prefix by complete moves, and return through the preserved corridor. -/
private theorem fill_row_return (s : HoleState w h) (row : Fin h) (n cut keep : ℕ)
    (hcut : s.player.1.val + n < cut) (hcount : n + keep ≤ (rowStock s row cut).card)
    (hcorridor : ∀ q : Cell w h, q.1 = s.player.1 →
      min s.player.2.val row.val ≤ q.2.val → q.2.val ≤ max s.player.2.val row.val → q ∈ s.empty)
    (B : Board w h) (hB : B.walls = ∅) :
    ∃ t : HoleState w h, Reachable B none s.toState t.toState ∧ t.player = s.player ∧
      (∀ q : Cell w h, q.2 = row → s.player.1.val ≤ q.1.val →
        q.1.val ≤ s.player.1.val + n → q ∈ t.empty) ∧
      (∀ q : Cell w h, q.2 ≠ row ∨ q.1.val ≤ s.player.1.val → (q ∈ t.empty ↔ q ∈ s.empty)) ∧
      keep ≤ (rowStock t row cut).card := by
  let q : Cell w h := (s.player.1, row)
  have hq : q ∈ s.empty := hcorridor q rfl (by dsimp [q]; omega) (by dsimp [q]; omega)
  let a := s.walk q hq
  have ha := (s.walk_vertical q hq rfl hcorridor B hB none).1
  have hc : n + keep ≤ (inventory a cut).card := hcount
  obtain ⟨t, ht, hp, hfilled, hframe, hkeep⟩ := fill_east_return a n cut keep hcut hc B hB
  have hstart : s.player ∈ t.empty := (hframe s.player (Or.inr le_rfl)).mpr s.player_empty
  have htx := congrArg Prod.fst hp
  change t.player.1 = s.player.1 at htx
  have hty := congrArg Prod.snd hp
  change t.player.2 = row at hty
  have hback : Reachable B none t.toState (t.walk s.player hstart).toState := by
    apply (t.walk_vertical s.player hstart htx.symm ?_ B hB none).1
    intro p hpx hlo hhi
    apply (hframe p (Or.inr (Nat.le_of_eq (congrArg Fin.val (hpx.trans htx))))).mpr
    apply hcorridor p (hpx.trans htx)
    · rw [hty] at hlo
      omega
    · rw [hty] at hhi
      omega
  refine ⟨_, (ha.trans ht).trans hback, rfl, hfilled, hframe, ?_⟩
  have he : rowStock t row cut = inventory t cut := by
    ext p
    simp only [rowStock, inventory, hp, a, HoleState.walk, q]
  exact he ▸ hkeep

/-- Every listed row is filled using its own original eastern holes; all walks return to the same corridor cell. -/
theorem fill_rows_return (s : HoleState w h) (rows : List (Fin h)) (n cut keep : ℕ)
    (hnd : rows.Nodup) (hcut : s.player.1.val + n < cut)
    (hcount : ∀ row ∈ rows, n + keep ≤ (rowStock s row cut).card)
    (hcorridor : ∀ row ∈ rows, ∀ q : Cell w h, q.1 = s.player.1 →
      min s.player.2.val row.val ≤ q.2.val → q.2.val ≤ max s.player.2.val row.val → q ∈ s.empty)
    (B : Board w h) (hB : B.walls = ∅) :
    ∃ t : HoleState w h, Reachable B none s.toState t.toState ∧ t.player = s.player ∧
      (∀ row ∈ rows, ∀ q : Cell w h, q.2 = row → s.player.1.val ≤ q.1.val →
        q.1.val ≤ s.player.1.val + n → q ∈ t.empty) ∧
      (∀ q : Cell w h, q.2 ∉ rows ∨ q.1.val ≤ s.player.1.val → (q ∈ t.empty ↔ q ∈ s.empty)) ∧
      ∀ row ∈ rows, keep ≤ (rowStock t row cut).card := by
  induction rows generalizing s with
  | nil => exact ⟨s, .refl, rfl, by simp, fun _ _ => Iff.rfl, by simp⟩
  | cons row rows ih =>
    obtain ⟨hnot, hnd⟩ := List.nodup_cons.mp hnd
    obtain ⟨t, ht, hp, hfilled, hframe, hkeep⟩ := fill_row_return s row n cut keep hcut
      (hcount row (List.mem_cons_self ..)) (hcorridor row (List.mem_cons_self ..)) B hB
    have hcount' : ∀ j ∈ rows, n + keep ≤ (rowStock t j cut).card := by
      intro j hj
      rw [rowStock_frame s t j cut (fun q hq => hframe q (Or.inl (by
        intro he; exact hnot (he ▸ hq ▸ hj))))]
      exact hcount j (List.mem_cons_of_mem row hj)
    have hcorridor' : ∀ j ∈ rows, ∀ q : Cell w h, q.1 = t.player.1 →
        min t.player.2.val j.val ≤ q.2.val → q.2.val ≤ max t.player.2.val j.val → q ∈ t.empty := by
      intro j hj q hqx hlo hhi
      rw [hp] at hqx hlo hhi
      exact (hframe q (Or.inr (Nat.le_of_eq (congrArg Fin.val hqx)))).mpr
        (hcorridor j (List.mem_cons_of_mem row hj) q hqx hlo hhi)
    obtain ⟨u, hu, hup, hufilled, huframe, hukeep⟩ := ih t hnd (by rwa [hp]) hcount' hcorridor'
    refine ⟨u, ht.trans hu, hup.trans hp, ?_, ?_, ?_⟩
    · intro j hj q hqy hlo hhi
      rcases List.mem_cons.mp hj with rfl | hj
      · apply (huframe q (Or.inl (hqy ▸ hnot))).mpr
        exact hfilled q hqy hlo hhi
      · exact hufilled j hj q hqy (by rwa [hp]) (by rwa [hp])
    · intro q hq
      apply (huframe q ?_).trans (hframe q ?_)
      · rcases hq with hq | hq
        · exact Or.inl (fun h => hq (List.mem_cons_of_mem _ h))
        · exact Or.inr (by rwa [hp])
      · rcases hq with hq | hq
        · exact Or.inl (fun h => hq (List.mem_cons.mpr (Or.inl h)))
        · exact Or.inr hq
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · rw [rowStock_frame t u j cut (fun q hq => huframe q (Or.inl (hq ▸ hnot)))]
        exact hkeep
      · exact hukeep j hj

end PushPuzzle.Push.CornerDock.Backup
