/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Basic
public import PushPush.ReadMinimum
public import PushPush.ColumnReaderForward
import all Push.ColumnScanForwardColumns

/-! A single committed maximum-sliding reader tests ordinary simultaneous column quotas. -/

@[expose] public section
namespace PushPuzzle.PushPush.ColumnReader

open PushFS (Cell State)
open Reader

variable (r : Push.ColumnScan.Input)

private theorem read_needle_minimum (i : Fin r.width)
    (hq : r.quotas.getD i.val 0 ≤ (sourceColumn r i).card)
    (s : State r.outputWidth r.outputHeight) (hv : s.player ∉ s.boxes)
    (hp : s.player = r.needle i)
    (hc : ∀ p : Cell r.outputWidth r.outputHeight, p.1.val = i.val →
      (p ∉ s.boxes ↔ p ∈ r.empty)) :
    ∃ t : State r.outputWidth r.outputHeight, Reachable s t ∧ t.player.1 = s.player.1 ∧
      t.player.2.val + r.quotas.getD i.val 0 = s.player.2.val ∧
      ∀ p : Cell r.outputWidth r.outputHeight, p.1 ≠ s.player.1 → (p ∈ t.boxes ↔ p ∈ s.boxes) := by
  have hx : s.player.1.val = i.val := by rw [hp]; rfl
  have hy : s.player.2.val = r.needleLevel i := by rw [hp]; rfl
  have he := data_eq_sourceColumn r s i hx hc
  obtain ⟨t, ht, htx, hty, _, _, hframe⟩ := read_north_at_least
    (r.quotas.getD i.val 0) s r.height hv (he ▸ hq)
    (by rw [he, hy]; exact needle_space r i) (by
      intro p hpx hlo hhi
      have hpx : p.1.val = i.val := (congrArg Fin.val hpx).trans hx
      by_contra hn
      exact r.column_gap i p hpx hlo (by omega) ((hc p hpx).mp hn))
  exact ⟨t, ht, htx, hty, hframe⟩

private theorem advance_minimum (i : Fin r.width)
    (hq : r.quotas.getD i.val 0 ≤ (sourceColumn r i).card)
    (s : State r.outputWidth r.outputHeight) (hv : s.player ∉ s.boxes)
    (hx : s.player.1.val = i.val + 1) (hy : s.player.2.val = r.readLevel (i.val + 1))
    (hc : ∀ p : Cell r.outputWidth r.outputHeight, p.1.val = i.val →
      (p ∉ s.boxes ↔ p ∈ r.empty)) :
    ∃ t : State r.outputWidth r.outputHeight, Reachable s t ∧
      t.player.1.val = i.val ∧ t.player.2.val = r.readLevel i.val ∧
      ∀ p : Cell r.outputWidth r.outputHeight, p.1.val ≠ i.val → (p ∈ t.boxes ↔ p ∈ s.boxes) := by
  have hm : r.needle i ∉ s.boxes := (hc _ rfl).mpr (r.needle_mem i)
  let a : State r.outputWidth r.outputHeight := ⟨r.needle i, s.boxes⟩
  have hwalk : Move .west s a := .walk hv ⟨hx.symm, Fin.ext hy.symm⟩ hm rfl
  obtain ⟨t, ht, htx, hty, hframe⟩ := read_needle_minimum r i hq a hm rfl hc
  refine ⟨t, (Relation.ReflTransGen.single ⟨.west, hwalk⟩).trans ht,
    congrArg Fin.val htx, Nat.add_right_cancel (hty.trans (r.readLevel_succ i)), ?_⟩
  intro p hp
  exact hframe p (fun he => hp (congrArg Fin.val he))

private theorem read_columns_minimum
    (hq : ∀ i : Fin r.width, r.quotas.getD i.val 0 ≤ (sourceColumn r i).card)
    (k : ℕ) (hk : k ≤ r.width) (s : State r.outputWidth r.outputHeight)
    (hv : s.player ∉ s.boxes) (hx : s.player.1.val = k) (hy : s.player.2.val = r.readLevel k)
    (hc : ∀ p : Cell r.outputWidth r.outputHeight, p.1.val < k →
      (p ∉ s.boxes ↔ p ∈ r.empty)) :
    ∃ t : State r.outputWidth r.outputHeight, Reachable s t ∧
      t.player.1.val = 0 ∧ t.player.2.val = r.targetLevel ∧
      ∀ p : Cell r.outputWidth r.outputHeight, k ≤ p.1.val → (p ∈ t.boxes ↔ p ∈ s.boxes) := by
  induction k generalizing s with
  | zero => exact ⟨s, .refl, hx, by simpa only [Push.ColumnScan.Input.readLevel_zero] using hy,
      fun _ _ => Iff.rfl⟩
  | succ k ih =>
    let i : Fin r.width := ⟨k, by omega⟩
    obtain ⟨t, hread, htx, hty, hframe⟩ := advance_minimum r i (hq i) s hv hx hy
      (fun p hp => hc p (by change p.1.val = k at hp; omega))
    obtain ⟨u, hrun, hux, huy, hout⟩ := ih (by omega) t (hread.valid hv) htx hty (by
      intro p hp
      have he := hframe p (by dsimp [i]; omega)
      exact (not_congr he).trans (hc p (by omega)))
    refine ⟨u, hread.trans hrun, hux, huy, ?_⟩
    intro p hp
    exact (hout p (by omega)).trans (hframe p (by dsimp [i]; omega))

/-- Every simultaneous feasible quota vector has a physical maximum-sliding reader solution. -/
theorem compile_solvable_of_quotas (hcorner : r.initial.player = r.sourceCorner)
    (hq : ∀ i : Fin r.width, r.quotas.getD i.val 0 ≤ (sourceColumn r i).card) :
    PushPush.Instance.Solvable r.compile := by
  obtain ⟨t, hr, hx, hy, _⟩ := read_columns_minimum r hq r.width le_rfl r.sealedState.toState
    (Finset.notMem_compl.mpr r.sealedState.player_empty) rfl (by
      change r.firstLevel = r.firstLevel - (r.quotas.drop r.width).sum
      rw [← r.quotas_width, List.drop_length, List.sum_nil, Nat.sub_zero]) (by
      intro p hp
      simpa only [PushS.HoleState.toState, Finset.mem_compl, not_not] using r.sealedState_source_columns p hp)
  exact ⟨t, (sealed_reachable r hcorner).trans hr, Prod.ext (Fin.ext hx) (Fin.ext hy)⟩

end PushPuzzle.PushPush.ColumnReader
