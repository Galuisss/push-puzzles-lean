/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ColumnScanForwardRead
public import Push.ReaderResidualOrder
import all Push.ColumnScanForwardRead

/-! Exact source deletion by the concrete sequence of complete north pushes. -/

public section
namespace PushPuzzle.Push.ColumnScan.HoleState

open PushFS PushS ReaderResidual

variable {w h : ℕ}

/-- All source-row holes, retaining their original board coordinates. -/
@[expose] def sourceRows (s : PushS.HoleState w h) (cutoff : ℕ) : Finset (Cell w h) :=
  s.empty.filter fun q => q.2.val < cutoff

private def sourceRows_pop (s t : PushS.HoleState w h) (cutoff : ℕ) (b : Cell w h)
    (hb : b ∈ northSources s cutoff)
    (hmax : ∀ q ∈ northSources s cutoff, q.2.val ≤ b.2.val)
    (hy : cutoff ≤ t.player.2.val) (he : t.empty = insert t.player (s.empty.erase b)) :
    BottomPop (sourceRows s cutoff) (sourceRows t cutoff) := by
  obtain ⟨hbE, hbx, hby⟩ := Finset.mem_filter.mp hb
  refine ⟨b, Finset.mem_filter.mpr ⟨hbE, hby⟩, ?_, ?_⟩
  · intro q hq hx
    obtain ⟨hqE, hqy⟩ := Finset.mem_filter.mp hq
    exact hmax q (Finset.mem_filter.mpr ⟨hqE, hx.trans hbx, hqy⟩)
  · ext q
    simp only [sourceRows, he, Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
    by_cases hqp : q = t.player
    · subst q; simp only [true_or, true_and]; omega
    · simp only [hqp, false_or]; tauto

private theorem read_step_exact (s : PushS.HoleState w h) (cutoff n : ℕ)
    (hspace : cutoff + (n + 1) < s.player.2.val)
    (hcount : n + 1 ≤ (northSources s cutoff).card)
    (hgap : ∀ q : Cell w h, q.1 = s.player.1 → cutoff ≤ q.2.val →
      q.2.val < s.player.2.val → q ∉ s.empty)
    (B : Board w h) (hB : B.walls = ∅) :
    ∃ t : PushS.HoleState w h, Move B none .north s.toState t.toState ∧
      t.player.1 = s.player.1 ∧ t.player.2.val + 1 = s.player.2.val ∧
      n ≤ (northSources t cutoff).card ∧
      (∀ q : Cell w h, q.1 = t.player.1 → cutoff ≤ q.2.val →
        q.2.val < t.player.2.val → q ∉ t.empty) ∧
      (∀ q : Cell w h, q.1 ≠ s.player.1 → (q ∈ t.empty ↔ q ∈ s.empty)) ∧
      (northSources t cutoff).card + 1 = (northSources s cutoff).card ∧
      Nonempty (BottomPop (sourceRows s cutoff) (sourceRows t cutoff)) := by
  have hne : (northSources s cutoff).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨b, hb, hmax⟩ := (northSources s cutoff).exists_max_image (fun q => q.2.val) hne
  have hbx := (Finset.mem_filter.mp hb).2.1
  let p : Cell w h := (s.player.1, ⟨s.player.2.val - 1, by have := s.player.2.isLt; omega⟩)
  let t : PushS.HoleState w h := ⟨p, insert p (s.empty.erase b), Finset.mem_insert_self _ _⟩
  have hp : p.2.val + 1 = s.player.2.val := by dsimp [p]; omega
  have hcut : cutoff ≤ p.2.val := by omega
  have hmove := move_to_max_source s t cutoff b hb hmax (by omega) hgap ⟨rfl, hp⟩ rfl B hB
  have hsource := northSources_transport s t cutoff b rfl hcut rfl
  have hcard : (northSources t cutoff).card + 1 = (northSources s cutoff).card := by
    rw [hsource]
    exact Finset.card_erase_add_one hb
  refine ⟨t, hmove, rfl, hp, by omega, ?_, ?_, hcard, ?_⟩
  · intro q hx hlo hhi hq
    change q.1 = s.player.1 at hx
    change q.2.val < p.2.val at hhi
    simp only [t, Finset.mem_insert, Finset.mem_erase] at hq
    rcases hq with rfl | ⟨_, hq⟩
    · omega
    · exact hgap q hx hlo (by omega) hq
  · intro q hx
    have hqp : q ≠ p := fun he => hx ((congrArg Prod.fst he).trans (show p.1 = s.player.1 from rfl))
    have hqb : q ≠ b := fun he => hx ((congrArg Prod.fst he).trans hbx)
    simp [t, hqp, hqb]
  · exact ⟨sourceRows_pop s t cutoff b hb hmax hcut rfl⟩

/-- The canonical pushes delete exactly their quota, retaining northern prefixes of every source column. -/
theorem read_north_exact (s : PushS.HoleState w h) (cutoff n : ℕ)
    (hspace : cutoff + n < s.player.2.val)
    (hcount : n ≤ (northSources s cutoff).card)
    (hgap : ∀ q : Cell w h, q.1 = s.player.1 → cutoff ≤ q.2.val →
      q.2.val < s.player.2.val → q ∉ s.empty)
    (B : Board w h) (hB : B.walls = ∅) :
    ∃ t : PushS.HoleState w h, Reachable B none s.toState t.toState ∧
      t.player.1 = s.player.1 ∧ t.player.2.val + n = s.player.2.val ∧
      (∀ q : Cell w h, q.1 ≠ s.player.1 → (q ∈ t.empty ↔ q ∈ s.empty)) ∧
      (northSources t cutoff).card + n = (northSources s cutoff).card ∧
      BottomRemainder (sourceRows s cutoff) (sourceRows t cutoff) := by
  induction n generalizing s with
  | zero => exact ⟨s, .refl, rfl, by simp, fun _ _ => Iff.rfl, by simp, .refl _⟩
  | succ n ih =>
    obtain ⟨t, hm, hx, hy, hcount', hgap', hframe, hcard, hpop⟩ :=
      read_step_exact s cutoff n hspace hcount hgap B hB
    obtain ⟨u, hrun, hux, huy, huframe, hucard, hrem⟩ := ih t (by omega) hcount' hgap'
    refine ⟨u, (Relation.ReflTransGen.single ⟨.north, hm⟩).trans hrun,
      hux.trans hx, by omega, ?_, by omega, ((BottomRemainder.refl _).pop hpop.some).trans hrem⟩
    intro q hq
    exact (huframe q (by rwa [hx])).trans (hframe q hq)

end PushPuzzle.Push.ColumnScan.HoleState
