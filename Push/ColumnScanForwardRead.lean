/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ColumnScanForward
import all PushS.LinePush
import Mathlib.Data.Finset.Max

/-! Complete north pushes consume source-column holes one at a time. -/

@[expose] public section
namespace PushPuzzle.Push.ColumnScan

open PushFS PushS

namespace HoleState

variable {w h : ℕ}

/-- The remaining source holes north of a read position in its own column. -/
def northSources (s : PushS.HoleState w h) (cutoff : ℕ) : Finset (Cell w h) :=
  s.empty.filter fun q => q.1 = s.player.1 ∧ q.2.val < cutoff

private theorem move_to_max_source (s t : PushS.HoleState w h) (cutoff : ℕ) (b : Cell w h)
    (hb : b ∈ northSources s cutoff)
    (hmax : ∀ q ∈ northSources s cutoff, q.2.val ≤ b.2.val)
    (hspace : cutoff + 1 < s.player.2.val)
    (hgap : ∀ q : Cell w h, q.1 = s.player.1 → cutoff ≤ q.2.val →
      q.2.val < s.player.2.val → q ∉ s.empty)
    (ht : Adjacent .north s.player t.player) (he : t.empty = insert t.player (s.empty.erase b))
    (B : Board w h) (hB : B.walls = ∅) : Move B none .north s.toState t.toState := by
  have hb' := Finset.mem_filter.mp hb
  apply PushS.HoleState.move_to_first_hole s t .north b (s.player.2.val - b.2.val - 1)
    (by omega) (congrArg Fin.val hb'.2.1) ?_ ?_ hb'.1 ht he B hB
  · change -(b.2.val : ℤ) = -(s.player.2.val : ℤ) +
      ((s.player.2.val - b.2.val - 1 : ℕ) : ℤ) + 1
    omega
  · intro q hl hlo hhi hq
    have hx : q.1 = s.player.1 := Fin.ext hl
    change -(s.player.2.val : ℤ) < -(q.2.val : ℤ) at hlo
    change -(q.2.val : ℤ) < -(b.2.val : ℤ) at hhi
    by_cases hc : cutoff ≤ q.2.val
    · exact hgap q hx hc (by omega) hq
    · have hm := hmax q (Finset.mem_filter.mpr ⟨hq, hx, by omega⟩)
      omega

private theorem northSources_transport (s t : PushS.HoleState w h) (cutoff : ℕ)
    (b : Cell w h) (hx : t.player.1 = s.player.1) (hy : cutoff ≤ t.player.2.val)
    (he : t.empty = insert t.player (s.empty.erase b)) :
    northSources t cutoff = (northSources s cutoff).erase b := by
  ext q
  simp only [northSources, he, hx, Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
  by_cases hqp : q = t.player
  · subst q
    simp only [true_or, true_and]
    omega
  · simp only [hqp, false_or]
    tauto

private theorem read_step (s : PushS.HoleState w h) (cutoff n : ℕ)
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
      (∀ q : Cell w h, q.1 ≠ s.player.1 → (q ∈ t.empty ↔ q ∈ s.empty)) := by
  have hne : (northSources s cutoff).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨b, hb, hmax⟩ := (northSources s cutoff).exists_max_image (fun q => q.2.val) hne
  have hb' := Finset.mem_filter.mp hb
  let p : Cell w h := (s.player.1, ⟨s.player.2.val - 1, by have := s.player.2.isLt; omega⟩)
  let t : PushS.HoleState w h := ⟨p, insert p (s.empty.erase b), Finset.mem_insert_self _ _⟩
  have hp : p.2.val + 1 = s.player.2.val := by dsimp [p]; omega
  have hcut : cutoff ≤ p.2.val := by omega
  have hmove := move_to_max_source s t cutoff b hb hmax (by omega) hgap ⟨rfl, hp⟩ rfl B hB
  have hsource := northSources_transport s t cutoff b rfl hcut rfl
  refine ⟨t, hmove, rfl, hp, ?_, ?_, ?_⟩
  · rw [hsource, Finset.card_erase_of_mem hb]
    omega
  · intro q hx hlo hhi hq
    change q.1 = s.player.1 at hx
    change q.2.val < p.2.val at hhi
    simp only [t, Finset.mem_insert, Finset.mem_erase] at hq
    rcases hq with rfl | ⟨_, hq⟩
    · omega
    · exact hgap q hx hlo (by omega) hq
  · intro q hx
    have hp1 : p.1 = s.player.1 := rfl
    have hqp : q ≠ p := fun he => hx ((congrArg Prod.fst he).trans hp1)
    have hqb : q ≠ b := fun he => hx ((congrArg Prod.fst he).trans hb'.2.1)
    simp [t, hqp, hqb]

/-- Read a prescribed number of source holes by actual complete north pushes.
Every other column retains its exact bitmap. -/
theorem read_north (s : PushS.HoleState w h) (cutoff n : ℕ)
    (hspace : cutoff + n < s.player.2.val)
    (hcount : n ≤ (northSources s cutoff).card)
    (hgap : ∀ q : Cell w h, q.1 = s.player.1 → cutoff ≤ q.2.val →
      q.2.val < s.player.2.val → q ∉ s.empty)
    (B : Board w h) (hB : B.walls = ∅) :
    ∃ t : PushS.HoleState w h, Reachable B none s.toState t.toState ∧
      t.player.1 = s.player.1 ∧ t.player.2.val + n = s.player.2.val ∧
      (∀ q : Cell w h, q.1 ≠ s.player.1 → (q ∈ t.empty ↔ q ∈ s.empty)) := by
  induction n generalizing s with
  | zero => exact ⟨s, .refl, rfl, by simp, fun _ _ => Iff.rfl⟩
  | succ n ih =>
    obtain ⟨t, hm, hx, hy, hcount', hgap', hframe⟩ :=
      read_step s cutoff n hspace hcount hgap B hB
    obtain ⟨u, hrun, hux, huy, huframe⟩ := ih t (by omega) hcount' hgap'
    refine ⟨u, (Relation.ReflTransGen.single ⟨.north, hm⟩).trans hrun,
      hux.trans hx, by omega, ?_⟩
    intro q hq
    exact (huframe q (by rwa [hx])).trans (hframe q hq)

end HoleState
end PushPuzzle.Push.ColumnScan
