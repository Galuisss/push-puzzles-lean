/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ReaderResidual
public import Push.ReaderResidualOrder

/-! Complete pushes from below remove source holes in bottom-first order. -/

public section
namespace PushPuzzle.Push.ReaderResidual

open PushFS PushS ReflectedFrontier

variable {w h cut height n : ℕ} {B : Board w h} {cap : Option ℕ}
  {d : Direction} {s t : State w h}

private theorem north_run_maximal (run : Run B .north s n) (hs : height ≤ s.player.2.val)
    {p : Cell w h} (hp : p ∈ source cut height s)
    (hx : p.1 = (run.cell ⟨n + 1, by omega⟩).1) :
    p.2.val ≤ (run.cell ⟨n + 1, by omega⟩).2.val := by
  by_contra hy
  have hpy := (Finset.mem_filter.mp hp).2.2
  have hend := run.position ⟨n + 1, by omega⟩
  have hlend := run.lane ⟨n + 1, by omega⟩
  simp only [Direction.position, Direction.lane] at hend hlend
  let k := s.player.2.val - p.2.val
  have hk : 0 < k ∧ k ≤ n := by dsimp [k]; omega
  let i : Fin (n + 2) := ⟨k, by omega⟩
  have hpos := run.position i
  have hlane := run.lane i
  simp only [Direction.position, Direction.lane] at hpos hlane
  have he : run.cell i = p := by
    apply Prod.ext <;> apply Fin.ext
    · have hxp := congrArg Fin.val hx
      omega
    · change -((run.cell i).2.val : ℤ) = -(s.player.2.val : ℤ) + (k : ℤ) at hpos
      dsimp [k] at hpos
      omega
  exact (mem_holes _).mp (Finset.mem_filter.mp hp).1 (he ▸ run.occupied_at i hk.1 hk.2)

/-- A source destination above the player forces the true push direction to be north. -/
theorem source_push_north (run : Run B d s n) (hs : height ≤ s.player.2.val)
    (hq : run.cell ⟨n + 1, by omega⟩ ∈ source cut height s) : d = .north := by
  have hy := (Finset.mem_filter.mp hq).2.2
  have hpos := run.position ⟨n + 1, by omega⟩
  have hlane := run.lane ⟨n + 1, by omega⟩
  cases d <;> simp only [Direction.position, Direction.lane] at hpos hlane <;> first | rfl | omega

/-- The actual complete source push deletes precisely the southernmost hole of its column. -/
private theorem source_push_pop (run : Run B d s n) (hn : 0 < n)
    (hp : t.player = run.cell 1)
    (hb : t.boxes = insert (run.cell ⟨n + 1, by omega⟩) (s.boxes.erase (run.cell 1)))
    (hs : height ≤ s.player.2.val) (ht : height ≤ t.player.2.val)
    (hq : run.cell ⟨n + 1, by omega⟩ ∈ source cut height s) :
    Nonempty (BottomPop (source cut height s) (source cut height t)) := by
  have hdir := source_push_north run hs hq
  subst d
  exact ⟨⟨run.cell ⟨n + 1, by omega⟩, hq,
    fun p hp hx => north_run_maximal run hs hp hx,
    source_push run hn hp hb (fun _ => ht)⟩⟩

/-- Any physical step below the source retains its source bitmap or performs one bottom pop. -/
private theorem source_step_pop (hm : Step B cap s t)
    (hs : height ≤ s.player.2.val) (ht : height ≤ t.player.2.val) :
    source cut height t = source cut height s ∨
      Nonempty (BottomPop (source cut height s) (source cut height t)) := by
  obtain ⟨d, hm⟩ := hm
  cases hm with
  | walk _ _ _ _ hb => exact Or.inl (by simp only [source, holes, hb])
  | @push n _ hn _ run hp hb =>
    by_cases hq : run.cell ⟨n + 1, by omega⟩ ∈ source cut height s
    · exact Or.inr (source_push_pop run hn hp hb hs ht hq)
    · exact Or.inl ((source_push run hn hp hb (fun _ => ht)).trans (Finset.erase_eq_of_notMem hq))

/-- Arbitrary source-avoiding trajectories retain northern prefixes in the original columns. -/
theorem source_remainder
    (hr : Relation.ReflTransGen (fun a b => Step B cap a b ∧ height ≤ a.player.2.val ∧
      height ≤ b.player.2.val) s t) : BottomRemainder (source cut height s) (source cut height t) := by
  induction hr with
  | refl => exact .refl _
  | tail _ hm ih =>
    rcases source_step_pop (cut := cut) hm.1 hm.2.1 hm.2.2 with he | hpop
    · simpa only [he] using ih
    · cases hpop with
      | intro pop => exact ih.pop pop

end PushPuzzle.Push.ReaderResidual
