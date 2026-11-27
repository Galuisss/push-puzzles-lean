/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.Blocked
public import PushS.Support

/-! Reverse support whose straight rays are cut by established unvisited holes. -/

@[expose] public section
namespace PushPuzzle.PushS.Support

open PushFS

variable {w h : ℕ} {B : Board w h} {cap : Option ℕ} {d : Direction}
  {s t : State w h} {G : Finset (Cell w h)} {C : Set (Cell w h)}

/-- A straight directed path avoiding all known blockers. -/
abbrev StraightReach (G : Finset (Cell w h)) (d : Direction) :=
  Relation.ReflTransGen (fun p q : Cell w h => Adjacent d p q ∧ p ∉ G ∧ q ∉ G)

/-- Adjacent supported holes propagate support only along a clear straight ray. -/
def RelativeClosed (C : Set (Cell w h)) (G : Finset (Cell w h)) : Prop :=
  ∀ ⦃d p q⦄, Adjacent d p q → p ∈ C → q ∈ C → p ∉ G → q ∉ G →
    ∀ r, StraightReach G d p r → r ∈ C

private theorem straightReach_run {n : ℕ} (run : Run B d s n)
    (hG : ∀ i, run.cell i ∉ G) (i : Fin (n + 2)) :
    StraightReach G d s.player (run.cell i) := by
  induction i using Fin.induction with
  | zero => simpa only [run.start] using (Relation.ReflTransGen.refl :
      StraightReach G d s.player s.player)
  | succ i ih => exact ih.tail ⟨run.adjacent i, hG i.castSucc, hG i.succ⟩

/-- An actual push is supported all the way to its first destination hole. -/
theorem RelativeClosed.push_run (hC : RelativeClosed C G) (hs : s.Valid B)
    {n : ℕ} (run : Run B d s n) (hn : 0 < n) (hp : t.player = run.cell 1)
    (hb : t.boxes = insert (run.cell ⟨n + 1, by omega⟩) (s.boxes.erase (run.cell 1)))
    (hGs : Blocked.Excluded G s) (hGt : Blocked.Excluded G t) (ht : Supported C t)
    (i : Fin (n + 2)) : run.cell i ∈ C := by
  have hm : Move B none d s t := .push hs hn trivial run hp hb
  exact hC (players_adjacent hm) (ht _ ((mem_holes _).mp (source_player_mem_holes hm)))
    (ht _ hm.valid_target.2.2) hGs.player hGt.player _
    (straightReach_run run (Blocked.run_avoids run hGs hGt hb) i)

/-- Relative support propagates backwards through a move preserving its blockers. -/
private theorem RelativeClosed.move_source (hC : RelativeClosed C G) (hm : Move B cap d s t)
    (hGs : Blocked.Excluded G s) (hGt : Blocked.Excluded G t) (ht : Supported C t) :
    Supported C s := by
  cases hm with
  | walk _ _ _ _ hb => simpa only [Supported, hb] using ht
  | @push n hs hn _ run hp hb =>
    intro p he
    by_cases hlast : p = run.cell ⟨n + 1, by omega⟩
    · subst p
      exact hC.push_run hs run hn hp hb hGs hGt ht _
    · apply ht p
      rw [hb]
      simp only [Finset.mem_insert, Finset.mem_erase]
      exact fun h => h.elim hlast (fun h => he h.2)

/-- A terminal support may be pulled back from any final player location. -/
theorem RelativeClosed.reachable_source (hC : RelativeClosed C G)
    (hr : Relation.ReflTransGen (Blocked.ExcludingStep B cap G) s t) :
    Supported C t → Supported C s := by
  induction hr with
  | refl => exact id
  | tail _ hm ih =>
    exact fun ht => ih (hC.move_source hm.1.choose_spec hm.2.1 hm.2.2 ht)

end PushPuzzle.PushS.Support
