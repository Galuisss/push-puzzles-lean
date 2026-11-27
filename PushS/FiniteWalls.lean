/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteBasic
public import PushS.FiniteFreeze

/-! Replacing thick fixed walls by ordinary boxes and storage targets. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteWalls

open PushFS

variable {w h k n : ℕ} {B : Board w h} {d : Direction} {s t : State w h}

/-- Remove the wall flags and store an additional box at every former wall. -/
def board (B : Board w h) : Board w h := ⟨∅, B.goals ∪ B.walls⟩

/-- Keep the player and add the wall boxes. -/
def fill (B : Board w h) (s : State w h) : State w h :=
  ⟨s.player, s.boxes ∪ B.walls⟩

/-- Remove the frozen wall boxes from a physical state. -/
def clear (B : Board w h) (s : State w h) : State w h :=
  ⟨s.player, s.boxes \ B.walls⟩

private theorem clear_fill (hs : s.Valid B) : clear B (fill B s) = s := by
  refine State.ext (by rfl) ?_
  change (s.boxes ∪ B.walls) \ B.walls = s.boxes
  ext p
  have hd := Finset.disjoint_left.mp hs.2.1
  simp only [Finset.mem_sdiff, Finset.mem_union]
  exact ⟨fun hp => hp.1.resolve_right hp.2, fun hp => ⟨Or.inl hp, hd hp⟩⟩

theorem fill_valid (hs : s.Valid B) : (fill B s).Valid (board B) := by
  refine ⟨Finset.notMem_empty _, Finset.disjoint_empty_right _, ?_⟩
  exact fun hp => (Finset.mem_union.mp hp).elim hs.2.2 hs.1

private theorem clear_valid (hs : s.Valid (board B)) (hfull : B.walls ⊆ s.boxes) :
    (clear B s).Valid B := by
  refine ⟨fun hp => hs.2.2 (hfull hp), ?_, ?_⟩
  · exact Finset.disjoint_left.mpr fun p hp hw => (Finset.mem_sdiff.mp hp).2 hw
  · exact fun hp => hs.2.2 (Finset.mem_sdiff.mp hp).1

private def fillRun (r : Run B d s n) : Run (board B) d (fill B s) n where
  cell := r.cell
  start := r.start
  adjacent := r.adjacent
  occupied i := Finset.mem_union_left _ (r.occupied i)
  empty hp := (Finset.mem_union.mp hp).elim r.empty (r.floor _)
  floor _ := Finset.notMem_empty _

/-- Every original move uses the same cells after the walls are filled. -/
private theorem move_fill {cap : Option ℕ} (hm : Move B cap d s t) :
    Move (board B) cap d (fill B s) (fill B t) := by
  cases hm with
  | walk hv ha hf he hb =>
    exact .walk (fill_valid hv) ha (Finset.notMem_empty _)
      (fun hp => (Finset.mem_union.mp hp).elim he hf) (congrArg (· ∪ B.walls) hb)
  | push hv hn hc r hp hb =>
    refine .push (fill_valid hv) hn hc (fillRun r) hp ?_
    change t.boxes ∪ B.walls = insert (r.cell _) ((s.boxes ∪ B.walls).erase (r.cell 1))
    rw [hb, Finset.erase_union_distrib, Finset.erase_eq_of_notMem (r.floor 1),
      Finset.insert_union]

theorem reachable_fill {cap : Option ℕ} (hr : Reachable B cap s t) :
    Reachable (board B) cap (fill B s) (fill B t) := by
  induction hr with
  | refl => exact .refl
  | tail _ hm ih => exact ih.tail ⟨hm.choose, move_fill hm.choose_spec⟩

private def clearRun (hW : FiniteFreeze.Thick k B.walls)
    (hs : s.Valid (board B)) (hfull : B.walls ⊆ s.boxes)
    (r : Run (board B) d s n) (hn : n ≤ k) : Run B d (clear B s) n where
  cell := r.cell
  start := r.start
  adjacent := r.adjacent
  occupied i := Finset.mem_sdiff.mpr
    ⟨r.occupied i, FiniteFreeze.run_avoids hW hs hfull r hn _⟩
  empty hp := r.empty (Finset.mem_sdiff.mp hp).1
  floor i := FiniteFreeze.run_avoids hW hs hfull r hn i

/-- A bounded move projects back to the fixed-wall board. -/
private theorem move_clear (hW : FiniteFreeze.Thick k B.walls)
    (hm : Move (board B) (some k) d s t) (hfull : B.walls ⊆ s.boxes) :
    Move B (some k) d (clear B s) (clear B t) := by
  cases hm with
  | walk hv ha _ he hb =>
    refine .walk (clear_valid hv hfull) ha ?_
      (fun hp => he (Finset.mem_sdiff.mp hp).1) (congrArg (· \ B.walls) hb)
    exact fun hp => he (hfull hp)
  | @push n hv hn hc r hp hb =>
    refine .push (clear_valid hv hfull) hn hc (clearRun hW hv hfull r hc) hp ?_
    change t.boxes \ B.walls = insert (r.cell _) ((s.boxes \ B.walls).erase (r.cell 1))
    rw [hb]
    ext p
    have ha := FiniteFreeze.run_avoids hW hv hfull r hc ⟨n + 1, by omega⟩
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨hp | hp, hw⟩
      · exact Or.inl hp
      · exact Or.inr ⟨hp.1, hp.2, hw⟩
    · rintro (hp | hp)
      · exact ⟨Or.inl hp, hp ▸ ha⟩
      · exact ⟨Or.inr ⟨hp.1, hp.2.1⟩, hp.2.2⟩

/-- Thick wall boxes stay fixed along the entire projected trajectory. -/
private theorem reachable_clear (hW : FiniteFreeze.Thick k B.walls)
    (hr : Reachable (board B) (some k) s t) (hfull : B.walls ⊆ s.boxes) :
    Reachable B (some k) (clear B s) (clear B t) := by
  induction hr with
  | refl => exact .refl
  | tail hr hm ih =>
    exact ih.tail ⟨hm.choose, move_clear hW hm.choose_spec
      (FiniteFreeze.reachable_full hW hr hfull)⟩

/-- The total wall-filling compiler retains the rectangle and the exact player. -/
noncomputable def fillWalls (I : PushFS.Instance) : PushS.Instance :=
  Instance.ofState (I.board.goals ∪ I.board.walls) (fill I.board I.initial)
    (fill_valid I.initial_valid).2.2 (by
      change (I.initial.boxes ∪ I.board.walls).card = (I.board.goals ∪ I.board.walls).card
      rw [Finset.card_union_of_disjoint I.initial_valid.2.1,
        Finset.card_union_of_disjoint I.goals_floor.symm, I.boxes_eq_goals])

/-- Filling thick walls preserves solvability at the specified finite push limit. -/
theorem fillWalls_solvable_iff (I : PushFS.Instance)
    (hW : FiniteFreeze.Thick k I.board.walls) :
    (fillWalls I).SolvableFinite k ↔ I.Solvable (some k) := by
  change (∃ t : State I.width I.height,
    Reachable (board I.board) (some k) (fill I.board I.initial) t ∧
      t.boxes = I.board.goals ∪ I.board.walls) ↔ I.Solvable (some k)
  constructor
  · rintro ⟨t, hr, ht⟩
    have hr' : Reachable (board I.board) (some k) (fill I.board I.initial) t := hr
    have hc := reachable_clear hW hr' (Finset.subset_union_right)
    rw [clear_fill I.initial_valid] at hc
    refine ⟨clear I.board t, hc, ?_⟩
    change t.boxes \ I.board.walls = I.board.goals
    change t.boxes = I.board.goals ∪ I.board.walls at ht
    rw [ht]
    ext p
    have hd := Finset.disjoint_left.mp I.goals_floor.symm
    simp only [Finset.mem_sdiff, Finset.mem_union]
    exact ⟨fun hp => hp.1.resolve_right hp.2, fun hp => ⟨Or.inl hp, hd hp⟩⟩
  · rintro ⟨t, hr, ht⟩
    exact ⟨fill I.board t, reachable_fill hr, congrArg (· ∪ I.board.walls) ht⟩

end PushPuzzle.PushS.FiniteWalls
