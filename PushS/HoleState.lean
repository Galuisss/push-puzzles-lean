/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.Holes

/-! Hole-set constructions produce genuine wall-free storage instances and legal pushes. -/

@[expose] public section
namespace PushPuzzle.PushS

open PushFS

/-- A complete wall-free configuration specified by holes rather than boxes. -/
structure HoleState (w h : ℕ) where
  player : Cell w h
  empty : Finset (Cell w h)
  player_empty : player ∈ empty

namespace HoleState
variable {w h : ℕ}

/-- Every cell not explicitly left empty contains an ordinary box. -/
def toState (s : HoleState w h) : State w h := ⟨s.player, s.emptyᶜ⟩

@[simp] theorem holes_toState (s : HoleState w h) : holes s.toState = s.empty := by
  simp [holes, toState]

theorem valid (s : HoleState w h) (B : Board w h) (hB : B.walls = ∅) : s.toState.Valid B := by
  simp [State.Valid, toState, hB, s.player_empty]

/-- Walk to an adjacent hole without altering the empty set. -/
def walk (s : HoleState w h) (p : Cell w h) (hp : p ∈ s.empty) : HoleState w h :=
  ⟨p, s.empty, hp⟩

theorem walk_move (s : HoleState w h) {d : Direction} {p : Cell w h}
    (hp : p ∈ s.empty) (ha : Adjacent d s.player p)
    (B : Board w h) (hB : B.walls = ∅) (cap : Option ℕ) :
    Move B cap d s.toState (s.walk p hp).toState :=
  .walk (s.valid B hB) ha (by simp [hB]) (by simpa [toState, walk] using hp) rfl

/-- A complete ray from the player through occupied cells to its first destination hole. -/
structure Push (s : HoleState w h) (d : Direction) where
  length : ℕ
  positive : 0 < length
  cell : Fin (length + 2) → Cell w h
  start : cell 0 = s.player
  adjacent : ∀ i : Fin (length + 1), Adjacent d (cell i.castSucc) (cell i.succ)
  occupied : ∀ i : Fin length, cell ⟨i.val + 1, by omega⟩ ∉ s.empty
  destination : cell ⟨length + 1, by omega⟩ ∈ s.empty

/-- Transport the first hole to the neighbouring box cell. -/
def Push.target {s : HoleState w h} {d : Direction} (r : s.Push d) : HoleState w h where
  player := r.cell 1
  empty := insert (r.cell 1) (s.empty.erase (r.cell ⟨r.length + 1, by omega⟩))
  player_empty := Finset.mem_insert_self _ _

private def Push.run {s : HoleState w h} {d : Direction} (r : s.Push d)
    (B : Board w h) (hB : B.walls = ∅) : Run B d s.toState r.length where
  cell := r.cell
  start := r.start
  adjacent := r.adjacent
  occupied i := Finset.mem_compl.mpr (r.occupied i)
  empty := by simpa [toState] using r.destination
  floor _ := by simp [hB]

/-- The hole update performs the exact complete box-column push in the common semantics. -/
theorem Push.move {s : HoleState w h} {d : Direction} (r : s.Push d)
    (B : Board w h) (hB : B.walls = ∅) (cap : Option ℕ) (hc : Permits cap r.length) :
    Move B cap d s.toState r.target.toState := by
  refine .push (s.valid B hB) r.positive hc (r.run B hB) rfl ?_
  change (insert (r.cell 1) (s.empty.erase (r.cell _)))ᶜ =
    insert (r.cell _) (s.emptyᶜ.erase (r.cell 1))
  have hfirst : r.cell 1 ∉ s.empty := by
    have h := (r.run B hB).first_occupied r.positive
    exact Finset.mem_compl.mp h
  have hlast := r.destination
  ext p
  simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_erase]
  by_cases hp : p = r.cell 1
  · subst p
    have hne : r.cell 1 ≠ r.cell ⟨r.length + 1, by omega⟩ :=
      fun he => hfirst (he ▸ hlast)
    simp [hne]
  · simp only [hp, false_or]
    tauto

/-- Unlimited pushing accepts every positive complete ray. -/
theorem Push.step {s : HoleState w h} {d : Direction} (r : s.Push d)
    (B : Board w h) (hB : B.walls = ∅) : Step B none s.toState r.target.toState :=
  ⟨d, r.move B hB none trivial⟩

end HoleState

/-- Compile equal-sized initial and target hole sets into an explicit wall-free instance. -/
def Instance.ofHoles {w h : ℕ} (initial : HoleState w h) (target : Finset (Cell w h))
    (hcard : initial.empty.card = target.card) : Instance :=
  Instance.ofState targetᶜ initial.toState
    (by simpa [HoleState.toState] using initial.player_empty)
    (by simp [HoleState.toState, Finset.card_compl, hcard])

end PushPuzzle.PushS
