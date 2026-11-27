/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Placement
public import Mathlib.Data.Fin.Rev

/-!
# Exact grid rotations and reflections for every push limit

Cell and direction equivalences preserve the complete maximal occupied run,
its length, the exact player state and the unlabelled target set. The same
maps give an isomorphism of the wall-induced static displacement graphs.
-/

@[expose] public section

namespace PushPuzzle.PushFS


variable {w h W H w' h' : ℕ}

/-- A bijective rectangular grid map preserving all four labelled adjacencies. -/
structure GridIsometry (w h W H : ℕ) where
  cells : Cell w h ≃ Cell W H
  directions : Direction ≃ Direction
  adjacent : ∀ d p q, Adjacent (directions d) (cells p) (cells q) ↔ Adjacent d p q

namespace GridIsometry

def refl (w h : ℕ) : GridIsometry w h w h := ⟨Equiv.refl _, Equiv.refl _, by simp⟩

def symm (e : GridIsometry w h W H) : GridIsometry W H w h where
  cells := e.cells.symm
  directions := e.directions.symm
  adjacent d p q := by
    simpa using (e.adjacent (e.directions.symm d) (e.cells.symm p) (e.cells.symm q)).symm

def trans (e : GridIsometry w h W H) (f : GridIsometry W H w' h') : GridIsometry w h w' h' where
  cells := e.cells.trans f.cells
  directions := e.directions.trans f.directions
  adjacent d p q := (f.adjacent (e.directions d) (e.cells p) (e.cells q)).trans (e.adjacent d p q)

def transposeDirection : Direction → Direction
  | .north => .west
  | .east => .south
  | .south => .east
  | .west => .north

def transpose (w h : ℕ) : GridIsometry w h h w where
  cells := Equiv.prodComm _ _
  directions := ⟨transposeDirection, transposeDirection,
    by intro d; cases d <;> rfl, by intro d; cases d <;> rfl⟩
  adjacent d p q := by
    cases d <;> simp [Adjacent, transposeDirection, Fin.ext_iff] <;> omega

def reflectDirection : Direction → Direction
  | .north => .north
  | .east => .west
  | .south => .south
  | .west => .east

def reflectX (w h : ℕ) : GridIsometry w h w h where
  cells := Equiv.prodCongr Fin.revPerm (Equiv.refl _)
  directions := ⟨reflectDirection, reflectDirection,
    by intro d; cases d <;> rfl, by intro d; cases d <;> rfl⟩
  adjacent d p q := by
    have hp := p.1.isLt
    have hq := q.1.isLt
    cases d <;> simp [Adjacent, reflectDirection, Fin.ext_iff, Fin.revPerm, Fin.rev] <;> omega

def board (e : GridIsometry w h W H) (B : Board w h) : Board W H :=
  ⟨B.walls.map e.cells.toEmbedding, B.goals.map e.cells.toEmbedding⟩

def state (e : GridIsometry w h W H) (s : State w h) : State W H :=
  ⟨e.cells s.player, s.boxes.map e.cells.toEmbedding⟩

theorem board_trans (e : GridIsometry w h W H) (f : GridIsometry W H w' h') (B : Board w h) :
    f.board (e.board B) = (e.trans f).board B := by
  simp only [board, Finset.map_map]
  rfl

theorem state_trans (e : GridIsometry w h W H) (f : GridIsometry W H w' h') (s : State w h) :
    f.state (e.state s) = (e.trans f).state s := by
  simp only [state, Finset.map_map]
  rfl

@[simp] theorem mem_walls (e : GridIsometry w h W H) (B : Board w h) (p : Cell w h) :
    e.cells p ∈ (e.board B).walls ↔ p ∈ B.walls := by simp [board]

@[simp] theorem mem_goals (e : GridIsometry w h W H) (B : Board w h) (p : Cell w h) :
    e.cells p ∈ (e.board B).goals ↔ p ∈ B.goals := by simp [board]

@[simp] theorem mem_boxes (e : GridIsometry w h W H) (s : State w h) (p : Cell w h) :
    e.cells p ∈ (e.state s).boxes ↔ p ∈ s.boxes := by simp [state]

@[simp] theorem board_symm (e : GridIsometry w h W H) (B : Board w h) :
    e.symm.board (e.board B) = B := by
  apply Board.ext <;> ext p <;> simp [board, symm]

@[simp] theorem state_symm (e : GridIsometry w h W H) (s : State w h) :
    e.symm.state (e.state s) = s := by
  apply State.ext
  · simp [state, symm]
  · ext p; simp [state, symm]

theorem valid_state (e : GridIsometry w h W H) {B : Board w h} {s : State w h}
    (hs : s.Valid B) : (e.state s).Valid (e.board B) := by
  refine ⟨fun hp => hs.1 ((e.mem_walls B _).mp hp), ?_, ?_⟩
  · apply Finset.disjoint_left.mpr
    intro p hp hw
    obtain ⟨q, rfl⟩ := e.cells.surjective p
    exact Finset.disjoint_left.mp hs.2.1 ((e.mem_boxes s q).mp hp) ((e.mem_walls B q).mp hw)
  · exact fun hp => hs.2.2 ((e.mem_boxes s _).mp hp)

/-- Every occupied cell, its support and the first empty destination are transported together. -/
private def run (e : GridIsometry w h W H) {B : Board w h} {s : State w h}
    {d : Direction} {n : ℕ} (r : Run B d s n) :
    Run (e.board B) (e.directions d) (e.state s) n where
  cell i := e.cells (r.cell i)
  start := congrArg e.cells r.start
  adjacent i := (e.adjacent _ _ _).mpr (r.adjacent i)
  occupied i := (e.mem_boxes _ _).mpr (r.occupied i)
  empty hp := r.empty ((e.mem_boxes _ _).mp hp)
  floor i hp := r.floor i ((e.mem_walls _ _).mp hp)

/-- An actual move retains the push length and cap under reorientation. -/
theorem move (e : GridIsometry w h W H) {B : Board w h} {cap : Option ℕ}
    {s t : State w h} {d : Direction} (hm : Move B cap d s t) :
    Move (e.board B) cap (e.directions d) (e.state s) (e.state t) := by
  cases hm with
  | walk hv ha hf he hb =>
    exact .walk (e.valid_state hv) ((e.adjacent _ _ _).mpr ha)
      (fun hp => hf ((e.mem_walls _ _).mp hp))
      (fun hp => he ((e.mem_boxes _ _).mp hp)) (by simp only [state, hb])
  | push hv hn hc r hp hb =>
    apply Move.push (e.valid_state hv) hn hc (e.run r)
    · exact congrArg e.cells hp
    · simp only [state, hb, Finset.map_insert, Finset.map_erase, run]
      rfl

/-- Transport every exact player state and every box of any finite trajectory. -/
theorem reachable (e : GridIsometry w h W H) {B : Board w h} {cap : Option ℕ}
    {s t : State w h} (hr : Reachable B cap s t) :
    Reachable (e.board B) cap (e.state s) (e.state t) :=
  hr.lift e.state (fun _ _ ⟨d, hd⟩ => ⟨e.directions d, e.move hd⟩)

theorem reachable_iff (e : GridIsometry w h W H) (B : Board w h) (cap : Option ℕ)
    (s t : State w h) :
    Reachable (e.board B) cap (e.state s) (e.state t) ↔ Reachable B cap s t := by
  constructor
  · intro hr
    simpa only [board_symm, state_symm] using e.symm.reachable hr
  · exact e.reachable

/-- A full grid isometry is also an adjacency-preserving rectangle placement. -/
def embedding (e : GridIsometry w h W H) : GridEmbedding w h W H where
  cells := e.cells.toEmbedding
  direction := e.directions
  adjacent d p q := (e.adjacent d p q).mpr

private theorem wallsAgree (e : GridIsometry w h W H) (B : Board w h) :
    e.embedding.WallsAgree B (e.board B) := e.mem_walls B

/-- The wall-only static graph is transported using the same geometric map. -/
private theorem displacement (e : GridIsometry w h W H) {B : Board w h} {p q : Cell w h}
    (hd : Displacement B p q) : Displacement (e.board B) (e.cells p) (e.cells q) :=
  GridEmbedding.displacement (e.wallsAgree B) hd

theorem displacement_iff (e : GridIsometry w h W H) (B : Board w h) (p q : Cell w h) :
    Displacement (e.board B) (e.cells p) (e.cells q) ↔ Displacement B p q := by
  constructor
  · intro hd
    have hr := e.symm.displacement hd
    simp only [board_symm] at hr
    simpa only [symm, Equiv.symm_apply_apply] using hr
  · exact e.displacement

private theorem staticReach (e : GridIsometry w h W H) {B : Board w h} {p q : Cell w h}
    (hr : StaticReach B p q) : StaticReach (e.board B) (e.cells p) (e.cells q) :=
  hr.lift e.cells (fun _ _ hd => e.displacement hd)

private theorem staticReach_iff (e : GridIsometry w h W H) (B : Board w h) (p q : Cell w h) :
    StaticReach (e.board B) (e.cells p) (e.cells q) ↔ StaticReach B p q := by
  constructor
  · intro hr
    have hh := e.symm.staticReach hr
    rw [e.board_symm B] at hh
    simpa only [symm, Equiv.symm_apply_apply] using hh
  · exact e.staticReach

/-- Static SCC identity has its exact original meaning after reorientation. -/
theorem sameComponent_iff (e : GridIsometry w h W H) (B : Board w h) (p q : Cell w h) :
    SameComponent (e.board B) (e.cells p) (e.cells q) ↔ SameComponent B p q :=
  and_congr (e.staticReach_iff B p q) (e.staticReach_iff B q p)

/-- Reorient all walls, boxes, targets and the actual starting player. -/
def reorientInstance (I : Instance) (e : GridIsometry I.width I.height W H) : Instance where
  width := W
  height := H
  board := e.board I.board
  initial := e.state I.initial
  goals_floor := by
    apply Finset.disjoint_left.mpr
    intro p hp hg
    obtain ⟨q, rfl⟩ := e.cells.surjective p
    exact Finset.disjoint_left.mp I.goals_floor ((e.mem_walls _ _).mp hp) ((e.mem_goals _ _).mp hg)
  initial_valid := e.valid_state I.initial_valid
  boxes_eq_goals := by simpa [state, board] using I.boxes_eq_goals

/-- Reflection across a horizontal line. -/
def reflectY (w h : ℕ) : GridIsometry w h w h :=
  ((transpose w h).trans (reflectX h w)).trans (transpose h w)

/-- A clockwise quarter turn. -/
def clockwise (w h : ℕ) : GridIsometry w h h w :=
  (transpose w h).trans (reflectX h w)

end GridIsometry

namespace GridEmbedding

/-- Compose a reoriented local placement with its global rectangle placement. -/
def trans (e : GridEmbedding w h W H) (f : GridEmbedding W H w' h') : GridEmbedding w h w' h' where
  cells := e.cells.trans f.cells
  direction := f.direction ∘ e.direction
  adjacent d p q hp := f.adjacent _ _ _ (e.adjacent d p q hp)

end GridEmbedding
end PushPuzzle.PushFS
