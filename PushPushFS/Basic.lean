/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Slide
public import PushFS.Encoding

/-! Finite-strength maximum sliding with immutable walls and exact storage. -/

@[expose] public section
namespace PushPuzzle.PushPushFS

open PushFS (Cell Direction Adjacent State Board)

variable {w h n k limit : ℕ} {B : Board w h} {d : Direction} {s t : State w h}

/-- Walls act as stationary obstacles when locating the maximum stop. -/
def blocked (B : Board w h) (s : State w h) : State w h :=
  ⟨s.player, s.boxes ∪ B.walls⟩

/-- A complete box run slides along floor until a box, wall, or boundary stops it. -/
structure Slide (B : Board w h) (d : Direction) (s : State w h) (n k : ℕ) where
  /-- The same ray with walls included among its stopping obstacles. -/
  ray : PushPush.Slide d (blocked B s) n k
  /-- Every traversed cell is floor, including every moving box. -/
  floor : ∀ i, ray.cell i ∉ B.walls

namespace Slide

/-- The complete directed ray, including the player. -/
abbrev cell (r : Slide B d s n k) := r.ray.cell
/-- The initial moving box set. -/
abbrev before (r : Slide B d s n k) := r.ray.before
/-- The moving box set translated by the full sliding distance. -/
abbrev after (r : Slide B d s n k) := r.ray.after

/-- Translate the moving boxes and preserve every other box. -/
def boxes (r : Slide B d s n k) : Finset (Cell w h) :=
  (s.boxes \ r.before) ∪ r.after

theorem occupied (r : Slide B d s n k) (i : Fin n) :
    r.cell ⟨i.val + 1, by omega⟩ ∈ s.boxes :=
  (Finset.mem_union.mp (r.ray.occupied i)).resolve_right (r.floor _)

private theorem boxes_subset (r : Slide B d s n k) : r.boxes ⊆ r.ray.boxes := by
  intro p hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr
      ⟨Finset.mem_union_left _ (Finset.mem_sdiff.mp hp).1, (Finset.mem_sdiff.mp hp).2⟩)
  · exact Finset.mem_union_right _ hp

private theorem boxes_floor (r : Slide B d s n k) (hs : Disjoint s.boxes B.walls) :
    Disjoint r.boxes B.walls := by
  apply Finset.disjoint_left.mpr
  intro p hp hw
  rcases Finset.mem_union.mp hp with hp | hp
  · exact Finset.disjoint_left.mp hs (Finset.mem_sdiff.mp hp).1 hw
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact r.floor _ hw

private theorem player_empty (r : Slide B d s n k) (hn : 0 < n) (hk : 0 < k) :
    r.cell ⟨1, by omega⟩ ∉ r.boxes :=
  fun hp => r.ray.player_empty hn hk (r.boxes_subset hp)

end Slide

/-- A legal walk or a maximum slide of at most `limit` boxes. -/
inductive Move (B : Board w h) (limit : ℕ) (d : Direction) :
    State w h → State w h → Prop
  | walk {s t : State w h} (valid : s.Valid B) (adjacent : Adjacent d s.player t.player)
      (floor : t.player ∉ B.walls) (empty : t.player ∉ s.boxes)
      (boxes : t.boxes = s.boxes) : Move B limit d s t
  | push {s t : State w h} {n k : ℕ} (valid : s.Valid B) (positive : 0 < n) (permitted : n ≤ limit)
      (distance : 0 < k) (slide : Slide B d s n k)
      (player : t.player = slide.cell ⟨1, by omega⟩)
      (boxes : t.boxes = slide.boxes) : Move B limit d s t

/-- A move in any direction. -/
def Step (B : Board w h) (limit : ℕ) (s t : State w h) : Prop :=
  ∃ d, Move B limit d s t

/-- Finite maximum-slide trajectories. -/
abbrev Reachable (B : Board w h) (limit : ℕ) := Relation.ReflTransGen (Step B limit)

private theorem Move.valid_target (hm : Move B limit d s t) : t.Valid B := by
  cases hm with
  | walk hv _ hf he hb => exact ⟨hf, hb ▸ hv.2.1, hb ▸ he⟩
  | push hv hn _ hk r hp hb =>
    exact ⟨hp ▸ r.floor _, hb ▸ r.boxes_floor hv.2.1, hp ▸ hb ▸ r.player_empty hn hk⟩

theorem Reachable.valid (hr : Reachable B limit s t) (hs : s.Valid B) : t.Valid B := by
  induction hr with
  | refl => exact hs
  | tail _ hm _ => exact hm.choose_spec.valid_target

/-- Explicit finite boards with fixed walls and equally many boxes and goals. -/
abbrev Instance := PushFS.Instance
/-- The existing dense board encoding. -/
abbrev encoding := PushFS.encoding

/-- Reach the exact target set with unrestricted final player position. -/
def Instance.Solvable (I : Instance) (limit : ℕ) : Prop :=
  ∃ t, Reachable I.board limit I.initial t ∧ t.boxes = I.board.goals

/-- PushPush-kFS at the fixed push limit. -/
def solvable (limit : ℕ) : Set Instance := {I | Instance.Solvable I limit}

end PushPuzzle.PushPushFS
