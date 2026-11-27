/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPushFS.Basic
public import PushPushS.Basic

/-! Maximum sliding with immutable walls and unrestricted initial box-run length. -/

@[expose] public section
namespace PushPuzzle.PushPushFS.Unlimited

open PushFS (Cell Direction Adjacent State Board)

variable {w h n k : ℕ} {B : Board w h} {d : Direction} {s t : State w h}

/-- A legal walk or a maximum slide of the complete initial box run. -/
inductive Move (B : Board w h) (d : Direction) : State w h → State w h → Prop
  | walk {s t : State w h} (valid : s.Valid B) (adjacent : Adjacent d s.player t.player)
      (floor : t.player ∉ B.walls) (empty : t.player ∉ s.boxes)
      (boxes : t.boxes = s.boxes) : Move B d s t
  | push {s t : State w h} {n k : ℕ} (valid : s.Valid B) (positive : 0 < n)
      (distance : 0 < k) (slide : Slide B d s n k)
      (player : t.player = slide.cell ⟨1, by omega⟩)
      (boxes : t.boxes = slide.boxes) : Move B d s t

/-- One maximum-slide move in any direction. -/
def Step (B : Board w h) (s t : State w h) : Prop := ∃ d, Move B d s t

/-- Finite trajectories of unrestricted-strength maximum slides. -/
abbrev Reachable (B : Board w h) := Relation.ReflTransGen (Step B)

/-- Every ray fits in the board, so its area bounds every legal initial box run. -/
theorem move_finite_iff : Move B d s t ↔ PushPushFS.Move B (w * h) d s t := by
  constructor <;> intro hm
  · cases hm with
    | walk hv ha hf he hb => exact .walk hv ha hf he hb
    | push hv hn hk r hp hb =>
      have hr := Fintype.card_le_of_injective r.ray.cell r.ray.injective
      simp only [Fintype.card_fin, Fintype.card_prod] at hr
      exact .push hv hn (by omega) hk r hp hb
  · cases hm with
    | walk hv ha hf he hb => exact .walk hv ha hf he hb
    | push hv hn _ hk r hp hb => exact .push hv hn hk r hp hb

theorem step_finite_iff : Step B s t ↔ PushPushFS.Step B (w * h) s t :=
  exists_congr fun _ => move_finite_iff

/-- The board-area bound preserves precisely the unrestricted trajectories. -/
theorem reachable_finite_iff : Reachable B s t ↔ PushPushFS.Reachable B (w * h) s t := by
  constructor <;> intro hr
  · induction hr with
    | refl => exact .refl
    | tail _ hm ih => exact ih.tail ⟨hm.choose, move_finite_iff.mp hm.choose_spec⟩
  · induction hr with
    | refl => exact .refl
    | tail _ hm ih => exact ih.tail ⟨hm.choose, move_finite_iff.mpr hm.choose_spec⟩

theorem Reachable.valid (hr : Reachable B s t) (hs : s.Valid B) : t.Valid B :=
  (reachable_finite_iff.mp hr).valid hs

private def slideOfWallFree (hw : B.walls = ∅) (r : PushPush.Slide d s n k) :
    Slide B d s n k where
  ray := {
    cell := r.cell
    start := r.start
    adjacent := r.adjacent
    occupied := by simpa only [blocked, hw, Finset.union_empty] using r.occupied
    clear := by simpa only [blocked, hw, Finset.union_empty] using r.clear
    stopped := by simpa only [blocked, hw, Finset.union_empty] using r.stopped }
  floor := by simp [hw]

private def slideWithoutWalls (hw : B.walls = ∅) (r : Slide B d s n k) :
    PushPush.Slide d s n k where
  cell := r.cell
  start := r.ray.start
  adjacent := r.ray.adjacent
  occupied := r.occupied
  clear := by simpa only [blocked, hw, Finset.union_empty] using r.ray.clear
  stopped := by simpa only [blocked, hw, Finset.union_empty] using r.ray.stopped

private theorem move_wallFree_iff (hw : B.walls = ∅) :
    Move B d s t ↔ PushPush.Move d s t := by
  constructor <;> intro hm
  · cases hm with
    | walk hv ha _ he hb => exact .walk hv.2.2 ha he hb
    | push hv hn hk r hp hb => exact .push hv.2.2 hn hk (slideWithoutWalls hw r) hp hb
  · cases hm with
    | walk hv ha he hb => exact .walk ⟨by simp [hw], by simp [hw], hv⟩ ha (by simp [hw]) he hb
    | push hv hn hk r hp hb =>
      exact .push ⟨by simp [hw], by simp [hw], hv⟩ hn hk (slideOfWallFree hw r) hp hb

/-- Removing an empty wall set preserves every player position and box set. -/
theorem reachable_wallFree_iff (hw : B.walls = ∅) :
    Reachable B s t ↔ PushPush.Reachable s t := by
  constructor <;> intro hr
  · induction hr with
    | refl => exact .refl
    | tail _ hm ih => exact ih.tail ⟨hm.choose, (move_wallFree_iff hw).mp hm.choose_spec⟩
  · induction hr with
    | refl => exact .refl
    | tail _ hm ih => exact ih.tail ⟨hm.choose, (move_wallFree_iff hw).mpr hm.choose_spec⟩

/-- Exact storage with a fixed wall set and unrestricted push strength. -/
def Solvable (I : Instance) : Prop :=
  ∃ t, Reachable I.board I.initial t ∧ t.boxes = I.board.goals

/-- The PushPush-*FS decision problem. -/
def solvable : Set Instance := {I | Solvable I}

/-- Empty-wall storage has exactly the original wall-free solutions. -/
theorem solvable_wallFree_iff (I : PushS.Instance) :
    Solvable I.toInstance ↔ PushPushS.Instance.Solvable I := by
  constructor <;> rintro ⟨t, hr, hg⟩
  · exact ⟨t, (reachable_wallFree_iff I.walls_empty).mp hr, hg⟩
  · exact ⟨t, (reachable_wallFree_iff I.walls_empty).mpr hr, hg⟩

end PushPuzzle.PushPushFS.Unlimited
