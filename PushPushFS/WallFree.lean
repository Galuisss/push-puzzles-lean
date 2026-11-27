/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPushFS.Basic
public import PushPushS.FiniteBasic

/-! Empty-wall instances preserve the complete finite-strength maximum-slide semantics. -/

@[expose] public section
namespace PushPuzzle.PushPushFS

open PushFS (Cell Direction Adjacent State Board)

variable {w h n k limit : ℕ} {B : Board w h} {d : Direction} {s t : State w h}

private def Slide.ofWallFree (hw : B.walls = ∅) (r : PushPush.Slide d s n k) :
    Slide B d s n k where
  ray := {
    cell := r.cell
    start := r.start
    adjacent := r.adjacent
    occupied := by simpa only [blocked, hw, Finset.union_empty] using r.occupied
    clear := by simpa only [blocked, hw, Finset.union_empty] using r.clear
    stopped := by simpa only [blocked, hw, Finset.union_empty] using r.stopped }
  floor := by simp [hw]

private def Slide.withoutWalls (hw : B.walls = ∅) (r : Slide B d s n k) :
    PushPush.Slide d s n k where
  cell := r.cell
  start := r.ray.start
  adjacent := r.ray.adjacent
  occupied := r.occupied
  clear := by simpa only [blocked, hw, Finset.union_empty] using r.ray.clear
  stopped := by simpa only [blocked, hw, Finset.union_empty] using r.ray.stopped

/-- With no walls, the same actual move has precisely the wall-free semantics. -/
private theorem move_wallFree_iff (hw : B.walls = ∅) :
    Move B limit d s t ↔ PushPush.Finite.Move limit d s t := by
  constructor
  · intro hm
    cases hm with
    | walk hv ha _ he hb => exact .walk hv.2.2 ha he hb
    | push hv hn hl hk r hp hb =>
      exact .push hv.2.2 hn hl hk (r.withoutWalls hw) hp hb
  · intro hm
    cases hm with
    | walk hv ha he hb => exact .walk ⟨by simp [hw], by simp [hw], hv⟩ ha (by simp [hw]) he hb
    | push hv hn hl hk r hp hb =>
      exact .push ⟨by simp [hw], by simp [hw], hv⟩ hn hl hk (.ofWallFree hw r) hp hb

/-- Empty-wall trajectories preserve every player position and box set. -/
private theorem reachable_wallFree_iff (hw : B.walls = ∅) :
    Reachable B limit s t ↔ PushPush.Finite.Reachable limit s t := by
  constructor <;> intro hr
  · induction hr with
    | refl => exact .refl
    | tail _ hm ih => exact ih.tail ⟨hm.choose, (move_wallFree_iff hw).mp hm.choose_spec⟩
  · induction hr with
    | refl => exact .refl
    | tail _ hm ih => exact ih.tail ⟨hm.choose, (move_wallFree_iff hw).mpr hm.choose_spec⟩

/-- The wall-free storage instance is unchanged when viewed as a fixed-wall instance. -/
theorem solvable_wallFree_iff (I : PushS.Instance) (limit : ℕ) :
    Instance.Solvable I.toInstance limit ↔ PushPushS.Instance.SolvableFinite I limit := by
  constructor <;> rintro ⟨t, hr, hg⟩
  · exact ⟨t, (reachable_wallFree_iff I.walls_empty).mp hr, hg⟩
  · exact ⟨t, (reachable_wallFree_iff I.walls_empty).mpr hr, hg⟩

end PushPuzzle.PushPushFS
