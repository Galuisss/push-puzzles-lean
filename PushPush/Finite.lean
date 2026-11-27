/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Slide

/-! Maximum sliding with a fixed bound on the initial consecutive box run. -/

public section
namespace PushPuzzle.PushPush.Finite

open PushFS (Direction Adjacent State)

variable {w h limit limit' : ℕ} {d : Direction} {s t : State w h}

/-- A walk or a maximum slide starting with at most `limit` consecutive boxes. -/
inductive Move (limit : ℕ) (d : Direction) : State w h → State w h → Prop
  | walk {s t : State w h} (valid : s.player ∉ s.boxes)
      (adjacent : Adjacent d s.player t.player)
      (empty : t.player ∉ s.boxes) (boxes : t.boxes = s.boxes) : Move limit d s t
  | push {s t : State w h} {n k : ℕ} (valid : s.player ∉ s.boxes) (positive : 0 < n)
      (bound : n ≤ limit) (distance : 0 < k) (slide : Slide d s n k)
      (player : t.player = slide.cell ⟨1, by omega⟩)
      (boxes : t.boxes = slide.boxes) : Move limit d s t

/-- One walk or bounded maximum slide in any direction. -/
@[expose] def Step (limit : ℕ) (s t : State w h) : Prop := ∃ d, Move limit d s t

/-- Finite trajectories at a fixed push limit. -/
abbrev Reachable (limit : ℕ) := Relation.ReflTransGen (@Step w h limit)

/-- Removing the push bound preserves every move. -/
private theorem Move.unlimited (hm : Move limit d s t) : PushPush.Move d s t := by
  cases hm with
  | walk hv ha he hb => exact .walk hv ha he hb
  | push hv hn _ hk r hp hb => exact .push hv hn hk r hp hb

/-- Increasing the push bound preserves every move. -/
private theorem Move.mono (hm : Move limit d s t) (hl : limit ≤ limit') : Move limit' d s t := by
  cases hm with
  | walk hv ha he hb => exact .walk hv ha he hb
  | push hv hn hb hk r hp ht => exact .push hv hn (hb.trans hl) hk r hp ht

/-- Removing the push bound preserves finite trajectories. -/
theorem Reachable.unlimited (hr : Reachable limit s t) : PushPush.Reachable s t := by
  induction hr with
  | refl => exact .refl
  | tail _ hm ih => exact ih.tail ⟨hm.choose, hm.choose_spec.unlimited⟩

/-- Increasing the push bound preserves finite trajectories. -/
theorem Reachable.mono (hr : Reachable limit s t) (hl : limit ≤ limit') :
    Reachable limit' s t := by
  induction hr with
  | refl => exact .refl
  | tail _ hm ih => exact ih.tail ⟨hm.choose, hm.choose_spec.mono hl⟩

theorem Move.valid_target (hm : Move limit d s t) : t.player ∉ t.boxes :=
  hm.unlimited.valid_target

theorem Reachable.valid (hr : Reachable limit s t) (hs : s.player ∉ s.boxes) :
    t.player ∉ t.boxes := hr.unlimited.valid hs

end PushPuzzle.PushPush.Finite
