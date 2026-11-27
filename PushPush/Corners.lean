/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Slide

/-! A box in the true southeast corner stays there under maximum sliding. -/

@[expose] public section
namespace PushPuzzle.PushPush

open PushFS (Cell State Direction)

variable {w h : ℕ} {s t : State w h} {d : Direction} {p : Cell w h}

private theorem Move.southeast_box (hm : Move d s t) (hx : p.1.val + 1 = w)
    (hy : p.2.val + 1 = h) (hp : p ∈ s.boxes) : p ∈ t.boxes := by
  cases hm with
  | walk _ _ _ hb => exact hb ▸ hp
  | @push n k _ _ hk slide _ hb =>
    rw [hb]
    apply Finset.mem_union_left
    apply Finset.mem_sdiff.mpr
    refine ⟨hp, ?_⟩
    intro hm
    obtain ⟨i, _, he⟩ := Finset.mem_image.mp hm
    have ha := slide.position ⟨i.val + 1, by omega⟩
    have hb := slide.position ⟨k + i.val + 1, by omega⟩
    rw [he] at ha
    dsimp only at ha hb
    cases d <;> simp only [Direction.position] at ha hb <;> omega

private theorem Reachable.southeast_box (hr : Reachable s t) (hx : p.1.val + 1 = w)
    (hy : p.2.val + 1 = h) (hp : p ∈ s.boxes) : p ∈ t.boxes := by
  induction hr with
  | refl => exact hp
  | tail _ hm ih => exact hm.choose_spec.southeast_box hx hy ih

theorem Reachable.southeast_empty (hr : Reachable s t) (hx : p.1.val + 1 = w)
    (hy : p.2.val + 1 = h) (ht : p ∉ t.boxes) : p ∉ s.boxes :=
  fun hp => ht (hr.southeast_box hx hy hp)

end PushPuzzle.PushPush
