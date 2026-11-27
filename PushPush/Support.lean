/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Boundary

/-! The occupied rectangle can only shrink along an interior trajectory. -/

@[expose] public section
namespace PushPuzzle.PushPush

open PushFS (Cell Direction Adjacent State)

variable {w h n k : ℕ} {d : Direction} {s t : State w h}

/-- Every box lies below a bound on a chosen signed coordinate. -/
def Supported (e : Direction) (b : ℤ) (s : State w h) : Prop :=
  ∀ p ∈ s.boxes, e.position p ≤ b

private theorem Slide.supported (r : Slide d s n k) (hn : 0 < n)
    (ht : ∀ p ∈ r.boxes, ¬ Boundary p) {e : Direction} {b : ℤ}
    (hs : Supported e b s) : ∀ p ∈ r.boxes, e.position p ≤ b := by
  obtain ⟨q, hq, ha⟩ := r.exists_stopper hn ht
  have hqb := hs q hq
  have hqp := ha.position
  have hql := ha.lane
  have hlastp := r.position ⟨n + k, by omega⟩
  have hlastl := r.lane ⟨n + k, by omega⟩
  intro p hp
  rcases Finset.mem_union.mp hp with hp | hp
  · exact hs p (Finset.mem_sdiff.mp hp).1
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    have hib := hs _ (r.occupied i)
    have hip := r.position ⟨i.val + 1, by omega⟩
    have hil := r.lane ⟨i.val + 1, by omega⟩
    have hjp := r.position ⟨k + i.val + 1, by omega⟩
    have hjl := r.lane ⟨k + i.val + 1, by omega⟩
    cases d <;> cases e <;>
      simp only [Direction.position, Direction.lane] at hqb hqp hql hlastp hlastl hib hip hil hjp hjl ⊢ <;>
      omega

private theorem Move.supported (hm : Move d s t) (ht : Interior t) {e : Direction} {b : ℤ}
    (hs : Supported e b s) : Supported e b t := by
  cases hm with
  | walk _ _ _ hb => simpa only [Supported, hb] using hs
  | push _ hn _ r _ hb =>
    rw [show Interior t ↔ ∀ p ∈ r.boxes, ¬ Boundary p from by rw [Interior, hb]] at ht
    unfold Supported
    rw [hb]
    exact r.supported hn ht hs

/-- Four signed-coordinate bounds give a fixed containing rectangle for every prefix. -/
theorem Reachable.supported (hr : Reachable s t) (ht : Interior t)
    {e : Direction} {b : ℤ} (hs : Supported e b s) : Supported e b t := by
  induction hr with
  | refl => exact hs
  | tail _ hm ih => exact hm.choose_spec.supported ht (ih (hm.choose_spec.interior_source ht))

end PushPuzzle.PushPush
