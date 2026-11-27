/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.Support
public import PushS.Holes

/-! Forward hole support in row- and column-convex regions. -/

public section
namespace PushPuzzle.Push

open PushFS PushS

namespace Support

variable {w h : ℕ} {C : Set (Cell w h)}

/-- Every row and column of the region is an interval. -/
def AxisConvex (C : Set (Cell w h)) : Prop :=
  ∀ (d : Direction) ⦃a b q⦄, a ∈ C → b ∈ C →
    d.lane b = d.lane a → d.lane q = d.lane a →
    d.position a ≤ d.position q → d.position q ≤ d.position b → q ∈ C

/-- A complete straight push stays between its player and destination hole. -/
theorem AxisConvex.run {B : Board w h} {d : Direction} {s : State w h} {n : ℕ}
    (hC : AxisConvex C) (r : Run B d s n) (hp : s.player ∈ C)
    (he : r.cell ⟨n + 1, by omega⟩ ∈ C) (i : Fin (n + 2)) : r.cell i ∈ C := by
  apply hC d hp he (r.lane _) (r.lane _)
  · rw [r.position]
    omega
  · rw [r.position, r.position]
    dsimp only
    have := i.isLt
    omega

/-- New holes are created inside the interval between two existing holes. -/
private theorem AxisConvex.move_target {B : Board w h} {cap : Option ℕ} {d : Direction}
    {s t : State w h} (hC : AxisConvex C) (hm : Move B cap d s t)
    (hs : PushS.Support.Supported C s) : PushS.Support.Supported C t := by
  cases hm with
  | walk _ _ _ _ hb => simpa only [PushS.Support.Supported, hb] using hs
  | push hv hn _ r _ hb =>
    intro q hq
    have hq' : q ∈ holes t := (mem_holes _).mpr hq
    rw [holes_push r hn hb, Finset.mem_insert] at hq'
    rcases hq' with rfl | hq'
    · exact hC.run r (hs _ hv.2.2) (hs _ r.empty) 1
    · exact hs _ ((mem_holes _).mp (Finset.mem_of_mem_erase hq'))

private theorem AxisConvex.step_target {B : Board w h} {cap : Option ℕ} {s t : State w h}
    (hC : AxisConvex C) (hm : Step B cap s t) :
    PushS.Support.Supported C s → PushS.Support.Supported C t :=
  hC.move_target hm.choose_spec

/-- Forward convex support holds at every prefix, independently of the final objective. -/
theorem AxisConvex.reachable_target {B : Board w h} {cap : Option ℕ} {s t : State w h}
    (hC : AxisConvex C) (hr : Reachable B cap s t)
    (hs : PushS.Support.Supported C s) : PushS.Support.Supported C t := by
  induction hr with
  | refl => exact hs
  | tail _ hm ih => exact hC.step_target hm ih

/-- A northeast quadrant has a row- and column-convex complement. -/
private theorem northeast_compl_axisConvex (x y : ℕ) :
    AxisConvex {q : Cell w h | q.1.val < x ∨ y < q.2.val} := by
  intro d a b q ha hb hl hq hlo hhi
  cases d <;> simp only [Direction.lane, Direction.position] at hl hq hlo hhi <;>
    change _ < x ∨ y < _ at ha hb ⊢ <;> omega

/-- A southeast quadrant has a row- and column-convex complement. -/
theorem southeast_compl_axisConvex (x y : ℕ) :
    AxisConvex {q : Cell w h | q.1.val < x ∨ q.2.val < y} := by
  intro d a b q ha hb hl hq hlo hhi
  cases d <;> simp only [Direction.lane, Direction.position] at hl hq hlo hhi <;>
    change _ < x ∨ _ < y at ha hb ⊢ <;> omega

/-- A northwest quadrant has a row- and column-convex complement. -/
theorem northwest_compl_axisConvex (x y : ℕ) :
    AxisConvex {q : Cell w h | x ≤ q.1.val ∨ y ≤ q.2.val} := by
  intro d a b q ha hb hl hq hlo hhi
  cases d <;> simp only [Direction.lane, Direction.position] at hl hq hlo hhi <;>
    change x ≤ _ ∨ y ≤ _ at ha hb ⊢ <;> omega

/-- An initially full northeast quadrant remains full on every actual play. -/
theorem northeast_full {B : Board w h} {cap : Option ℕ} {s t : State w h}
    (x y : ℕ) (hr : Reachable B cap s t)
    (hs : ∀ q, x ≤ q.1.val → q.2.val ≤ y → q ∈ s.boxes) :
    ∀ q, x ≤ q.1.val → q.2.val ≤ y → q ∈ t.boxes := by
  have hsupport : PushS.Support.Supported {q : Cell w h | q.1.val < x ∨ y < q.2.val} s := by
    intro q hq
    by_contra h
    change ¬(q.1.val < x ∨ y < q.2.val) at h
    exact hq (hs q (by omega) (by omega))
  have ht := (northeast_compl_axisConvex x y).reachable_target hr hsupport
  intro q hx hy
  by_contra hq
  have := ht q hq
  change q.1.val < x ∨ y < q.2.val at this
  omega

end Support
end PushPuzzle.Push
