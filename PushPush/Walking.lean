/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.RoomSlide
public import PushPush.ReadPath

/-! Actual player walks through empty rectangular-grid intervals. -/

@[expose] public section
namespace PushPuzzle.PushPush

open PushFS (Cell State Direction Adjacent)

variable {w h : ℕ}

/-- Walking along an empty straight interval preserves the complete box set. -/
private theorem walk_straight_relation (R : State w h → State w h → Prop)
    (hwalk : ∀ (d : Direction) (a b : Cell w h) (boxes : Finset (Cell w h)),
      a ∉ boxes → Adjacent d a b → b ∉ boxes → R ⟨a, boxes⟩ ⟨b, boxes⟩)
    (boxes : Finset (Cell w h)) (d : Direction) (a b : Cell w h)
    (hlane : d.lane b = d.lane a) (hpos : d.position a ≤ d.position b)
    (hempty : ∀ p : Cell w h, d.lane p = d.lane a →
      d.position a ≤ d.position p → d.position p ≤ d.position b → p ∉ boxes) :
    Relation.ReflTransGen R ⟨a, boxes⟩ ⟨b, boxes⟩ := by
  let n := (d.position b - d.position a).toNat
  have hn : d.position b = d.position a + n := by dsimp [n]; omega
  obtain ⟨cell, hstart, hend, hadj⟩ := Doors.straight_ray d a b n hlane hn
  have hp (i : Fin (n + 1)) : d.position (cell i) = d.position a + i.val := by
    induction i using Fin.induction with
    | zero => simp only [hstart, Fin.val_zero, Int.natCast_zero, Int.add_zero]
    | succ i ih =>
      have := (hadj i).position
      change d.position (cell i.succ) = d.position (cell i.castSucc) + 1 at this
      change d.position (cell i.castSucc) = d.position a + i.val at ih
      change d.position (cell i.succ) = d.position a + (i.val + 1 : ℕ)
      omega
  have hl (i : Fin (n + 1)) : d.lane (cell i) = d.lane a := by
    induction i using Fin.induction with
    | zero => rw [hstart]
    | succ i ih => exact (hadj i).lane.trans ih
  have hem (i : Fin (n + 1)) : cell i ∉ boxes := hempty (cell i) (hl i)
    (by rw [hp]; omega) (by rw [hp]; have := i.isLt; omega)
  have path (i : Fin (n + 1)) : Relation.ReflTransGen R
      ⟨cell 0, boxes⟩ ⟨cell i, boxes⟩ := by
    induction i using Fin.induction with
    | zero => exact .refl
    | succ i ih => exact ih.tail (hwalk d _ _ boxes (hem i.castSucc) (hadj i) (hem i.succ))
  have hr := path (Fin.last n)
  simpa only [hstart, hend] using hr

private theorem walk_straight (boxes : Finset (Cell w h)) (d : Direction) (a b : Cell w h)
    (hlane : d.lane b = d.lane a) (hpos : d.position a ≤ d.position b)
    (hempty : ∀ p : Cell w h, d.lane p = d.lane a →
      d.position a ≤ d.position p → d.position p ≤ d.position b → p ∉ boxes) :
    Reachable ⟨a, boxes⟩ ⟨b, boxes⟩ :=
  walk_straight_relation Step (fun d _ _ _ hv ha he => ⟨d, .walk hv ha he rfl⟩)
    boxes d a b hlane hpos hempty

private theorem ReadPath.walk_straight (boxes : Finset (Cell w h)) (d : Direction) (a b : Cell w h)
    (hlane : d.lane b = d.lane a) (hpos : d.position a ≤ d.position b)
    (hempty : ∀ p : Cell w h, d.lane p = d.lane a →
      d.position a ≤ d.position p → d.position p ≤ d.position b → p ∉ boxes) :
    ReadPath ⟨a, boxes⟩ ⟨b, boxes⟩ :=
  walk_straight_relation ReadStep (fun d _ _ _ hv ha he => ⟨d, .walk hv ha he rfl, Or.inr rfl⟩)
    boxes d a b hlane hpos hempty

theorem walk_vertical (boxes : Finset (Cell w h)) (x : Fin w) (a b : Fin h)
    (hempty : ∀ y : Fin h, min a.val b.val ≤ y.val → y.val ≤ max a.val b.val → (x, y) ∉ boxes) :
    Reachable ⟨(x, a), boxes⟩ ⟨(x, b), boxes⟩ := by
  by_cases hab : a.val ≤ b.val
  · apply walk_straight boxes .south (x, a) (x, b) rfl (by
      change (a.val : ℤ) ≤ b.val; exact_mod_cast hab)
    intro p hl hlo hhi
    simp only [Direction.lane, Direction.position] at hl hlo hhi
    have hx : p.1 = x := Fin.ext hl
    have hy := hempty p.2 (by omega) (by omega)
    exact (Prod.ext hx.symm rfl : (x, p.2) = p) ▸ hy
  · apply walk_straight boxes .north (x, a) (x, b) rfl (by
      change -(a.val : ℤ) ≤ -(b.val : ℤ); omega)
    intro p hl hlo hhi
    simp only [Direction.lane, Direction.position] at hl hlo hhi
    have hx : p.1 = x := Fin.ext hl
    have hy := hempty p.2 (by omega) (by omega)
    exact (Prod.ext hx.symm rfl : (x, p.2) = p) ▸ hy

theorem ReadPath.walk_vertical (boxes : Finset (Cell w h)) (x : Fin w) (a b : Fin h)
    (hempty : ∀ y : Fin h, min a.val b.val ≤ y.val → y.val ≤ max a.val b.val → (x, y) ∉ boxes) :
    ReadPath ⟨(x, a), boxes⟩ ⟨(x, b), boxes⟩ := by
  by_cases hab : a.val ≤ b.val
  · apply ReadPath.walk_straight boxes .south (x, a) (x, b) rfl (by
      change (a.val : ℤ) ≤ b.val; exact_mod_cast hab)
    intro p hl hlo hhi
    simp only [Direction.lane, Direction.position] at hl hlo hhi
    have hx : p.1 = x := Fin.ext hl
    have hy := hempty p.2 (by omega) (by omega)
    exact (Prod.ext hx.symm rfl : (x, p.2) = p) ▸ hy
  · apply ReadPath.walk_straight boxes .north (x, a) (x, b) rfl (by
      change -(a.val : ℤ) ≤ -(b.val : ℤ); omega)
    intro p hl hlo hhi
    simp only [Direction.lane, Direction.position] at hl hlo hhi
    have hx : p.1 = x := Fin.ext hl
    have hy := hempty p.2 (by omega) (by omega)
    exact (Prod.ext hx.symm rfl : (x, p.2) = p) ▸ hy

end PushPuzzle.PushPush
