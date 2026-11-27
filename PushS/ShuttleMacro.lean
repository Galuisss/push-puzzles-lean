/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.HoleState

/-!
# The physical five-push two-box shuttle

A horizontal window has offsets one through nine. Its two boxes move from offsets two and
three to seven and eight, consuming the five successive destination holes. Every step is a
complete run of exactly two ordinary boxes. Holes outside the window are arbitrary and fixed.
-/

public section
namespace PushPuzzle.PushS.ShuttleMacro


open PushFS

variable {w h : ℕ}

/-- Actual bounded coordinates of the short train and its two pushing positions. -/
structure Rail (w h : ℕ) where
  /-- Horizontal origin of the three-port core. -/
  x : ℕ
  /-- Actual working row. -/
  row : Fin h
  /-- All offsets through the right pushing position are on the board. -/
  fits : x + 9 < w

namespace Rail

/-- The cell at the supplied physical horizontal offset. -/
@[expose] def cell (r : Rail w h) (j : Fin 10) : Cell w h :=
  (⟨r.x + j.val, by have := r.fits; omega⟩, r.row)

private theorem cell_injective (r : Rail w h) : Function.Injective r.cell := by
  intro i j he
  have hx := congrArg (fun p : Cell w h => p.1.val) he
  change r.x + i.val = r.x + j.val at hx
  exact Fin.ext (Nat.add_left_cancel hx)

@[simp] theorem cell_eq_iff (r : Rail w h) (i j : Fin 10) : r.cell i = r.cell j ↔ i = j :=
  r.cell_injective.eq_iff

/-- The nine cells whose occupancy changes or supplies the player during the macro. -/
@[expose] def window (r : Rail w h) : Finset (Cell w h) :=
  (Finset.univ.erase 0).image r.cell

@[simp] theorem cell_mem_window (r : Rail w h) (j : Fin 10) :
    r.cell j ∈ r.window ↔ j ≠ 0 := by
  simp [window]

/-- The moving window is exactly offsets one through nine on the actual working row. -/
theorem mem_window_iff (r : Rail w h) (p : Cell w h) :
    p ∈ r.window ↔ p.2 = r.row ∧ r.x + 1 ≤ p.1.val ∧ p.1.val ≤ r.x + 9 := by
  constructor
  · intro hp
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
    have hne : j.val ≠ 0 := by
      intro he
      exact (Finset.mem_erase.mp hj).1 (Fin.ext he)
    change r.row = r.row ∧ r.x + 1 ≤ r.x + j.val ∧ r.x + j.val ≤ r.x + 9
    have := j.isLt
    exact ⟨rfl, by omega, by omega⟩
  · rintro ⟨hy, hlow, hhigh⟩
    let j : Fin 10 := ⟨p.1.val - r.x, by omega⟩
    refine Finset.mem_image.mpr ⟨j, ?_, ?_⟩
    · simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      intro he
      have hx := congrArg Fin.val he
      change p.1.val - r.x = 0 at hx
      omega
    · apply Prod.ext
      · apply Fin.ext
        change r.x + (p.1.val - r.x) = p.1.val
        omega
      · exact hy.symm

/-- The two consecutive boxes after `t` of the five rightward pushes. -/
@[expose] def pair (r : Rail w h) (t : Fin 6) : Finset (Cell w h) :=
  {r.cell ⟨t.val + 2, by omega⟩, r.cell ⟨t.val + 3, by omega⟩}

/-- Ambient holes together with the window minus the two short-train boxes. -/
@[expose] def empty (r : Rail w h) (ambient : Finset (Cell w h)) (t : Fin 6) : Finset (Cell w h) :=
  ambient ∪ (r.window \ r.pair t)

private theorem hole (r : Rail w h) (ambient : Finset (Cell w h)) (t : Fin 6)
    (j : Fin 10) (hj : j ≠ 0) (hfirst : j.val ≠ t.val + 2) (hsecond : j.val ≠ t.val + 3) :
    r.cell j ∈ r.empty ambient t := by
  apply Finset.mem_union_right
  simp [pair, Fin.ext_iff, hj, hfirst, hsecond]

private theorem ambient_off (r : Rail w h) (ambient : Finset (Cell w h))
    (ha : Disjoint ambient r.window) (j : Fin 10) (hj : j ≠ 0) : r.cell j ∉ ambient :=
  fun hp => Finset.disjoint_left.mp ha hp ((r.cell_mem_window j).mpr hj)

private theorem occupied (r : Rail w h) (ambient : Finset (Cell w h))
    (ha : Disjoint ambient r.window) (t : Fin 6) (j : Fin 10)
    (hj : j.val = t.val + 2 ∨ j.val = t.val + 3) : r.cell j ∉ r.empty ambient t := by
  have hn : j ≠ 0 := by intro he; have := congrArg Fin.val he; rcases hj with hj | hj <;> omega
  have hoff := r.ambient_off ambient ha j hn
  have hp : r.cell j ∈ r.pair t := by
    simpa only [pair, Finset.mem_insert, Finset.mem_singleton, cell_eq_iff, Fin.ext_iff] using hj
  simp [empty, hoff, hp]

/-- Position the player immediately left of the two short-train boxes. -/
@[expose] def eastState (r : Rail w h) (ambient : Finset (Cell w h)) (t : Fin 6) : HoleState w h where
  player := r.cell ⟨t.val + 1, by omega⟩
  empty := r.empty ambient t
  player_empty := by
    exact r.hole ambient t ⟨t.val + 1, by omega⟩
      (by intro he; have hx := congrArg Fin.val he; change t.val + 1 = 0 at hx; omega)
      (by change t.val + 1 ≠ t.val + 2; omega) (by change t.val + 1 ≠ t.val + 3; omega)

/-- Position the player immediately right of the same two boxes. -/
@[expose] def westState (r : Rail w h) (ambient : Finset (Cell w h)) (t : Fin 6) : HoleState w h where
  player := r.cell ⟨t.val + 4, by omega⟩
  empty := r.empty ambient t
  player_empty := by
    exact r.hole ambient t ⟨t.val + 4, by omega⟩
      (by intro he; have hx := congrArg Fin.val he; change t.val + 4 = 0 at hx; omega)
      (by change t.val + 4 ≠ t.val + 2; omega) (by change t.val + 4 ≠ t.val + 3; omega)

/-- The complete physical two-box run at any one of the five eastward stages. -/
@[expose] def eastPush (r : Rail w h) (ambient : Finset (Cell w h))
    (ha : Disjoint ambient r.window) (t : Fin 5) : (r.eastState ambient t.castSucc).Push .east where
  length := 2
  positive := by omega
  cell i := r.cell ⟨t.val + i.val + 1, by omega⟩
  start := rfl
  adjacent i := by constructor <;> rfl
  occupied i := by
    apply r.occupied ambient ha t.castSucc
    have := i.isLt
    simp only [Fin.val_castSucc]
    omega
  destination := by
    exact r.hole ambient t.castSucc ⟨t.val + 4, by omega⟩
      (by intro he; have hx := congrArg Fin.val he; change t.val + 4 = 0 at hx; omega)
      (by change t.val + 4 ≠ t.val + 2; omega) (by change t.val + 4 ≠ t.val + 3; omega)

/-- The complete physical two-box run at any one of the five westward stages. -/
@[expose] def westPush (r : Rail w h) (ambient : Finset (Cell w h))
    (ha : Disjoint ambient r.window) (t : Fin 5) : (r.westState ambient t.succ).Push .west where
  length := 2
  positive := by omega
  cell i := r.cell ⟨t.val + 5 - i.val, by omega⟩
  start := by simp [westState, cell, Nat.add_assoc]
  adjacent i := by
    constructor
    · change r.x + (t.val + 5 - (i.val + 1)) + 1 = r.x + (t.val + 5 - i.val)
      have := i.isLt
      omega
    · rfl
  occupied i := by
    apply r.occupied ambient ha t.succ
    have := i.isLt
    simp only [Fin.val_succ]
    omega
  destination := by
    exact r.hole ambient t.succ ⟨t.val + 5 - 3, by omega⟩
      (by intro he; have hx := congrArg Fin.val he; change t.val + 5 - 3 = 0 at hx; omega)
      (by change t.val + 5 - 3 ≠ t.val + 1 + 2; omega)
      (by change t.val + 5 - 3 ≠ t.val + 1 + 3; omega)

private theorem shift_holes {α : Type*} [DecidableEq α] (A W : Finset α) (a b c : α)
    (ha : a ∈ W) (hc : c ∈ W) (hA : c ∉ A)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    A ∪ (W \ {b, c}) = insert a ((A ∪ (W \ {a, b})).erase c) := by
  ext p
  by_cases hpa : p = a <;> by_cases hpb : p = b <;> by_cases hpc : p = c <;> simp_all

private theorem state_ext {s t : HoleState w h} (hp : s.player = t.player)
    (he : s.empty = t.empty) : s = t := by
  cases s
  cases t
  cases hp
  cases he
  rfl

private theorem empty_east (r : Rail w h) (ambient : Finset (Cell w h))
    (ha : Disjoint ambient r.window) (t : Fin 5) :
    r.empty ambient t.succ = insert (r.cell ⟨t.val + 2, by omega⟩)
      ((r.empty ambient t.castSucc).erase (r.cell ⟨t.val + 4, by omega⟩)) := by
  apply shift_holes
  · apply (r.cell_mem_window _).mpr
    intro he
    have hx := congrArg Fin.val he
    change t.val + 2 = 0 at hx
    omega
  · apply (r.cell_mem_window _).mpr
    intro he
    have hx := congrArg Fin.val he
    change t.val + 4 = 0 at hx
    omega
  · apply r.ambient_off ambient ha
    intro he
    have hx := congrArg Fin.val he
    change t.val + 4 = 0 at hx
    omega
  · intro he
    have hx := congrArg (fun p : Cell w h => p.1.val) he
    change r.x + (t.val + 2) = r.x + (t.val + 3) at hx
    omega
  · intro he
    have hx := congrArg (fun p : Cell w h => p.1.val) he
    change r.x + (t.val + 2) = r.x + (t.val + 4) at hx
    omega
  · intro he
    have hx := congrArg (fun p : Cell w h => p.1.val) he
    change r.x + (t.val + 3) = r.x + (t.val + 4) at hx
    omega

/-- One eastward run has exactly the next stage's player and hole set. -/
private theorem eastPush_target (r : Rail w h) (ambient : Finset (Cell w h))
    (ha : Disjoint ambient r.window) (t : Fin 5) :
    (r.eastPush ambient ha t).target = r.eastState ambient t.succ := by
  apply state_ext
  · rfl
  · exact (empty_east r ambient ha t).symm

private theorem empty_west (r : Rail w h) (ambient : Finset (Cell w h))
    (ha : Disjoint ambient r.window) (t : Fin 5) :
    r.empty ambient t.castSucc = insert (r.cell ⟨t.val + 4, by omega⟩)
      ((r.empty ambient t.succ).erase (r.cell ⟨t.val + 2, by omega⟩)) := by
  have hocc : r.cell ⟨t.val + 2, by omega⟩ ∉ r.empty ambient t.castSucc :=
    r.occupied ambient ha t.castSucc _ (Or.inl rfl)
  have hhole : r.cell ⟨t.val + 4, by omega⟩ ∈ r.empty ambient t.castSucc := by
    exact r.hole ambient t.castSucc ⟨t.val + 4, by omega⟩
      (by intro he; have hx := congrArg Fin.val he; change t.val + 4 = 0 at hx; omega)
      (by change t.val + 4 ≠ t.val + 2; omega) (by change t.val + 4 ≠ t.val + 3; omega)
  rw [empty_east r ambient ha t]
  simp [Finset.notMem_mono (Finset.erase_subset _ _) hocc,
    Finset.insert_erase hhole]

/-- One westward run has exactly the preceding stage's player and hole set. -/
private theorem westPush_target (r : Rail w h) (ambient : Finset (Cell w h))
    (ha : Disjoint ambient r.window) (t : Fin 5) :
    (r.westPush ambient ha t).target = r.westState ambient t.castSucc := by
  apply state_ext
  · apply Prod.ext
    · apply Fin.ext
      change r.x + (t.val + 5 - 1) = r.x + (t.val + 4)
      omega
    · rfl
  · change insert (r.cell ⟨t.val + 5 - 1, by omega⟩)
        ((r.empty ambient t.succ).erase (r.cell ⟨t.val + 5 - 3, by omega⟩)) = _
    have hfirst : (⟨t.val + 5 - 1, by omega⟩ : Fin 10) = ⟨t.val + 4, by omega⟩ :=
      Fin.ext (show t.val + 5 - 1 = t.val + 4 by omega)
    have hlast : (⟨t.val + 5 - 3, by omega⟩ : Fin 10) = ⟨t.val + 2, by omega⟩ :=
      Fin.ext (show t.val + 5 - 3 = t.val + 2 by omega)
    rw [hfirst, hlast]
    exact (empty_west r ambient ha t).symm

/-- Each eastward stage is a real push of its complete two-box run. -/
private theorem east_move (r : Rail w h) (ambient : Finset (Cell w h))
    (ha : Disjoint ambient r.window) (t : Fin 5) (B : Board w h) (hB : B.walls = ∅)
    (cap : Option ℕ) (hc : Permits cap 2) :
    Move B cap .east (r.eastState ambient t.castSucc).toState
      (r.eastState ambient t.succ).toState := by
  simpa only [eastPush_target] using (r.eastPush ambient ha t).move B hB cap hc

/-- Each westward stage is a real push of its complete two-box run. -/
private theorem west_move (r : Rail w h) (ambient : Finset (Cell w h))
    (ha : Disjoint ambient r.window) (t : Fin 5) (B : Board w h) (hB : B.walls = ∅)
    (cap : Option ℕ) (hc : Permits cap 2) :
    Move B cap .west (r.westState ambient t.succ).toState
      (r.westState ambient t.castSucc).toState := by
  simpa only [westPush_target] using (r.westPush ambient ha t).move B hB cap hc

/-- Five consecutive east pushes take boxes at `x+2,x+3` to `x+7,x+8`, with player `x+6`. -/
theorem east_five (r : Rail w h) (ambient : Finset (Cell w h))
    (ha : Disjoint ambient r.window) (B : Board w h) (hB : B.walls = ∅) :
    Reachable B none (r.eastState ambient 0).toState (r.eastState ambient 5).toState := by
  have walk (t : Fin 6) :
      Reachable B none (r.eastState ambient 0).toState (r.eastState ambient t).toState := by
    induction t using Fin.induction with
    | zero => exact .refl
    | succ t ih => exact ih.tail ⟨.east, r.east_move ambient ha t B hB none trivial⟩
  exact walk 5

/-- Five consecutive west pushes return the same two boxes, starting at player `x+9`
and ending at player `x+4`. -/
theorem west_five (r : Rail w h) (ambient : Finset (Cell w h))
    (ha : Disjoint ambient r.window) (B : Board w h) (hB : B.walls = ∅) :
    Reachable B none (r.westState ambient 5).toState (r.westState ambient 0).toState := by
  have walk (t : Fin 6) :
      Reachable B none (r.westState ambient t).toState (r.westState ambient 0).toState := by
    induction t using Fin.induction with
    | zero => exact .refl
    | succ t ih => exact ih.head ⟨.west, r.west_move ambient ha t B hB none trivial⟩
  exact walk 5

/-- The final eastward player is precisely six cells to the right of the origin. -/
theorem east_five_player (r : Rail w h) (ambient : Finset (Cell w h)) :
    (r.eastState ambient 5).player = r.cell 6 := rfl

/-- The final westward player is precisely four cells to the right of the origin. -/
theorem west_five_player (r : Rail w h) (ambient : Finset (Cell w h)) :
    (r.westState ambient 0).player = r.cell 4 := rfl

end Rail
end PushPuzzle.PushS.ShuttleMacro
