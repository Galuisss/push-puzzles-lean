/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Encoding
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Equiv.Fin.Basic

/-! Fixed-width row-major dynamic state words, with one box and one player bit per cell. -/

@[expose] public section

namespace PushPuzzle.PushFS


variable {w h : ℕ}

namespace State

/-- Cells numbered by the explicit product equivalence. -/
def cellAt (i : Fin (h * w)) : Cell w h := (finProdFinEquiv.symm i).swap

/-- The index and cell maps are inverse, including the coordinate swap. -/
@[simp] theorem cellAt_index (p : Cell w h) : cellAt (finProdFinEquiv p.swap) = p := by
  simp [cellAt]

theorem cellAt_eq_iff (i : Fin (h * w)) (p : Cell w h) :
    cellAt i = p ↔ i = finProdFinEquiv p.swap := by
  constructor
  · intro heq
    apply finProdFinEquiv.symm.injective
    simpa [cellAt] using congrArg Prod.swap heq
  · rintro rfl
    exact cellAt_index p

/-- The state-bit ordering agrees with the row ordering of the puzzle input. -/
theorem ofFn_cellAt {α : Type} (f : Cell w h → α) :
    (List.ofFn fun i => f (cellAt i)) =
      (List.ofFn fun y : Fin h => List.ofFn fun x : Fin w => f (x, y)).flatten := by
  rw [List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn
  funext y
  apply congrArg List.ofFn
  funext x
  apply congrArg f
  apply Prod.swap_injective
  change finProdFinEquiv.symm _ = (y, x)
  apply (Equiv.symm_apply_eq finProdFinEquiv).mpr
  apply Fin.ext
  simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

/-- One bit for every box position. -/
def boxBits (s : State w h) : List Bool :=
  List.ofFn fun i : Fin (h * w) => decide (cellAt i ∈ s.boxes)

theorem boxBits_eq_iff (s t : State w h) : s.boxBits = t.boxBits ↔ s.boxes = t.boxes := by
  constructor
  · intro heq
    ext p
    have := congrFun (List.ofFn_injective heq) (finProdFinEquiv p.swap)
    simpa [boxBits, cellAt] using this
  · intro heq
    simp only [boxBits, heq]

/-- One bit for every possible player position. -/
def playerBits (s : State w h) : List Bool :=
  List.ofFn fun i : Fin (h * w) => decide (cellAt i = s.player)

@[simp] theorem length_boxBits (s : State w h) : s.boxBits.length = w * h := by
  simp [boxBits, Nat.mul_comm]

@[simp] theorem length_playerBits (s : State w h) : s.playerBits.length = w * h := by
  simp [playerBits, Nat.mul_comm]

/-- A fixed-width state code; the board itself is shared by all states. -/
def bits (s : State w h) : List Bool := s.boxBits ++ s.playerBits

@[simp] theorem length_bits (s : State w h) : s.bits.length = 2 * (w * h) := by
  simp [bits, two_mul]

theorem bits_injective : Function.Injective (bits (w := w) (h := h)) := by
  intro s t heq
  have hb : s.boxBits = t.boxBits := by
    have := congrArg (List.take (w * h)) heq
    simpa [bits] using this
  have hp : s.playerBits = t.playerBits := by
    have := congrArg (List.drop (w * h)) heq
    simpa [bits] using this
  have boxes : s.boxes = t.boxes := by
    ext p
    have := congrFun (List.ofFn_injective hb) (finProdFinEquiv p.swap)
    simpa [boxBits, cellAt] using this
  have player : s.player = t.player := by
    have := congrFun (List.ofFn_injective hp) (finProdFinEquiv s.player.swap)
    simpa [playerBits, cellAt] using this
  exact State.ext player boxes

/-- The state encoding used by the search prerequisites. -/
def encoding : State w h ↪ List Bool := ⟨bits, bits_injective⟩

end State

end PushPuzzle.PushFS
