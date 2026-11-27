/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramRounds
public import PushS.PortCentralMarkers
public import Mathlib.Order.Interval.Finset.Fin

/-! The actual target's first two compact rounds remove exactly its complete outer frame. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS

/-- Whole side columns, followed by the remaining holes of the top and bottom rows. -/
def frameSchedule (W H : ℕ) : List Template :=
  [.read .south [(0, H + 1), (W, H + 1)],
    .read .west [(0, W + 1), (H, W + 1)]]

private theorem column_full (W H lane : ℕ) (hlane : lane ≤ W) :
    (Scan.lineCells (w := W + 1) (h := H + 1) .south lane).take (H + 1) =
      Scan.lineCells .south lane := by
  apply List.take_of_length_le
  simp only [Scan.lineCells, dite_eq_left (by omega : lane < W + 1),
    List.length_reverse, List.length_ofFn, le_refl]

private theorem row_full (W H lane : ℕ) (hlane : lane ≤ H) :
    (Scan.lineCells (w := W + 1) (h := H + 1) .west lane).take (W + 1) =
      Scan.lineCells .west lane := by
  apply List.take_of_length_le
  simp only [Scan.lineCells, dite_eq_left (by omega : lane < H + 1), List.length_ofFn, le_refl]

/-- The two whole-frame rounds retain exactly the strict rectangle interior. -/
theorem frame_remaining (W H : ℕ) (E : Finset (Cell (W + 1) (H + 1))) :
    (emit (frameSchedule W H) E).remaining = E \ Boundary.frame := by
  ext q
  simp only [frameSchedule, emit, emitReads, column_full W H 0 (Nat.zero_le _),
    column_full W H W le_rfl, row_full W H 0 (Nat.zero_le _), row_full W H H le_rfl,
    Finset.mem_sdiff, List.mem_toFinset, Scan.mem_lineCells, Direction.lane,
    Boundary.frame, Boundary.edge, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [Nat.add_right_cancel_iff]
  tauto

private theorem frame_discarded (W H : ℕ) (E : Finset (Cell (W + 1) (H + 1))) :
    (emit (frameSchedule W H) E).discarded = 0 := rfl

private theorem frame_card {W H : ℕ} (hW : 1 ≤ W) (hH : 1 ≤ H) :
    (Boundary.frame (w := W + 1) (h := H + 1)).card = 2 * (W + H) := by
  have he : Boundary.frame (w := W + 1) (h := H + 1) =
      (Finset.Ioo (0 : Fin (W + 1)) (Fin.last W) ×ˢ
        Finset.Ioo (0 : Fin (H + 1)) (Fin.last H))ᶜ := by
    ext q
    simp only [Boundary.frame, Boundary.edge, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_compl, Finset.mem_product, Finset.mem_Ioo, Fin.lt_def,
      Fin.val_zero, Fin.val_last]
    have hx := q.1.isLt
    have hy := q.2.isLt
    omega
  rw [he, Finset.card_compl, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
    Finset.card_product, Fin.card_Ioo, Fin.card_Ioo, Fin.val_zero, Fin.val_last, Nat.sub_zero]
  simp only [Fin.val_last, Fin.val_zero, Nat.sub_zero]
  have ha : (W + 1) * (H + 1) = (W - 1) * (H - 1) + 2 * (W + H) := by
    have hw := Nat.sub_add_cancel hW
    have hh := Nat.sub_add_cancel hH
    nlinarith
  omega

/-- The real full-frame target pays the exact four-edge inventory and leaves only its interior. -/
theorem frame_quota {W H : ℕ} (hW : 1 ≤ W) (hH : 1 ≤ H)
    (E : Finset (Cell (W + 1) (H + 1))) (hframe : Boundary.frame ⊆ E) :
    Scan.quota (instructions (w := W + 1) (h := H + 1) (emit (frameSchedule W H) E).rounds) =
      2 * (W + H) := by
  have hc := emit_accounting (frameSchedule W H) E
  rw [frame_remaining, frame_discarded, Nat.add_zero] at hc
  have hf := Finset.card_sdiff_add_card_eq_card hframe
  have hsize := frame_card hW hH
  rw [quota_instructions]
  omega

/-- The literal canonical target hole set used by the marked two-page source compiler. -/
def targetHoles (l : PortLayout) (p : Scales.Parameters) (target : List Bool) :
    Finset (Cell (p.W + 1) (p.H + 1)) :=
  SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p (l.canonical target))

/-- The first two blocks accept the actual canonical target and remove exactly its frame. -/
theorem target_frame (l : PortLayout) (p : Scales.Parameters) (target : List Bool) :
    Scan.eval (instructions (emit (frameSchedule p.W p.H) (targetHoles l p target)).rounds)
      (targetHoles l p target) = some (targetHoles l p target \ Boundary.frame) ∧
      Scan.quota (instructions (w := p.W + 1) (h := p.H + 1)
        (emit (frameSchedule p.W p.H) (targetHoles l p target)).rounds) = 2 * (p.W + p.H) := by
  refine ⟨?_, ?_⟩
  · rw [emit_eval, frame_remaining]
  · have hD : 0 < p.D := by have := p.outer_distance; omega
    have hW : 1 ≤ p.W := Nat.mul_pos (by omega) hD
    have hH : 1 ≤ p.H := by change 1 ≤ 2 * p.D; omega
    exact frame_quota hW hH _ (l.encodedSegments_frame_subset p (l.canonical target))

end PushPuzzle.Push.AcceptanceProgram
