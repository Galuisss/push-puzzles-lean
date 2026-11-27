/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombCrossingGeometry
import all PushS.CombCrossingGeometry
import all PushS.CombTopology

/-! Uniform local feature budgets in the actual bounded-width comb compiler. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib

open Cslib.Complexity

/-- The actual shear window contains exactly the original longitudinal rows in its fixed span. -/
theorem point_column_window_iff (width start span : ℕ) (a : Cslib.Orthogonal.Point)
    (ha : 0 ≤ a.1 ∧ a.1 ≤ width) :
    (2 * (stride width : ℤ) * start ≤ (point width a).1 ∧
      (point width a).1 ≤ 2 * (stride width : ℤ) * start + (2 * (stride width : ℤ) * span + 2 * width)) ↔
      (start : ℤ) ≤ a.2 ∧ a.2 ≤ (start : ℤ) + span := by
  have hs : (0 : ℤ) ≤ stride width := by positivity
  have hwide : (width : ℤ) < stride width := by simp only [stride, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]; omega
  dsimp only [point]
  constructor
  · rintro ⟨hl, hr⟩
    constructor
    · by_contra h
      have hm := mul_le_mul_of_nonneg_left (show a.2 + 1 ≤ (start : ℤ) by omega) hs
      nlinarith
    · by_contra h
      have hm := mul_le_mul_of_nonneg_left (show (start : ℤ) + span + 1 ≤ a.2 by omega) hs
      nlinarith
  · rintro ⟨hl, hr⟩
    have hl' := mul_le_mul_of_nonneg_left hl hs
    have hr' := mul_le_mul_of_nonneg_left hr hs
    constructor <;> nlinarith

/-- Distinct genuine crossings on one tooth occupy distinct integer heights in `[0,2*width]`. -/
theorem toothCrossings_length_le (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (vertex : ℕ) :
    (toothCrossings width d vertex).length ≤ 2 * width + 1 := by
  have hv : ∀ p ∈ d.1, 0 ≤ p.1 ∧ p.1 ≤ width := fun p hp => ⟨(hfit.1 p hp).1, (hfit.1 p hp).2.1⟩
  have hp : ∀ r ∈ d.2, ∀ p ∈ r, 0 ≤ p.1 ∧ p.1 ≤ width :=
    fun r hr p hp => ⟨(hfit.2 r hr p hp).1, (hfit.2 r hr p hp).2.1⟩
  let hits := toothCrossings width d vertex
  have bounds (i : Fin hits.length) : 0 ≤ (hits.get i).height ∧ (hits.get i).height ≤ 2 * width :=
    crossing_height_bounds width hd hp (tooth_mem width d (List.get_mem hits i)).1
  let f : Fin hits.length → Fin (2 * width + 1) := fun i =>
    ⟨(hits.get i).height.toNat, by have := bounds i; omega⟩
  have hf : Function.Injective f := by
    intro i j he
    have hn := (toothCrossings_perm width d vertex).nodup_iff.mpr ((crossings_nodup width d).filter _)
    apply hn.get_inj_iff.mp
    apply tooth_height_injective width hd hv (List.get_mem hits i) (List.get_mem hits j)
    have hi := bounds i
    have hj := bounds j
    have hh := congrArg Fin.val he
    change (hits.get i).height.toNat = (hits.get j).height.toNat at hh
    omega
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf

/-- The literal native core emits at most five ports, one upper pair and two lower groups. -/
theorem coreTemplate_feature_bounds (vertex : ℕ) (ports : List (NCL.WeightedPort ℕ)) :
    (coreTemplate vertex ports).order.length ≤ 5 ∧ (coreTemplate vertex ports).upper.length ≤ 1 ∧
      (coreTemplate vertex ports).lower.length ≤ 2 := by
  unfold coreTemplate
  extract_lets a b c kind ta tb tc inside outside
  split_ifs <;> simp only [List.length_cons, List.length_nil] <;> decide

/-- Each actual vertex block has uniformly bounded contour ports and local page groups. -/
theorem vertexBlock_feature_bounds (width height : ℕ) (input : Input) {G : Graph}
    (hd : G.IsPlanarOrthogonalDrawing input.drawing) (hfit : Graph.drawingFits input.drawing width height)
    (vertex : ℕ) :
    (vertexBlock width input vertex).order.length ≤ 4 * width + 7 ∧
      (vertexBlock width input vertex).upper.length ≤ 1 ∧
        (vertexBlock width input vertex).lower.length ≤ 2 * width + 3 := by
  have htooth := toothCrossings_length_le width height hd hfit vertex
  have hcore := coreTemplate_feature_bounds vertex (fan width input vertex)
  simp only [vertexBlock, coreBlock, List.length_append, List.length_map, List.length_reverse]
  omega

private theorem flatMap_length_le {α β : Type*} (xs : List α) (f : α → List β) (budget : ℕ)
    (hbudget : ∀ a ∈ xs, (f a).length ≤ budget) :
    (xs.flatMap f).length ≤ xs.length * budget := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := hbudget a (by simp)
    have ht := ih (fun a ha => hbudget a (List.mem_cons_of_mem _ ha))
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- The actual full contour emits only a constant number of ports per original source vertex. -/
theorem cut_order_length_le (width height : ℕ) (input : Input) {G : Graph}
    (hd : G.IsPlanarOrthogonalDrawing input.drawing) (hfit : Graph.drawingFits input.drawing width height) :
    (cut width input).order.length ≤ input.drawing.1.length * (4 * width + 7) := by
  have hb := flatMap_length_le (vertexOrder width input.drawing)
    (fun sv => (vertexBlock width input sv.2).order) (4 * width + 7)
    (fun sv _ => (vertexBlock_feature_bounds width height input hd hfit sv.2).1)
  have hlen : (vertexOrder width input.drawing).length = input.drawing.1.length := by
    simpa only [prepare, List.length_map, List.length_zipIdx] using (vertexOrder_perm width input.drawing).length_eq
  simpa only [cut, List.flatMap_map, Function.comp_def, hlen] using hb

/-- The same actual compiled layout retains that linear contour-port budget. -/
theorem compile_portCount_le (width height : ℕ) (input : Input) {G : Graph}
    (hd : G.IsPlanarOrthogonalDrawing input.drawing) (hfit : Graph.drawingFits input.drawing width height) :
    (compile width input).portCount ≤ input.drawing.1.length * (4 * width + 7) :=
  cut_order_length_le width height input hd hfit

/-- Actual lower groups emit only a constant number per original source vertex. -/
theorem cut_lower_length_le (width height : ℕ) (input : Input) {G : Graph}
    (hd : G.IsPlanarOrthogonalDrawing input.drawing) (hfit : Graph.drawingFits input.drawing width height) :
    (cut width input).lower.length ≤ input.drawing.1.length * (2 * width + 3) := by
  have hb := flatMap_length_le (vertexOrder width input.drawing)
    (fun sv => (vertexBlock width input sv.2).lower) (2 * width + 3)
    (fun sv _ => (vertexBlock_feature_bounds width height input hd hfit sv.2).2.2)
  have hlen : (vertexOrder width input.drawing).length = input.drawing.1.length := by
    simpa only [prepare, List.length_map, List.length_zipIdx] using (vertexOrder_perm width input.drawing).length_eq
  simpa only [cut, List.flatMap_map, Function.comp_def, hlen] using hb

end PushPuzzle.PushS.Comb
