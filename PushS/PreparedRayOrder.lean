/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombRayDirections
public import CslibFrontier.Foundations.Geometry.Polygonal.AngleOrder

/-! Literal clockwise order of the actual horizontal, prepared diagonal and vertical comb rays. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib

open Cslib.Complexity

open Cslib.Orthogonal

/-- The clockwise angle of a literal compass octant, starting east. -/
@[expose] noncomputable def octantAngle (rank : ℕ) : Real.Angle := ((-(rank : ℝ) * Real.pi / 4 : ℝ) : Real.Angle)

private theorem octant_lift_mem (rank : ℕ) (hr : rank < 8) :
    -(rank : ℝ) * Real.pi / 4 ∈ Set.Ioo (-(15 * Real.pi / 8)) (-(15 * Real.pi / 8) + 2 * Real.pi) := by
  have hr' : (rank : ℝ) ≤ 7 := by exact_mod_cast (show rank ≤ 7 by omega)
  have hp := mul_le_mul_of_nonneg_right hr' Real.pi_pos.le
  have hn := mul_nonneg (Nat.cast_nonneg (α := ℝ) rank) Real.pi_pos.le
  constructor <;> linarith [Real.pi_pos]

private theorem octant_lift_lt (left right : ℕ) :
    -(left : ℝ) * Real.pi / 4 < -(right : ℝ) * Real.pi / 4 ↔ right < left := by
  rw [div_lt_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 4), neg_mul, neg_mul, neg_lt_neg_iff,
    mul_lt_mul_iff_left₀ Real.pi_pos]
  exact Nat.cast_lt

private theorem octant_lift_ne (left right : ℕ) (hne : left ≠ right) :
    -(left : ℝ) * Real.pi / 4 ≠ -(right : ℝ) * Real.pi / 4 := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ne_of_gt ((octant_lift_lt right left).mpr hlt)
  · exact ne_of_lt ((octant_lift_lt left right).mpr hgt)

/-- The actual angular strict-between predicate has precisely the literal clockwise octant order. -/
theorem sbtw_octants_iff {a b c : ℕ} (ha : a < 8) (hb : b < 8) (hc : c < 8)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    sbtw (octantAngle c) (octantAngle b) (octantAngle a) ↔
      (a < b ∧ b < c) ∨ (b < c ∧ c < a) ∨ (c < a ∧ a < b) := by
  rw [octantAngle, octantAngle, octantAngle,
    Cslib.Polygonal.sbtw_angle_iff_cyclic_lt (octant_lift_mem c hc) (octant_lift_mem b hb) (octant_lift_mem a ha)
      (octant_lift_ne c b hbc.symm) (octant_lift_ne b a hab.symm) (octant_lift_ne c a hac.symm)]
  simp only [octant_lift_lt]
  tauto

/-- The original four-way native tangent key read as its actual prepared compass octant. -/
@[expose] def tangentOctant (vector : Point) : ℕ :=
  match tangentKey vector with
  | 0 => 3
  | 1 => 4
  | 2 => 7
  | _ => 0

private theorem arg_diagonal : (1 + Complex.I).arg = Real.pi / 4 := by
  have hs : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hpoint : (Real.sqrt 2 : ℂ) * (Real.cos (Real.pi / 4) + Real.sin (Real.pi / 4) * Complex.I) = 1 + Complex.I := by
    apply Complex.ext <;> norm_num [Real.cos_pi_div_four, Real.sin_pi_div_four]
    all_goals nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have h := Complex.arg_mul_cos_add_sin_mul_I hs (θ := Real.pi / 4) (by constructor <;> linarith [Real.pi_pos])
  simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin] at h
  rw [hpoint] at h
  exact h

private theorem arg_negative_diagonal : (-1 - Complex.I).arg = -(3 * Real.pi / 4) := by
  rw [show (-1 - Complex.I : ℂ) = -(1 + Complex.I) by ring,
    Complex.arg_neg_eq_arg_sub_pi_of_im_pos (by norm_num), arg_diagonal]
  ring

private theorem arg_horizontal {vector : Point} (hy : vector.2 = 0) :
    (complexPoint vector).arg = if vector.1 < 0 then Real.pi else 0 := by
  have hpoint : complexPoint vector = ((vector.1 : ℝ) : ℂ) := by
    apply Complex.ext
    · rfl
    · change (vector.2 : ℝ) = 0
      exact_mod_cast hy
  rw [hpoint]
  split_ifs with hneg
  · exact Complex.arg_ofReal_of_neg (by exact_mod_cast hneg)
  · exact Complex.arg_ofReal_of_nonneg (by exact_mod_cast not_lt.mp hneg)

private theorem arg_diagonal_vector {vector : Point} (hy : vector.2 = vector.1) (hx : vector.1 ≠ 0) :
    (complexPoint vector).arg = if vector.1 < 0 then -(3 * Real.pi / 4) else Real.pi / 4 := by
  split_ifs with hneg
  · have hpoint : complexPoint vector = ((-(vector.1 : ℝ)) : ℂ) * (-1 - Complex.I) := by
      apply Complex.ext
      · change (vector.1 : ℝ) = _
        simp
      · change (vector.2 : ℝ) = _
        rw [hy]
        simp
    rw [hpoint]
    have hscale : (0 : ℝ) < -(vector.1 : ℝ) := by exact_mod_cast (neg_pos.mpr hneg)
    simpa only [Complex.ofReal_neg] using (Complex.arg_real_mul (-1 - Complex.I) hscale).trans arg_negative_diagonal
  · have hpos : 0 < vector.1 := by omega
    have hpoint : complexPoint vector = ((vector.1 : ℝ) : ℂ) * (1 + Complex.I) := by
      apply Complex.ext
      · change (vector.1 : ℝ) = _
        simp
      · change (vector.2 : ℝ) = _
        rw [hy]
        simp
    rw [hpoint]
    have hscale : (0 : ℝ) < (vector.1 : ℝ) := by exact_mod_cast hpos
    exact (Complex.arg_real_mul (1 + Complex.I) hscale).trans arg_diagonal

/-- Real principal arguments of the original four native prepared tangent keys. -/
@[expose] noncomputable def tangentArgument (key : ℕ) : ℝ :=
  match key with
  | 0 => -(3 * Real.pi / 4)
  | 1 => Real.pi
  | 2 => Real.pi / 4
  | _ => 0

/-- The original integer tangent key reads exactly the actual complex principal argument. -/
theorem tangentKey_arg (vector : Point) (hshape : vector.2 = 0 ∨ vector.2 = vector.1) (hx : vector.1 ≠ 0) :
    (complexPoint vector).arg = tangentArgument (tangentKey vector) := by
  rcases hshape with hy | hy
  · rw [arg_horizontal hy]
    by_cases hneg : vector.1 < 0 <;> simp [tangentKey, hy, hneg, tangentArgument]
  · rw [arg_diagonal_vector hy hx]
    by_cases hneg : vector.1 < 0
    · simp [tangentKey, hy, hneg, tangentArgument]
    · have hpos : 0 < vector.1 := by omega
      simp [tangentKey, hy, hneg, hpos, tangentArgument]

/-- The literal native tangent program always returns one of its four keys. -/
theorem tangentKey_lt (vector : Point) : tangentKey vector < 4 := by
  unfold tangentKey
  split_ifs <;> decide

private theorem tangentArgument_octant (vector : Point) :
    ((tangentArgument (tangentKey vector) : ℝ) : Real.Angle) = octantAngle (tangentOctant vector) := by
  have hbound := tangentKey_lt vector
  unfold tangentOctant
  generalize hkey : tangentKey vector = key at *
  interval_cases key
  · change ((-(3 * Real.pi / 4) : ℝ) : Real.Angle) = ((-(3 : ℝ) * Real.pi / 4 : ℝ) : Real.Angle)
    congr 1
    ring
  · change (Real.pi : Real.Angle) = ((-(4 : ℝ) * Real.pi / 4 : ℝ) : Real.Angle)
    rw [show (-(4 : ℝ) * Real.pi / 4) = -Real.pi by ring, Real.Angle.coe_neg, Real.Angle.neg_coe_pi]
  · change ((Real.pi / 4 : ℝ) : Real.Angle) = ((-(7 : ℝ) * Real.pi / 4 : ℝ) : Real.Angle)
    rw [show (-(7 : ℝ) * Real.pi / 4) = Real.pi / 4 - 2 * Real.pi by ring]
    simp only [Real.Angle.coe_sub, Real.Angle.coe_two_pi, sub_zero]
  · simp [tangentArgument, octantAngle]

/-- The actual source ray has exactly the literal compass octant read from its original tangent key. -/
theorem tangentKey_direction (vector : Point) (hshape : vector.2 = 0 ∨ vector.2 = vector.1) (hx : vector.1 ≠ 0) :
    ((complexPoint vector).arg : Real.Angle) = octantAngle (tangentOctant vector) := by
  rw [tangentKey_arg vector hshape hx]
  exact tangentArgument_octant vector

private def keyRank (key : Fin 4) : Fin 8 :=
  ⟨match key.val with | 0 => 3 | 1 => 4 | 2 => 7 | _ => 0, by split <;> omega⟩

private theorem keyRank_injective : Function.Injective keyRank := by decide

private theorem keyRank_ne_down : ∀ key : Fin 4, keyRank key ≠ 2 := by decide

private theorem keyRank_clockwise : ∀ a b : Fin 4, a ≠ b →
    (a.val < b.val ↔ (2 < (keyRank a).val ∧ (keyRank a).val < (keyRank b).val) ∨
      ((keyRank a).val < (keyRank b).val ∧ (keyRank b).val < 2) ∨
      ((keyRank b).val < 2 ∧ 2 < (keyRank a).val)) := by decide

/-- The original integer key sort is exactly clockwise order after the real downward tooth ray. -/
theorem tangentKey_clockwise_iff (left right : Point) (hne : tangentKey left ≠ tangentKey right) :
    sbtw (octantAngle (tangentOctant right)) (octantAngle (tangentOctant left)) (octantAngle 2) ↔
      tangentKey left < tangentKey right := by
  let a : Fin 4 := ⟨tangentKey left, tangentKey_lt left⟩
  let b : Fin 4 := ⟨tangentKey right, tangentKey_lt right⟩
  have hab : a ≠ b := fun h => hne (congrArg Fin.val h)
  have hoct : keyRank a ≠ keyRank b := fun h => hab (keyRank_injective h)
  have hneval : (keyRank a).val ≠ (keyRank b).val := fun h => hoct (Fin.ext h)
  change sbtw (octantAngle (keyRank b).val) (octantAngle (keyRank a).val) (octantAngle 2) ↔ a.val < b.val
  rw [sbtw_octants_iff (a := 2) (b := (keyRank a).val) (c := (keyRank b).val)
    (by decide) (keyRank a).isLt (keyRank b).isLt
    (fun h => keyRank_ne_down a (Fin.ext h.symm)) hneval (fun h => keyRank_ne_down b (Fin.ext h.symm))]
  exact (keyRank_clockwise a b hab).symm

/-- The original fan's integer key sort is the true clockwise order of its actual native fragment rays after the downward tooth. -/
theorem nativeFragment_clockwise_iff (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
    (hhead : ∀ edge : Fin G.edges.length,
      (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))
    (a b : Graph.Dart G)
    (hne : tangentKey (outgoingVector width d ⟨a.1.val, a.2⟩) ≠ tangentKey (outgoingVector width d ⟨b.1.val, b.2⟩)) :
    sbtw
      (((edgeFragment width height hd hfit b.1 (hhead b.1)
        (if b.2 then Fin.last (edgeCrossings width d b.1).length else 0)).germ b.2).arg : Real.Angle)
      (((edgeFragment width height hd hfit a.1 (hhead a.1)
        (if a.2 then Fin.last (edgeCrossings width d a.1).length else 0)).germ a.2).arg : Real.Angle)
      (octantAngle 2) ↔
      tangentKey (outgoingVector width d ⟨a.1.val, a.2⟩) < tangentKey (outgoingVector width d ⟨b.1.val, b.2⟩) := by
  rw [edgeFragment_native_arg width height hd hfit b.1 (hhead b.1) b.2,
    edgeFragment_native_arg width height hd hfit a.1 (hhead a.1) a.2,
    tangentKey_direction _ (outgoingVector_shape width hd b.1 (hhead b.1) b.2) (outgoingVector_x_ne_zero width hd b.1 (hhead b.1) b.2),
    tangentKey_direction _ (outgoingVector_shape width hd a.1 (hhead a.1) a.2) (outgoingVector_x_ne_zero width hd a.1 (hhead a.1) a.2)]
  exact tangentKey_clockwise_iff _ _ hne

end PushPuzzle.PushS.Comb
