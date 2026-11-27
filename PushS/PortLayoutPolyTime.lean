/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PageLevelsPolyTime

/-!
# Polynomial-time port data and bounded coordinate tables

The actual page arrays and canonical physical bits use their framed-list encodings.
The scale environment has a fixed number of working levels: each coordinate table is
therefore a fixed finite list of polynomial powers of its unary axis count.

## Main results

* `PortLayout.computableInPolyTime_canonical`: compute the actual internal filling.
* `PortLayout.computableInPolyTime_depthTable`: compute the bounded working-row table.
* `PortLayout.computableInPolyTime_lengthTable`: compute the bounded branch-length table.
-/

public section

namespace PushPuzzle.PushS


open _root_.Turing.MultiTapeTM
open scoped PushPuzzle.PushS PushPuzzle.PushS.PageLevels

@[local fun_prop] private theorem shape_polyTime :
    ComputableInPolyTime LowerGroup.shape encLowerGroup PageLevels.encGroup := by
  have h := encLowerGroup_elim_polyTime (encP := encUnit) (encE := PageLevels.encGroup)
    (g0 := fun p => .wire p.2.1 p.2.2) (g1 := fun p => .triple p.2.2)
    (by fun_prop) (by fun_prop)
  have hh := h.comp (show ComputableInPolyTime (fun g : LowerGroup => ((), g))
    encLowerGroup (encPair encUnit encLowerGroup) from by fun_prop)
  exact hh.of_enc_eq (by intro g; cases g <;> rfl)

private def isGate : LowerGroup → Bool
  | .wire .. => false
  | .gate .. => true

@[local fun_prop] private theorem isGate_polyTime :
    ComputableInPolyTime isGate encLowerGroup encBool := by
  have h := encLowerGroup_elim_polyTime (encP := encUnit) (encE := encBool)
    (g0 := fun _ => false) (g1 := fun _ => true) (by fun_prop) (by fun_prop)
  have hh := h.comp (show ComputableInPolyTime (fun g : LowerGroup => ((), g))
    encLowerGroup (encPair encUnit encLowerGroup) from by fun_prop)
  exact hh.of_enc_eq (by intro g; cases g <;> rfl)

private theorem sum_internalCount (gs : List LowerGroup) :
    (gs.map LowerGroup.internalCount).sum = gs.length + 2 * gs.countP isGate := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    cases g <;> simp [List.countP_cons, LowerGroup.internalCount, isGate, ih] <;> omega

namespace PortLayout

/-- Forgetting gate labels retains the actual ordered group arrays in polynomial time. -/
@[fun_prop] theorem computableInPolyTime_pages :
    ComputableInPolyTime pages encPortLayout PageLevels.encPages := by
  unfold pages
  fun_prop

/-- Read an actual upper working level by its unary input index. -/
@[fun_prop] theorem computableInPolyTime_upperLevel :
    ComputableInPolyTime (fun p : PortLayout × ℕ => p.1.upperLevel p.2)
      (encPair encPortLayout encUnary) encUnary := by
  unfold upperLevel
  fun_prop

/-- Read an actual lower working level by its unary input index. -/
@[fun_prop] theorem computableInPolyTime_lowerLevel :
    ComputableInPolyTime (fun p : PortLayout × ℕ => p.1.lowerLevel p.2)
      (encPair encPortLayout encUnary) encUnary := by
  unfold lowerLevel
  fun_prop

/-- Count the actual preceding internal signals, charging three slots for each gate. -/
@[fun_prop] theorem computableInPolyTime_lowerOffset :
    ComputableInPolyTime (fun p : PortLayout × ℕ => p.1.lowerOffset p.2)
      (encPair encPortLayout encUnary) encUnary := by
  simp only [lowerOffset, sum_internalCount]
  fun_prop

private def lowerSignals (axes : List Bool) : LowerGroup → List Bool
  | .wire a _ => [axes.getD a false]
  | .gate _ a =>
    let heavy := !(axes.getD (a + 2) false)
    [axes.getD a false, heavy, heavy]

@[local fun_prop] private theorem lowerSignals_polyTime :
    ComputableInPolyTime (fun p : List Bool × LowerGroup => lowerSignals p.1 p.2)
      (encPair (encList encBool) encLowerGroup) (encList encBool) := by
  have h := encLowerGroup_elim_polyTime (encP := encList encBool) (encE := encList encBool)
    (g0 := fun p => [p.1.getD p.2.1 false])
    (g1 := fun p => [p.1.getD p.2.2 false,
      !(p.1.getD (p.2.2 + 2) false), !(p.1.getD (p.2.2 + 2) false)])
    (by fun_prop) (by fun_prop)
  exact h.of_enc_eq (by intro p; rcases p with ⟨axes, g⟩; cases g <;> rfl)

/-- Fill the physical upper and lower internal signals in their actual list order. -/
@[fun_prop] theorem computableInPolyTime_canonical :
    ComputableInPolyTime (fun p : PortLayout × List Bool => p.1.canonical p.2)
      (encPair encPortLayout (encList encBool)) encSignalState := by
  change ComputableInPolyTime
    (fun p : PortLayout × List Bool => SignalState.mk p.2
      ((p.1.upperPairs.map fun ab => !(p.2.getD ab.1 false)) ++
        p.1.lowerGroups.flatMap (lowerSignals p.2))) _ _
  fun_prop

section Coordinates

variable {α : Type} {enc : α ↪ List Bool} {p : α → Scales.Parameters} {M : ℕ}
  (haxes : ComputableInPolyTime (fun a => (p a).axes) enc encUnary)
  (hlevels : ∀ a, (p a).levels = M)

include haxes hlevels

private theorem scaleA_polyTime :
    ComputableInPolyTime (fun a => (p a).A) enc encUnary := by
  simp only [Scales.Parameters.A, Scales.Parameters.Q, hlevels]
  fun_prop

omit hlevels in
private theorem scaleS_polyTime :
    ComputableInPolyTime (fun a => (p a).S) enc encUnary := by
  unfold Scales.Parameters.S
  fun_prop

/-- Every fixed allocated working row is a polynomial of the unary axis count. -/
theorem computableInPolyTime_Y (j : ℕ) :
    ComputableInPolyTime (fun a => (p a).Y j) enc encUnary := by
  have hA := scaleA_polyTime haxes hlevels
  have hS := scaleS_polyTime haxes
  unfold Scales.Parameters.Y
  fun_prop

/-- Every fixed allocated branch length is a polynomial of the unary axis count. -/
private theorem computableInPolyTime_L (j : ℕ) :
    ComputableInPolyTime (fun a => (p a).L j) enc encUnary := by
  have hA := scaleA_polyTime haxes hlevels
  have hS := scaleS_polyTime haxes
  unfold Scales.Parameters.L
  fun_prop

/-- With a fixed working-level bound, the board spacing is polynomial-time computable. -/
theorem computableInPolyTime_D :
    ComputableInPolyTime (fun a => (p a).D) enc encUnary := by
  have hA := scaleA_polyTime haxes hlevels
  have hS := scaleS_polyTime haxes
  simp only [Scales.Parameters.D, hlevels]
  fun_prop

/-- With a fixed working-level bound, the actual horizontal extent is polynomial-time. -/
theorem computableInPolyTime_W :
    ComputableInPolyTime (fun a => (p a).W) enc encUnary := by
  have hD := computableInPolyTime_D haxes hlevels
  unfold Scales.Parameters.W
  fun_prop

/-- With a fixed working-level bound, the actual vertical extent is polynomial-time. -/
theorem computableInPolyTime_H :
    ComputableInPolyTime (fun a => (p a).H) enc encUnary := by
  have hD := computableInPolyTime_D haxes hlevels
  unfold Scales.Parameters.H
  fun_prop

/-- Compute precisely the finite table used for every raw working-level lookup. -/
theorem computableInPolyTime_depthTable :
    ComputableInPolyTime (fun a => depthTable (p a)) enc (encList encUnary) := by
  have ht : ComputableInPolyTime
      (fun a => (List.range M).map fun j => (p a).Y (j + 1)) enc (encList encUnary) :=
    ComputableInPolyTime.mapConst _ (fun j _ => computableInPolyTime_Y haxes hlevels (j + 1))
  simp only [depthTable, hlevels]
  fun_prop

/-- Compute precisely the finite table used for every raw branch-length lookup. -/
theorem computableInPolyTime_lengthTable :
    ComputableInPolyTime (fun a => lengthTable (p a)) enc (encList encUnary) := by
  have ht : ComputableInPolyTime
      (fun a => (List.range M).map fun j => (p a).L (j + 1)) enc (encList encUnary) :=
    ComputableInPolyTime.mapConst _ (fun j _ => computableInPolyTime_L haxes hlevels (j + 1))
  simp only [lengthTable, hlevels]
  fun_prop

end Coordinates
end PortLayout
end PushPuzzle.PushS
