/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.ShuttleMacro
public import PushS.PortSegments
public import PushS.PortLayoutCoordinates
import CslibFrontier.Foundations.Data.List.Lookup
import all PushS.PortSegments

/-!
# The five-push macro on the emitted three-port core

Updating the actual short-train bit preserves the left, right and axis bits. The core's
finite hole sets have exactly the local two-box pattern used by the physical macro, with a
common background outside its window.
-/

public section
namespace PushPuzzle.PushS.ShuttleMacro


open PushFS PushFS.Reduction PortLayout SegmentRecipe

/-- Set just the actual short-train bit of a three-port core. -/
@[expose] def withShort (state : SignalState) (internal : ℕ) (b : Bool) : SignalState :=
  { state with internal := state.internal.set (internal + 1) b }

/-- All vertical-axis bits are unchanged by the physical short-train macro. -/
theorem withShort_axes (state : SignalState) (internal : ℕ) (b : Bool) :
    (withShort state internal b).axes = state.axes := rfl

/-- The short bit is set to the supplied value at its actual allocated index. -/
theorem withShort_short (state : SignalState) (internal : ℕ) (b : Bool)
    (hi : internal + 1 < state.internal.length) :
    (withShort state internal b).internal.getD (internal + 1) false = b :=
  List.getD_set_self hi

/-- Every other internal bit, including both outer horizontal signals, is unchanged. -/
theorem withShort_other (state : SignalState) (internal : ℕ) (b : Bool) (j : ℕ)
    (hj : j ≠ internal + 1) :
    (withShort state internal b).internal.getD j false = state.internal.getD j false :=
  List.getD_set_ne hj.symm

/-- Writing the actual current short bit leaves the complete physical signal state unchanged. -/
private theorem withShort_current (state : SignalState) (internal : ℕ)
    (hi : internal + 1 < state.internal.length) :
    withShort state internal (state.internal.getD (internal + 1) false) = state := by
  unfold withShort
  rw [List.getD_eq_getElem _ _ hi, List.set_getElem_self hi]

/-- The actual bounded horizontal rail at the first lower working level of this core. -/
@[expose] def coreRail (p : Scales.Parameters) (first : ℕ) (ha : first + 1 < p.axes) :
    Rail (p.W + 1) (p.H + 1) where
  x := p.x (first + 1)
  row := ⟨p.H - readDepth p 1, by omega⟩
  fits := by
    have h := x_add_readLength_lt_W p ha 0
    omega

/-- The actual finite set of holes emitted for the three core signal segments. -/
@[expose] def coreHoles (p : Scales.Parameters) (state : SignalState) (kind : Shuttle.Kind)
    (first internal : ℕ) : Finset (Cell (p.W + 1) (p.H + 1)) :=
  SegmentRecipe.holes (p.W + 1) (p.H + 1)
    (gateSegments (coordinates p) state kind first internal)

private theorem coreHoles_mem (p : Scales.Parameters) (state : SignalState) (kind : Shuttle.Kind)
    (first internal : ℕ) (q : Cell (p.W + 1) (p.H + 1)) :
    q ∈ coreHoles p state kind first internal ↔
      ((p.x (first + 1) + 2 + (state.internal.getD internal false).toNat - kind.kappa.toNat ≤ q.1.val ∧
        q.1.val ≤ p.x (first + 1) + (if state.internal.getD (internal + 1) false then 6 else 1)) ∧
        q.2.val = p.H - readDepth p 1) ∨
      ((p.x (first + 1) + (if state.internal.getD (internal + 1) false then 6 else 1) + 3 ≤ q.1.val ∧
        q.1.val ≤ p.x (first + 1) + 11 + (state.internal.getD (internal + 2) false).toNat) ∧
        q.2.val = p.H - readDepth p 1) ∨
      (q.1.val = p.x (first + 1) ∧
        p.H - (readDepth p 1 + 2 - (state.axes.getD (first + 1) false).toNat) ≤ q.2.val ∧
        q.2.val ≤ p.H - (readDepth p 1 + 1)) := by
  have hx := readLength_add_lt_x p (first + 1) 0
  have hy := readDepth_ge p (by omega) p.levels_pos
  have hH := readDepth_add_lt_H p 1
  have hl := Bool.toNat_le (state.internal.getD internal false)
  have hr := Bool.toNat_le (state.internal.getD (internal + 2) false)
  have hv := Bool.toNat_le (state.axes.getD (first + 1) false)
  have ht : 1 ≤ (if state.internal.getD (internal + 1) false then 6 else 1 : ℕ) ∧
      (if state.internal.getD (internal + 1) false then 6 else 1 : ℕ) ≤ 6 := by
    split <;> decide +kernel
  have hk : 2 ≤ kind.kappa.toNat ∧ kind.kappa.toNat ≤ 4 := by
    cases kind <;> decide +kernel
  have hcx : (coordinates p).x (first + 1) = p.x (first + 1) := rfl
  have hcy : (coordinates p).depth 1 = readDepth p 1 := rfl
  have hcH : (coordinates p).H = p.H := rfl
  simp only [coreHoles, SegmentRecipe.mem_holes, gateSegments]
  simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
  simp only [PortLayout.segment, Segment.Contains, hcx, hcy, kappaNat]
  simp only [onSide, reduceCtorEq, ite_false, hcH]
  omega

private theorem coreHoles_withShort_mem (p : Scales.Parameters) (state : SignalState)
    (kind : Shuttle.Kind) (first internal : ℕ) (hi : internal + 1 < state.internal.length)
    (b : Bool) (q : Cell (p.W + 1) (p.H + 1)) :
    q ∈ coreHoles p (withShort state internal b) kind first internal ↔
      ((p.x (first + 1) + 2 + (state.internal.getD internal false).toNat - kind.kappa.toNat ≤ q.1.val ∧
        q.1.val ≤ p.x (first + 1) + (if b then 6 else 1)) ∧ q.2.val = p.H - readDepth p 1) ∨
      ((p.x (first + 1) + (if b then 6 else 1) + 3 ≤ q.1.val ∧
        q.1.val ≤ p.x (first + 1) + 11 + (state.internal.getD (internal + 2) false).toNat) ∧
        q.2.val = p.H - readDepth p 1) ∨
      (q.1.val = p.x (first + 1) ∧
        p.H - (readDepth p 1 + 2 - (state.axes.getD (first + 1) false).toNat) ≤ q.2.val ∧
        q.2.val ≤ p.H - (readDepth p 1 + 1)) := by
  rw [coreHoles_mem]
  simp only [withShort_short state internal b hi,
    withShort_other state internal b internal (by omega),
    withShort_other state internal b (internal + 2) (by omega), withShort_axes]

/-- On the physical shuttle window, the actual core emitter leaves exactly the two train cells occupied. -/
theorem coreHoles_window (p : Scales.Parameters) (state : SignalState) (kind : Shuttle.Kind)
    (first internal : ℕ) (ha : first + 1 < p.axes) (hi : internal + 1 < state.internal.length)
    (b : Bool) (q : Cell (p.W + 1) (p.H + 1)) (hq : q ∈ (coreRail p first ha).window) :
    q ∈ coreHoles p (withShort state internal b) kind first internal ↔
      q ∉ (coreRail p first ha).pair (if b then 5 else 0) := by
  obtain ⟨hy, hlow, hhigh⟩ := ((coreRail p first ha).mem_window_iff q).mp hq
  have hyv := congrArg Fin.val hy
  change q.2.val = p.H - readDepth p 1 at hyv
  change p.x (first + 1) + 1 ≤ q.1.val at hlow
  change q.1.val ≤ p.x (first + 1) + 9 at hhigh
  have hx := readLength_add_lt_x p (first + 1) 0
  have hl := Bool.toNat_le (state.internal.getD internal false)
  have hr := Bool.toNat_le (state.internal.getD (internal + 2) false)
  have hk : 2 ≤ kind.kappa.toNat ∧ kind.kappa.toNat ≤ 4 := by
    cases kind <;> decide +kernel
  rw [coreHoles_withShort_mem p state kind first internal hi]
  simp only [Rail.pair, Rail.cell, coreRail, Finset.mem_insert, Finset.mem_singleton,
    Prod.ext_iff, Fin.ext_iff]
  cases b <;> simp only [Fin.val_zero, show (5 : Fin 6).val = 5 from rfl,
    Bool.false_eq_true, ite_false, ite_true] <;> omega

/-- Changing the actual short bit preserves every emitted hole outside the nine-cell window. -/
private theorem coreHoles_off_window (p : Scales.Parameters) (state : SignalState)
    (kind : Shuttle.Kind)
    (first internal : ℕ) (ha : first + 1 < p.axes) (hi : internal + 1 < state.internal.length)
    (b : Bool) (q : Cell (p.W + 1) (p.H + 1)) (hq : q ∉ (coreRail p first ha).window) :
    q ∈ coreHoles p (withShort state internal b) kind first internal ↔
      q ∈ coreHoles p (withShort state internal false) kind first internal := by
  have hoff := mt (((coreRail p first ha).mem_window_iff q).mpr) hq
  change ¬(q.2 = (coreRail p first ha).row ∧
    p.x (first + 1) + 1 ≤ q.1.val ∧ q.1.val ≤ p.x (first + 1) + 9) at hoff
  have hy : q.2 = (coreRail p first ha).row ↔ q.2.val = p.H - readDepth p 1 :=
    Fin.ext_iff
  rw [hy] at hoff
  rw [coreHoles_withShort_mem p state kind first internal hi,
    coreHoles_withShort_mem p state kind first internal hi]
  cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true]; omega

/-- The unchanged actual core holes outside its short-train window. -/
@[expose] def coreBackground (p : Scales.Parameters) (state : SignalState) (kind : Shuttle.Kind)
    (first internal : ℕ) (ha : first + 1 < p.axes) : Finset (Cell (p.W + 1) (p.H + 1)) :=
  coreHoles p (withShort state internal false) kind first internal \ (coreRail p first ha).window

/-- The actual emitted core is exactly the local two-box patch over its common background. -/
private theorem coreHoles_eq_patch (p : Scales.Parameters) (state : SignalState)
    (kind : Shuttle.Kind)
    (first internal : ℕ) (ha : first + 1 < p.axes) (hi : internal + 1 < state.internal.length)
    (b : Bool) :
    (coreRail p first ha).empty (coreBackground p state kind first internal ha)
      (if b then 5 else 0) = coreHoles p (withShort state internal b) kind first internal := by
  ext q
  by_cases hq : q ∈ (coreRail p first ha).window
  · simpa only [Rail.empty, coreBackground, Finset.mem_union, Finset.mem_sdiff, hq,
      not_true_eq_false, and_false, false_or, true_and] using
      (coreHoles_window p state kind first internal ha hi b q hq).symm
  · simpa only [Rail.empty, coreBackground, Finset.mem_union, Finset.mem_sdiff, hq,
      not_false_eq_true, and_true, false_and, or_false] using
      (coreHoles_off_window p state kind first internal ha hi b q hq).symm

private theorem background_disjoint (p : Scales.Parameters) (state : SignalState)
    (kind : Shuttle.Kind) (first internal : ℕ) (ha : first + 1 < p.axes)
    (ambient : Finset (Cell (p.W + 1) (p.H + 1)))
    (hambient : Disjoint ambient (coreRail p first ha).window) :
    Disjoint (ambient ∪ coreBackground p state kind first internal ha)
      (coreRail p first ha).window := by
  apply Finset.disjoint_union_left.mpr ⟨hambient, ?_⟩
  exact Finset.sdiff_disjoint

private theorem ambient_patch (p : Scales.Parameters) (state : SignalState)
    (kind : Shuttle.Kind) (first internal : ℕ) (ha : first + 1 < p.axes)
    (hi : internal + 1 < state.internal.length)
    (ambient : Finset (Cell (p.W + 1) (p.H + 1))) (b : Bool) :
    (coreRail p first ha).empty (ambient ∪ coreBackground p state kind first internal ha)
      (if b then 5 else 0) = ambient ∪ coreHoles p (withShort state internal b) kind first internal := by
  change (ambient ∪ coreBackground p state kind first internal ha) ∪ _ = _
  rw [Finset.union_assoc]
  exact congrArg (ambient ∪ ·) (coreHoles_eq_patch p state kind first internal ha hi b)

/-- The actual `gateSegments` short-bit switch is realized by five eastward two-box pushes,
with every ambient hole outside the local window fixed. -/
theorem core_east_five (p : Scales.Parameters) (state : SignalState) (kind : Shuttle.Kind)
    (first internal : ℕ) (ha : first + 1 < p.axes) (hi : internal + 1 < state.internal.length)
    (hshort : state.internal.getD (internal + 1) false = false)
    (ambient : Finset (Cell (p.W + 1) (p.H + 1)))
    (hambient : Disjoint ambient (coreRail p first ha).window)
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) :
    Reachable B none
      { player := (coreRail p first ha).cell 1
        boxes := (ambient ∪ coreHoles p state kind first internal)ᶜ }
      { player := (coreRail p first ha).cell 6
        boxes := (ambient ∪ coreHoles p (withShort state internal true) kind first internal)ᶜ } := by
  have h := (coreRail p first ha).east_five
    (ambient ∪ coreBackground p state kind first internal ha)
    (background_disjoint p state kind first internal ha ambient hambient) B hB
  have h0 := ambient_patch p state kind first internal ha hi ambient false
  have h5 := ambient_patch p state kind first internal ha hi ambient true
  simp only [Bool.false_eq_true, ite_false, ite_true] at h0 h5
  have hp0 : ((coreRail p first ha).eastState
      (ambient ∪ coreBackground p state kind first internal ha) 0).player =
      (coreRail p first ha).cell 1 := rfl
  have hp5 := (coreRail p first ha).east_five_player
    (ambient ∪ coreBackground p state kind first internal ha)
  have he0 : ((coreRail p first ha).eastState
      (ambient ∪ coreBackground p state kind first internal ha) 0).empty = _ := h0
  have he5 : ((coreRail p first ha).eastState
      (ambient ∪ coreBackground p state kind first internal ha) 5).empty = _ := h5
  have hcurrent := withShort_current state internal hi
  rw [hshort] at hcurrent
  simpa only [HoleState.toState, hp0, hp5, he0, he5, hcurrent] using h

/-- The same actual short-bit switch in reverse uses five westward two-box pushes,
starting at offset nine and finishing at offset four. -/
theorem core_west_five (p : Scales.Parameters) (state : SignalState) (kind : Shuttle.Kind)
    (first internal : ℕ) (ha : first + 1 < p.axes) (hi : internal + 1 < state.internal.length)
    (hshort : state.internal.getD (internal + 1) false = true)
    (ambient : Finset (Cell (p.W + 1) (p.H + 1)))
    (hambient : Disjoint ambient (coreRail p first ha).window)
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) :
    Reachable B none
      { player := (coreRail p first ha).cell 9
        boxes := (ambient ∪ coreHoles p state kind first internal)ᶜ }
      { player := (coreRail p first ha).cell 4
        boxes := (ambient ∪ coreHoles p (withShort state internal false) kind first internal)ᶜ } := by
  have h := (coreRail p first ha).west_five
    (ambient ∪ coreBackground p state kind first internal ha)
    (background_disjoint p state kind first internal ha ambient hambient) B hB
  have h0 := ambient_patch p state kind first internal ha hi ambient false
  have h5 := ambient_patch p state kind first internal ha hi ambient true
  simp only [Bool.false_eq_true, ite_false, ite_true] at h0 h5
  have hp5 : ((coreRail p first ha).westState
      (ambient ∪ coreBackground p state kind first internal ha) 5).player =
      (coreRail p first ha).cell 9 := rfl
  have hp0 := (coreRail p first ha).west_five_player
    (ambient ∪ coreBackground p state kind first internal ha)
  have he0 : ((coreRail p first ha).westState
      (ambient ∪ coreBackground p state kind first internal ha) 0).empty = _ := h0
  have he5 : ((coreRail p first ha).westState
      (ambient ∪ coreBackground p state kind first internal ha) 5).empty = _ := h5
  have hcurrent := withShort_current state internal hi
  rw [hshort] at hcurrent
  simpa only [HoleState.toState, hp0, hp5, he0, he5, hcurrent] using h

end PushPuzzle.PushS.ShuttleMacro
