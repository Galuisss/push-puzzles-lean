/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.PartnerConfigurationInternal
public import Push.PartnerCutsPaths

/-! Exact old-axis and fresh-WIRE direction words of the actual common-cut compiler. -/

@[expose] public section
namespace PushPuzzle.Push.Partner.Cuts

open PushS

/-- Inspect one old or fresh axis of the simultaneous cut. -/
def cutValue (l : PortLayout) (cut : ℕ) (axes leftValues rightValues : List Bool) (i : ℕ) : Bool :=
  let count := (active l cut).length
  if i < cut then axes.getD i false
  else if i < cut + count then leftValues.getD (cut + count - 1 - i) false
  else if i < cut + 2 * count then rightValues.getD (i - cut - count) false
  else axes.getD (i - 2 * count) false

/-- The full physical-axis word, retaining all old axes and independently specifying the new left/right incidences. -/
def cutState (l : PortLayout) (cut : ℕ) (axes leftValues rightValues : List Bool) : List Bool :=
  (List.range (compile l cut).portCount).map (cutValue l cut axes leftValues rightValues)

/-- Read the original direction word at its unchanged or shifted original ports. -/
def cutRestrict (l : PortLayout) (cut : ℕ) (axes : List Bool) : List Bool :=
  (List.range l.portCount).map fun i => axes.getD (shift cut (active l cut).length i) false

/-- Original right-endpoint directions, optionally negated, in the actual sorted active-arc order. -/
def activeValues (l : PortLayout) (cut : ℕ) (axes : List Bool) (negate : Bool) : List Bool :=
  (active l cut).map fun ab => if negate then !(axes.getD ab.2 false) else axes.getD ab.2 false

/-- Consistent alternating directions on each actual fresh three-axis chain. -/
def cutExtend (l : PortLayout) (cut : ℕ) (axes : List Bool) : List Bool :=
  cutState l cut axes (activeValues l cut axes false) (activeValues l cut axes true)

@[simp] theorem cutState_length (l : PortLayout) (cut : ℕ) (axes leftValues rightValues : List Bool) :
    (cutState l cut axes leftValues rightValues).length = (compile l cut).portCount := by
  simp only [cutState, List.length_map, List.length_range]

@[simp] theorem cutRestrict_length (l : PortLayout) (cut : ℕ) (axes : List Bool) :
    (cutRestrict l cut axes).length = l.portCount := by simp only [cutRestrict, List.length_map, List.length_range]

private theorem cutState_get (l : PortLayout) (cut : ℕ) (axes leftValues rightValues : List Bool)
    {i : ℕ} (hi : i < (compile l cut).portCount) :
    (cutState l cut axes leftValues rightValues).getD i false = cutValue l cut axes leftValues rightValues i := by
  rw [List.getD_eq_getElem _ _ (by simpa only [cutState_length] using hi)]
  simp only [cutState, List.getElem_map, List.getElem_range]

theorem cutState_old (l : PortLayout) (cut : ℕ) (axes leftValues rightValues : List Bool)
    {i : ℕ} (hi : i < l.portCount) :
    (cutState l cut axes leftValues rightValues).getD (shift cut (active l cut).length i) false = axes.getD i false := by
  rw [cutState_get l cut axes leftValues rightValues (shift_lt cut _ hi)]
  unfold cutValue shift
  dsimp only
  split_ifs <;> try omega
  all_goals first
    | rfl
    | exact congrArg (fun j => axes.getD j false) (Nat.add_sub_cancel i _)

theorem cutState_left (l : PortLayout) (cut : ℕ) (hc : cut ≤ l.portCount)
    (axes leftValues rightValues : List Bool) {j : ℕ} (hj : j < (active l cut).length) :
    (cutState l cut axes leftValues rightValues).getD (left cut (active l cut).length j) false = leftValues.getD j false := by
  have hb := left_bounds (cut := cut) hj
  have hlt : left cut (active l cut).length j < (compile l cut).portCount := by change _ < l.portCount + 2 * _; omega
  rw [cutState_get l cut axes leftValues rightValues hlt]
  have hidx : cut + (active l cut).length - 1 - left cut (active l cut).length j = j := by unfold left; omega
  simp only [cutValue, ite_eq_right (show ¬left cut (active l cut).length j < cut by omega), ite_eq_left hb.2, hidx]

theorem cutState_right (l : PortLayout) (cut : ℕ) (hc : cut ≤ l.portCount)
    (axes leftValues rightValues : List Bool) {j : ℕ} (hj : j < (active l cut).length) :
    (cutState l cut axes leftValues rightValues).getD (right cut (active l cut).length j) false = rightValues.getD j false := by
  have hb := right_bounds (cut := cut) hj
  have hlt : right cut (active l cut).length j < (compile l cut).portCount := by change _ < l.portCount + 2 * _; omega
  rw [cutState_get l cut axes leftValues rightValues hlt]
  have hidx : right cut (active l cut).length j - cut - (active l cut).length = j := by unfold right; omega
  simp only [cutValue, ite_eq_right (show ¬right cut (active l cut).length j < cut by omega),
    ite_eq_right (show ¬right cut (active l cut).length j < cut + (active l cut).length by omega), ite_eq_left hb.2, hidx]

theorem cutRestrict_get (l : PortLayout) (cut : ℕ) (axes : List Bool) {i : ℕ} (hi : i < l.portCount) :
    (cutRestrict l cut axes).getD i false = axes.getD (shift cut (active l cut).length i) false := by
  rw [List.getD_eq_getElem _ _ (by simpa only [cutRestrict_length] using hi)]
  simp only [cutRestrict, List.getElem_map, List.getElem_range]

theorem activeValues_get {l : PortLayout} {cut : ℕ} {p : (ℕ × ℕ) × ℕ}
    (hp : p ∈ (active l cut).zipIdx) (axes : List Bool) (negate : Bool) :
    (activeValues l cut axes negate).getD p.2 false = if negate then !(axes.getD p.1.2 false) else axes.getD p.1.2 false := by
  have hi : p.2 < (active l cut).length := by simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx hp
  rw [List.getD_eq_getElem _ _ (by simpa only [activeValues, List.length_map] using hi)]
  simp only [activeValues, List.getElem_map]
  have he := List.fst_eq_of_mem_zipIdx hp
  simp only [Nat.sub_zero] at he
  rw [← he]

/-- The actual common-cut axis emitter restores the complete original word under restriction. -/
theorem cutRestrict_extend (l : PortLayout) (cut : ℕ) (axes : List Bool) (hlen : axes.length = l.portCount) :
    cutRestrict l cut (cutExtend l cut axes) = axes := by
  apply List.ext_getElem (by simpa only [cutRestrict_length] using hlen.symm)
  intro i hi hj
  have hb : i < l.portCount := by simpa only [cutRestrict_length] using hi
  have hr := cutRestrict_get l cut (cutExtend l cut axes) hb
  have hvalue : (cutExtend l cut axes).getD (shift cut (active l cut).length i) false = axes.getD i false :=
    cutState_old l cut axes _ _ hb
  rw [hvalue] at hr
  simpa only [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] using hr

end PushPuzzle.Push.Partner.Cuts
