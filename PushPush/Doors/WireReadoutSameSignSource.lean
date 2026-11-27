/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.WireReadoutNeighbor

/-! Actual source geometry and free columns of the two same-sign attraction faults. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell Direction Adjacent)

theorem normal_near_ne_removed {w h : ℕ} {normal : Direction}
    {signal extra removed near : Cell w h}
    (hc : Wire.Corner normal signal extra removed) (ha : Adjacent normal signal near) :
    removed ≠ near := by
  intro he
  have hgap := hc.2.2.2
  have hp := ha.position
  rw [he] at hgap
  omega

theorem B_same_sign_corner (storage : Bool) (I : Instance)
    (index : Fin (layout storage I).wires.length)
    (hsame : decide ((layout storage I).wireY index.val (layout storage I).wires[index] <
      (layout storage I).wireV index.val (layout storage I).wires[index]) =
        (layout storage I).wires[index].sourceSouth)
    (near : Cell (layout storage I).width (layout storage I).height)
    (ha : Adjacent (wireDirection (layout storage I) index.val (layout storage I).wires[index] 3)
      (wirePosition storage I index.val index.isLt (layout storage I).wires[index]
        (List.getElem_mem index.isLt) 3) near) :
    let e := (layout storage I).wires[index]
    let signal := wirePosition storage I index.val index.isLt e (List.getElem_mem index.isLt) 3
    let extra := wireStop storage I index.val index.isLt e (List.getElem_mem index.isLt) 2
    let remote := wireStop storage I index.val index.isLt e (List.getElem_mem index.isLt) 1
    Wire.Corner .west near signal remote ∧ Adjacent .east signal extra := by
  intro e signal extra remote
  let side := decide ((layout storage I).wireY index.val e < (layout storage I).wireV index.val e)
  have hdir : wireDirection (layout storage I) index.val e 3 =
      if side then .south else .north := by simp [wireDirection, side]
  change Adjacent (wireDirection (layout storage I) index.val e 3) signal near at ha
  rw [hdir] at ha
  have hax : near.1.val = Layout.wireB index.val := by
    have hx : signal.1.val = Layout.wireB index.val := rfl
    cases hs : side <;> simp only [hs, Bool.false_eq_true, ite_false, ite_true] at ha <;>
      exact (congrArg Fin.val ha.1).trans hx
  have hay : near.2.val = Layout.beside side ((layout storage I).wireY index.val e) := by
    have hy : signal.2.val = (layout storage I).wireY index.val e := rfl
    cases hs : side <;> simp only [hs, Bool.false_eq_true, ite_false, ite_true,
      Adjacent, Layout.beside] at ha ⊢ <;> omega
  apply Wire.layout_B_same_sign (layout storage I) index.val e hsame near signal extra remote
  · exact Prod.ext hax hay
  · rfl
  · rfl
  · rfl

theorem C_same_sign_corner (storage : Bool) (I : Instance)
    (index : Fin (layout storage I).wires.length)
    (hsame : (layout storage I).wires[index].targetSouth =
      decide ((layout storage I).wireY index.val (layout storage I).wires[index] <
        (layout storage I).wireV index.val (layout storage I).wires[index]))
    (near : Cell (layout storage I).width (layout storage I).height)
    (ha : Adjacent (wireDirection (layout storage I) index.val (layout storage I).wires[index] 5)
      (wirePosition storage I index.val index.isLt (layout storage I).wires[index]
        (List.getElem_mem index.isLt) 5) near) :
    let e := (layout storage I).wires[index]
    let signal := wirePosition storage I index.val index.isLt e (List.getElem_mem index.isLt) 5
    let extra := wireStop storage I index.val index.isLt e (List.getElem_mem index.isLt) 4
    let remote := wireStop storage I index.val index.isLt e (List.getElem_mem index.isLt) 3
    Wire.Corner .east near signal remote ∧ Adjacent .west signal extra := by
  intro e signal extra remote
  have hax : near.1.val = Layout.wireC index.val := by
    change Adjacent (if e.targetSouth then .south else .north) signal near at ha
    have hx : signal.1.val = Layout.wireC index.val := rfl
    cases hs : e.targetSouth <;> simp only [hs, Bool.false_eq_true, ite_false, ite_true] at ha <;>
      exact (congrArg Fin.val ha.1).trans hx
  have hay : near.2.val = Layout.beside e.targetSouth ((layout storage I).wireV index.val e) := by
    change Adjacent (if e.targetSouth then .south else .north) signal near at ha
    have hy : signal.2.val = (layout storage I).wireV index.val e := rfl
    cases hs : e.targetSouth <;> simp only [hs, Bool.false_eq_true, ite_false, ite_true,
      Adjacent, Layout.beside] at ha ⊢ <;> omega
  apply Wire.layout_C_same_sign (layout storage I) index.val e hsame near signal extra remote
  · exact Prod.ext hax hay
  · rfl
  · rfl
  · rfl

theorem B_same_sign_free_columns (L : Layout) (i : ℕ) (near remote : Cell L.width L.height)
    (hnear : near.1.val = Layout.wireB i) (hremote : remote.1.val = Layout.wireA i) :
    (∀ landed, Adjacent .west near landed → ∀ p ∈ L.pins, p.1 ≠ landed.1.val) ∧
      (∀ landed, Adjacent .west landed remote → ∀ p ∈ L.pins, p.1 ≠ landed.1.val) := by
  constructor
  · intro landed ha p hp he
    have hx : landed.1.val = Layout.wireB i - 1 := by have := ha.1; omega
    exact (L.pins_not_free_column i hp).2.1 (he.trans hx)
  · intro landed ha p hp he
    have hx : landed.1.val = Layout.wireA i + 1 := by have := ha.1; omega
    exact (L.pins_not_free_column i hp).1 (he.trans hx)

theorem C_same_sign_free_columns (L : Layout) (i : ℕ) (near remote : Cell L.width L.height)
    (hnear : near.1.val = Layout.wireC i) (hremote : remote.1.val = Layout.wireB i) :
    (∀ landed, Adjacent .east near landed → ∀ p ∈ L.pins, p.1 ≠ landed.1.val) ∧
      (∀ landed, Adjacent .east landed remote → ∀ p ∈ L.pins, p.1 ≠ landed.1.val) := by
  constructor
  · intro landed ha p hp he
    have hx : landed.1.val = Layout.wireC i + 1 := by have := ha.1; omega
    exact (L.pins_not_free_column i hp).2.2 (he.trans hx)
  · intro landed ha p hp he
    have hx : landed.1.val = Layout.wireB i - 1 := by have := ha.1; omega
    exact (L.pins_not_free_column i hp).2.1 (he.trans hx)

end PushPuzzle.PushPush.Doors.Source
