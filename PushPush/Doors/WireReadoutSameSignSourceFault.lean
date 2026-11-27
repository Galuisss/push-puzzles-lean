/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.WireReadoutSameSignSource
public import PushPush.Doors.WireReadoutExtended

/-! The emitted B/C same-sign faults satisfy the complete four-box fault certificate. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source.Stock

open PushFS (Cell Direction Adjacent)

variable {I : Instance}

def sameSignBFault (storage : Bool) (S : Stock I)
    (index : Fin (layout storage I).wires.length)
    (hsignal : S.signal = wirePositionRaw (layout storage I) index.val (layout storage I).wires[index] 3)
    (hsame : decide ((layout storage I).wireY index.val (layout storage I).wires[index] <
      (layout storage I).wireV index.val (layout storage I).wires[index]) =
        (layout storage I).wires[index].sourceSouth)
    (near : Cell (layout storage I).width (layout storage I).height)
    (ha : Adjacent (wireDirection (layout storage I) index.val (layout storage I).wires[index] 3)
      (wirePosition storage I index.val index.isLt (layout storage I).wires[index]
        (List.getElem_mem index.isLt) 3) near) : ExtendedFault storage I S := by
  let e := (layout storage I).wires[index]
  let he := List.getElem_mem index.isLt
  let signal := wirePosition storage I index.val index.isLt e he 3
  let extra := wireStop storage I index.val index.isLt e he 2
  let removed := wireStop storage I index.val index.isLt e he 3
  let remote := wireStop storage I index.val index.isLt e he 1
  have hei : (e, index.val) ∈ ((layout storage I).wires).zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (by simp [e, index.isLt])
  have hc : Wire.Corner (wireDirection (layout storage I) index.val e 3) signal extra removed :=
    wire_private_corner_geometry storage I hei 3 (by decide) (by decide)
  have hext := B_same_sign_corner storage I index hsame near ha
  have hx : near.1.val = Layout.wireB index.val := by
    have hd : wireDirection (layout storage I) index.val e 3 = .north ∨
        wireDirection (layout storage I) index.val e 3 = .south := by
      change (if (layout storage I).wireY index.val e < (layout storage I).wireV index.val e then Direction.south else .north) = .north ∨
        (if (layout storage I).wireY index.val e < (layout storage I).wireV index.val e then Direction.south else .north) = .south
      split <;> simp
    have hsigx : signal.1.val = Layout.wireB index.val := rfl
    change Adjacent (wireDirection (layout storage I) index.val e 3) signal near at ha
    rcases hd with hd | hd <;> rw [hd] at ha <;> exact (congrArg Fin.val ha.1).trans hsigx
  have hfree := B_same_sign_free_columns (layout storage I) index.val near remote hx rfl
  refine {
    normal := wireDirection (layout storage I) index.val e 3
    forward := .west
    signal := signal
    near := near
    extra := extra
    removed := removed
    remote := remote
    normalCorner := hc
    nearAdj := ha
    extendedCorner := hext.1
    extraAdj := hext.2
    extra_pin := wireStopRaw_pin_mem storage I hei 2 (by decide)
    removed_pin := wireStopRaw_pin_mem storage I hei 3 (by decide)
    remote_pin := wireStopRaw_pin_mem storage I hei 1 (by decide)
    signal_raw := hsignal.symm
    signal_private := wire_private_position _ _ index.isLt e 3 (by decide) (by decide)
    near_margin := ?_
    remote_ne_removed := ?_
    removed_ne_near := normal_near_ne_removed hc ha
    horizontal := Or.inr rfl
    free_near := hfree.1
    free_remote := hfree.2 }
  · rw [hx]
    have hi := index.isLt
    dsimp [Layout.wireB, Layout.rackX]
    omega
  · intro heq
    have hxx := congrArg (fun p => p.1.val) heq
    change Layout.wireA index.val = Layout.wireB index.val at hxx
    dsimp [Layout.wireA, Layout.wireB] at hxx
    omega

def sameSignCFault (storage : Bool) (S : Stock I)
    (index : Fin (layout storage I).wires.length)
    (hsignal : S.signal = wirePositionRaw (layout storage I) index.val (layout storage I).wires[index] 5)
    (hsame : (layout storage I).wires[index].targetSouth =
      decide ((layout storage I).wireY index.val (layout storage I).wires[index] <
        (layout storage I).wireV index.val (layout storage I).wires[index]))
    (near : Cell (layout storage I).width (layout storage I).height)
    (ha : Adjacent (wireDirection (layout storage I) index.val (layout storage I).wires[index] 5)
      (wirePosition storage I index.val index.isLt (layout storage I).wires[index]
        (List.getElem_mem index.isLt) 5) near) : ExtendedFault storage I S := by
  let e := (layout storage I).wires[index]
  let he := List.getElem_mem index.isLt
  let signal := wirePosition storage I index.val index.isLt e he 5
  let extra := wireStop storage I index.val index.isLt e he 4
  let removed := wireStop storage I index.val index.isLt e he 5
  let remote := wireStop storage I index.val index.isLt e he 3
  have hei : (e, index.val) ∈ ((layout storage I).wires).zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (by simp [e, index.isLt])
  have hc : Wire.Corner (wireDirection (layout storage I) index.val e 5) signal extra removed :=
    wire_private_corner_geometry storage I hei 5 (by decide) (by decide)
  have hext := C_same_sign_corner storage I index hsame near ha
  have hx : near.1.val = Layout.wireC index.val := by
    have hd : wireDirection (layout storage I) index.val e 5 = .north ∨
        wireDirection (layout storage I) index.val e 5 = .south := by
      change (if e.targetSouth then Direction.south else .north) = .north ∨
        (if e.targetSouth then Direction.south else .north) = .south
      cases e.targetSouth <;> simp
    have hsigx : signal.1.val = Layout.wireC index.val := rfl
    change Adjacent (wireDirection (layout storage I) index.val e 5) signal near at ha
    rcases hd with hd | hd <;> rw [hd] at ha <;> exact (congrArg Fin.val ha.1).trans hsigx
  have hfree := C_same_sign_free_columns (layout storage I) index.val near remote hx rfl
  refine {
    normal := wireDirection (layout storage I) index.val e 5
    forward := .east
    signal := signal
    near := near
    extra := extra
    removed := removed
    remote := remote
    normalCorner := hc
    nearAdj := ha
    extendedCorner := hext.1
    extraAdj := hext.2
    extra_pin := wireStopRaw_pin_mem storage I hei 4 (by decide)
    removed_pin := wireStopRaw_pin_mem storage I hei 5 (by decide)
    remote_pin := wireStopRaw_pin_mem storage I hei 3 (by decide)
    signal_raw := hsignal.symm
    signal_private := wire_private_position _ _ index.isLt e 5 (by decide) (by decide)
    near_margin := ?_
    remote_ne_removed := ?_
    removed_ne_near := normal_near_ne_removed hc ha
    horizontal := Or.inl rfl
    free_near := hfree.1
    free_remote := hfree.2 }
  · rw [hx]
    have hi := index.isLt
    dsimp [Layout.wireC, Layout.rackX]
    omega
  · intro heq
    have hxx := congrArg (fun p => p.1.val) heq
    change Layout.wireB index.val = Layout.wireC index.val at hxx
    dsimp [Layout.wireB, Layout.wireC] at hxx
    omega

end PushPuzzle.PushPush.Doors.Source.Stock
