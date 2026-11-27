/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Space.StateCode
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite

/-! Input projections and bitmap updates with polynomial-time machine certificates. -/

@[expose] public section

namespace PushPuzzle.PushFS


open Turing.MultiTapeTM
open ComputableInPolyTime

namespace Machine

/-- Exposing the proof-free input fields is identity on the encoded word. -/
@[fun_prop] theorem data_polyTime :
    ComputableInPolyTime Encoding.data encoding Encoding.encData :=
  of_eq fun _ => rfl

@[fun_prop] theorem width_polyTime :
    ComputableInPolyTime Instance.width encoding encUnary :=
  Encoding.encData_width_polyTime data_polyTime

@[fun_prop] theorem height_polyTime :
    ComputableInPolyTime Instance.height encoding encUnary :=
  Encoding.encData_height_polyTime data_polyTime

@[fun_prop] theorem area_polyTime :
    ComputableInPolyTime Instance.area encoding encUnary := by
  unfold Instance.area
  exact unary_mul.comp (width_polyTime.prod height_polyTime)

/-- The explicit rows, including walls, goals, boxes and player bits. -/
def rows (I : Instance) : List (List Encoding.Tile) := Encoding.rows I.board I.initial

@[fun_prop] theorem rows_polyTime :
    ComputableInPolyTime rows encoding (encList (encList Encoding.encTile)) :=
  Encoding.encData_rows_polyTime data_polyTime

/-- Cells in row-major order, with every flag retained. -/
def tiles (I : Instance) : List Encoding.Tile := (rows I).flatten

@[fun_prop] theorem tiles_polyTime :
    ComputableInPolyTime tiles encoding (encList Encoding.encTile) :=
  (flatten Encoding.encTile).comp rows_polyTime

/-- Project a selected bit stream without retaining the other cell flags. -/
def flags (f : Encoding.Tile → Bool) (I : Instance) : List Bool := (tiles I).map f

/-- Any fixed Boolean function of the four flags has a certified polynomial-time
streaming projection. -/
theorem flags_polyTime (f : Encoding.Tile → Bool) :
    ComputableInPolyTime (flags f) encoding encBits := by
  have hf : ComputableInPolyTime f Encoding.encTile encBool := of_finite f
  have hmap : ComputableInPolyTime (flags f) encoding (encList encBool) := by
    unfold flags
    fun_prop
  exact (bits_encList_polyTime encBool).2.comp hmap

/-- The initial dynamic state in row-major order: box bits then player bits. -/
def initialBits (I : Instance) : List Bool :=
  flags Encoding.Tile.box I ++ flags Encoding.Tile.player I

@[fun_prop] theorem initialBits_polyTime :
    ComputableInPolyTime initialBits encoding encBits :=
  (flags_polyTime Encoding.Tile.box).bitsAppend (flags_polyTime Encoding.Tile.player)

@[simp] theorem length_tiles (I : Instance) : (tiles I).length = I.area := by
  simp only [tiles, rows, Encoding.rows, List.length_flatten, List.map_ofFn,
    Function.comp_def, List.length_ofFn, List.ofFn_const, List.sum_replicate,
    smul_eq_mul, Instance.area, Nat.mul_comm]

@[simp] theorem length_flags (f : Encoding.Tile → Bool) (I : Instance) :
    (flags f I).length = I.area := by
  simp [flags]

@[simp] theorem length_initialBits (I : Instance) :
    (initialBits I).length = 2 * I.area := by
  simp [initialBits, two_mul]

/-- A projected input stream is exactly the corresponding row-major bit function. -/
theorem flags_eq_ofFn (f : Encoding.Tile → Bool) (I : Instance) :
    flags f I = List.ofFn fun i => f (Encoding.tile I.board I.initial (State.cellAt i)) := by
  rw [State.ofFn_cellAt (fun p => f (Encoding.tile I.board I.initial p))]
  simp [flags, tiles, rows, Encoding.rows, List.map_flatten, List.map_ofFn, Function.comp_def]

/-- The certified preprocessing emits exactly the search state's compact code. -/
private theorem initialBits_eq (I : Instance) : initialBits I = I.initial.bits := by
  simp only [initialBits, flags_eq_ofFn, State.bits, State.boxBits, State.playerBits, Encoding.tile]

/-- The initial state's compact encoding has a concrete polynomial-time machine. -/
theorem initial_state_encoding_polyTime :
    ComputableInPolyTime (fun I : Instance => State.encoding I.initial) encoding encBits :=
  initialBits_polyTime.of_enc_eq (fun I => (initialBits_eq I).symm)

/-- Random access to the explicit bit representation, rejecting out-of-range
positions with `false`. Unary indices are appropriate for the dense board. -/
def bitAt (p : List Bool × ℕ) : Bool := p.1[p.2]?.getD false

@[fun_prop] theorem bitAt_polyTime :
    ComputableInPolyTime bitAt (encPair encBits encUnary) encBool := by
  unfold bitAt
  fun_prop

/-- Write one bit; an out-of-range index leaves the word unchanged. -/
def setBit (p : List Bool × ℕ × Bool) : List Bool :=
  (List.range p.1.length).map fun i => if i == p.2.1 then p.2.2 else bitAt (p.1, i)

/-- Single-cell writes have an actual machine certificate. -/
@[fun_prop] theorem setBit_polyTime :
    ComputableInPolyTime setBit (encPair encBits (encPair encUnary encBool)) encBits := by
  unfold setBit
  apply mapToBitsWithInput
  · fun_prop
  · have hn : ComputableInPolyTime
        (fun p : (List Bool × ℕ × Bool) × ℕ => p.2 == p.1.2.1)
        (encPair (encPair encBits (encPair encUnary encBool)) encUnary) encBool := by
      apply unary_beq <;> fun_prop
    exact hn.ite' (by fun_prop) (by fun_prop)

@[simp] theorem length_setBit (p : List Bool × ℕ × Bool) :
    (setBit p).length = p.1.length := by simp [setBit]

/-- A bit write has precisely its intended local effect. -/
private theorem getElem_setBit (word : List Bool) (index : ℕ) (value : Bool) (i : ℕ)
    (hi : i < word.length) :
    (setBit (word, index, value))[i]'(by simpa using hi) =
      if i = index then value else word[i] := by
  simp [setBit, bitAt, hi]

/-- The bitmap update of a push removes its source box and inserts its target. -/
def pushBits (p : List Bool × ℕ × ℕ) : List Bool :=
  setBit (setBit (p.1, p.2.1, false), p.2.2, true)

@[fun_prop] theorem pushBits_polyTime :
    ComputableInPolyTime pushBits (encPair encBits (encPair encUnary encUnary)) encBits := by
  unfold pushBits
  fun_prop

@[simp] theorem length_pushBits (p : List Bool × ℕ × ℕ) :
    (pushBits p).length = p.1.length := by simp [pushBits]

/-- Complete specification of the two writes, including the equal-index case. -/
private theorem getElem_pushBits (word : List Bool) (src dst i : ℕ) (hi : i < word.length) :
    (pushBits (word, src, dst))[i]'(by simpa using hi) =
      if i = dst then true else if i = src then false else word[i] := by
  change (setBit (setBit (word, src, false), dst, true))[i]'(by simpa using hi) = _
  rw [getElem_setBit _ _ _ i (by simpa using hi), getElem_setBit _ _ _ i hi]

/-- The certified raw bitmap update is the exact finite-set update of a push.
Legality (walls and empty destination) is checked separately by `Move`. -/
theorem pushBits_boxBits {w h : ℕ} (s : State w h) (src dst : Cell w h) :
    pushBits (s.boxBits, (finProdFinEquiv src.swap).val, (finProdFinEquiv dst.swap).val) =
      (State.mk s.player (insert dst (s.boxes.erase src))).boxBits := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  have hil : i < s.boxBits.length := by simpa using hi
  have hin : i < h * w := by simpa [State.boxBits] using hil
  have index_eq (p : Cell w h) :
      i = (finProdFinEquiv p.swap).val ↔ State.cellAt (⟨i, hin⟩ : Fin (h * w)) = p := by
    rw [State.cellAt_eq_iff, Fin.ext_iff]
  rw [getElem_pushBits _ _ _ _ hil]
  simp only [State.boxBits, List.getElem_ofFn, Finset.mem_insert, Finset.mem_erase]
  simp only [index_eq]
  split_ifs <;> simp_all

end Machine

end PushPuzzle.PushFS
