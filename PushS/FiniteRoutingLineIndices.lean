/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingLineWalking
public import Mathlib.Data.List.GetD

/-! Literal physical-label indices at line/tool interfaces. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting.Line

open PushFS

def ownedCount (w : ℕ) (atoms : List Atom) : ℕ := (ownedPositions w false atoms).length

private theorem ownedPositions_length (w : ℕ) (atoms : List Atom) (q : Bool) :
    (ownedPositions w q atoms).length = ownedCount w atoms := by
  induction atoms with
  | nil => rfl
  | cons a atoms ih =>
    simp only [ownedPositions, List.length_append, List.length_map, a.positions_length w q, ih]
    simp only [ownedCount, ownedPositions, List.length_append, List.length_map]

theorem positions_split_length (w : ℕ) (pre post : List Atom) :
    (positions w false (pre++post)).length = ownedCount w pre+(positions w false post).length := by
  rw [positions_split]
  simp only [List.length_append, List.length_map, ownedPositions_length]

def tailLabel (w : ℕ) (pre post : List Atom) (i : Label w post) : Label w (pre++post) :=
  ⟨ownedCount w pre+i.val, by rw [positions_split_length]; have := i.isLt; omega⟩

theorem tail_position (w : ℕ) (pre post : List Atom) (q : Bool) (i : Label w post) :
    position w (pre++post) q (tailLabel w pre post i) = span w pre+position w post q i := by
  have hi : i.val < (positions w q post).length := by simpa only [positions_length] using i.isLt
  have hn : ¬ownedCount w pre+i.val < ownedCount w pre := by omega
  have hh := congrArg (fun xs : List ℕ => xs[ownedCount w pre+i.val]?) (positions_split w q pre post)
  simp only [List.getElem?_append, List.getElem?_map, ownedPositions_length,
    hn, ite_false, Nat.add_sub_cancel_left, List.getElem?_eq_getElem hi] at hh
  have hlen : ownedCount w pre+i.val < (positions w q (pre++post)).length := by
    have ht := (tailLabel w pre post i).isLt
    change ownedCount w pre+i.val < (positions w false (pre++post)).length at ht
    simpa only [positions_length] using ht
  simp only [List.getElem?_eq_getElem hlen, Option.map_some, Option.some.injEq] at hh
  simpa only [position, tailLabel, List.get_eq_getElem] using hh

@[simp] theorem ownedCount_line (w n : ℕ) : ownedCount w [.line n] = n := by
  simp [ownedCount, ownedPositions, Atom.positions]

@[simp] theorem ownedCount_flip (w : ℕ) : ownedCount w [.flip] = 2 := rfl
@[simp] theorem ownedCount_parity (w : ℕ) : ownedCount w [.parity] = 1 := rfl

def lineLabel (w n : ℕ) (post : List Atom) (i : Fin n) : Label w (.line n::post) :=
  ⟨i.val, by simp only [positions, Atom.positions, List.length_append, List.length_map, List.length_range]; have := i.isLt; omega⟩

theorem line_position (w n : ℕ) (post : List Atom) (q : Bool) (i : Fin n) :
    position w (.line n::post) q (lineLabel w n post i) = 2*i.val+q.toNat := by
  have hi := i.isLt
  simp [position, positions, Atom.positions, lineLabel, List.get_eq_getElem,
    List.getElem_append_left, hi]

private theorem positions_head (w : ℕ) (atoms : List Atom) (q : Bool) :
    (positions w q atoms).headD 0 = q.toNat := by
  induction atoms with
  | nil => rfl
  | cons a atoms ih =>
    cases a with
    | line n =>
      cases n with
      | zero => simpa [positions, Atom.positions, Atom.span] using ih
      | succ n => exact positions_head_line w q (n+1) (by omega) atoms
    | flip => rfl
    | parity => rfl

theorem position_first (w : ℕ) (atoms : List Atom) (q : Bool) :
    position w atoms q (cutFirstLabel w atoms) = q.toNat := by
  have hh := positions_head w atoms q
  rw [List.headD_eq_getD, List.getD_eq_getElem (positions w q atoms) 0 (positions_length_pos w atoms q)] at hh
  exact hh

def lineEndpointLabel (w n : ℕ) (post : List Atom) : Label w (.line n::post) :=
  ⟨n, by
    have hh := positions_length_pos w post false
    simp only [positions, Atom.positions, List.length_append, List.length_map, List.length_range]
    omega⟩

theorem line_endpoint_position (w n : ℕ) (post : List Atom) (q : Bool) :
    position w (.line n::post) q (lineEndpointLabel w n post) = 2*n+q.toNat := by
  have hh := position_first w post q
  simp only [position, cutFirstLabel, List.get_eq_getElem] at hh
  simpa only [position, lineEndpointLabel, List.get_eq_getElem, positions, Atom.positions, Atom.span,
    List.getElem_append, List.length_map, List.length_range, Nat.lt_irrefl, dite_false,
    Nat.sub_self, List.getElem_map] using congrArg (2*n + ·) hh

end PushPuzzle.PushS.FiniteRouting.Line
