/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.Encoding
public import PushFS.BitmapIsometry

/-! Exact player-target reorientation and polynomial-time quarter turns. -/

@[expose] public section
namespace PushPuzzle.Push

open PushFS Turing.MultiTapeTM

namespace Instance

variable {W H : ℕ}

/-- Reorient every initial box, the starting player, and the required player destination. -/
def reorient (I : Instance) (e : GridIsometry I.width I.height W H) : Instance where
  width := W
  height := H
  initial := e.state I.initial
  target := e.cells I.target
  player_empty := fun h => I.player_empty ((e.mem_boxes I.initial I.initial.player).mp h)

/-- The common step-checker instance follows the same complete grid isometry. -/
private theorem reorient_toStorage (I : Instance) (e : GridIsometry I.width I.height W H) :
    (I.reorient e).toStorage = e.reorientInstance I.toStorage := by
  simp only [reorient, toStorage, GridIsometry.reorientInstance, GridIsometry.board,
    GridIsometry.state, Finset.map_empty]
  rfl

/-- Swap the rectangle's two coordinates. -/
def transposed (I : Instance) : Instance :=
  I.reorient (GridIsometry.transpose I.width I.height)

/-- Reflect across the vertical center line. -/
def reflectedX (I : Instance) : Instance :=
  I.reorient (GridIsometry.reflectX I.width I.height)

/-- Rotate the entire ordinary game by a clockwise quarter turn. -/
def clockwise (I : Instance) : Instance := I.transposed.reflectedX

/-- Rotate by two clockwise quarter turns. -/
def halfTurn (I : Instance) : Instance := I.clockwise.clockwise

/-- Rotate by three clockwise quarter turns. -/
def counterclockwise (I : Instance) : Instance := I.halfTurn.clockwise

/-- Reflect across the horizontal center line. -/
def reflectedY (I : Instance) : Instance := I.transposed.reflectedX.transposed

end Instance

namespace Encoding

private abbrev encFields : (PushFS.Instance × ℕ × ℕ) ↪ List Bool :=
  encPair PushFS.encoding (encPair encUnary encUnary)

private theorem data_polyTime : ComputableInPolyTime data encoding encFields :=
  ComputableInPolyTime.of_eq fun _ => rfl

private theorem transpose_polyTime :
    ComputableInPolyTime
      (fun q : PushFS.Instance × ℕ × ℕ => (q.1.transposed, q.2.2, q.2.1))
      encFields encFields := by
  unfold encFields
  fun_prop

private theorem reflectX_polyTime :
    ComputableInPolyTime
      (fun q : PushFS.Instance × ℕ × ℕ => (q.1.reflectedX, q.1.width - (q.2.1 + 1), q.2.2))
      encFields encFields := by
  have hwidth : ComputableInPolyTime PushFS.Instance.width PushFS.encoding encUnary :=
    PushFS.Encoding.encData_width_polyTime PushFS.Encoding.data_polyTime
  unfold encFields
  fun_prop

private theorem data_transposed (I : Instance) :
    data I.transposed = (I.toStorage.transposed, I.target.2.val, I.target.1.val) := by
  change ((I.reorient _).toStorage, _, _) = _
  rw [Instance.reorient_toStorage]
  rfl

private theorem data_reflectedX (I : Instance) :
    data I.reflectedX =
      (I.toStorage.reflectedX, I.width - (I.target.1.val + 1), I.target.2.val) := by
  change ((I.reorient _).toStorage, _, _) = _
  rw [Instance.reorient_toStorage]
  rfl

end Encoding

namespace Instance

/-- Transposition writes the exact dense output in polynomial time. -/
@[fun_prop] theorem transposed_polyTime :
    ComputableInPolyTime transposed encoding encoding :=
  (Encoding.transpose_polyTime.comp Encoding.data_polyTime).of_enc_eq
    (fun I => congrArg Encoding.encFields (Encoding.data_transposed I))

/-- Horizontal reflection writes the exact dense output in polynomial time. -/
@[fun_prop] theorem reflectedX_polyTime :
    ComputableInPolyTime reflectedX encoding encoding :=
  (Encoding.reflectX_polyTime.comp Encoding.data_polyTime).of_enc_eq
    (fun I => congrArg Encoding.encFields (Encoding.data_reflectedX I))

/-- The clockwise quarter turn has a standard polynomial-time machine certificate. -/
@[fun_prop] theorem clockwise_polyTime : ComputableInPolyTime clockwise encoding encoding :=
  reflectedX_polyTime.comp transposed_polyTime

@[fun_prop] theorem halfTurn_polyTime : ComputableInPolyTime halfTurn encoding encoding :=
  clockwise_polyTime.comp clockwise_polyTime

@[fun_prop] theorem counterclockwise_polyTime :
    ComputableInPolyTime counterclockwise encoding encoding :=
  clockwise_polyTime.comp halfTurn_polyTime

@[fun_prop] theorem reflectedY_polyTime : ComputableInPolyTime reflectedY encoding encoding :=
  transposed_polyTime.comp (reflectedX_polyTime.comp transposed_polyTime)

end Instance
end PushPuzzle.Push
