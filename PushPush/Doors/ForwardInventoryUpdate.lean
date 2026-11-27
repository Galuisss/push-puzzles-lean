/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.ForwardUpdate
public import PushPush.Doors.ForwardSignal
public import PushPush.Doors.ForwardControl

/-! Exact erased-and-inserted box inventories for physical controller transitions. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source.Stock

open PushFS (Cell)

variable {I : Instance}

/-- A collision exchanges the moving register's role with the incoming signal. -/
theorem boxes_after_collision (storage : Bool) (S : Stock I) (i : Fin I.doors.length)
    (incoming : Register) (hne : S.register i ≠ incoming)
    (hsignal : S.signal = atRow storage I (doorBase i.val + incoming.row)) :
    (({(S.setRegister i incoming) with
      signal := atRow storage I (doorBase i.val + collisionRow (S.register i) incoming)} : Stock I).boxes storage) =
      insert (doorCell storage I i (collisionRow (S.register i) incoming)
        (by have := collisionRow_bounds (S.register i) incoming; omega))
        ((S.boxes storage).erase (S.doorPoint storage i)) := by
  let next : Stock I := {(S.setRegister i incoming) with
    signal := atRow storage I (doorBase i.val + collisionRow (S.register i) incoming)}
  let landing := doorCell storage I i (collisionRow (S.register i) incoming)
    (by have := collisionRow_bounds (S.register i) incoming; omega)
  have hn : next.signal = (landing.1.val, landing.2.val) := rfl
  change next.boxes storage = insert landing ((S.boxes storage).erase (S.doorPoint storage i))
  rw [next.boxes_at_signal storage landing hn]
  change insert landing ((S.setRegister i incoming).stationary storage) = _
  congr 1
  rw [S.stationary_setRegister storage i incoming, S.boxes_at_door_input storage i incoming hsignal]
  symm
  apply Finset.erase_insert
  simp only [Finset.mem_insert, not_or]
  refine ⟨?_, Finset.notMem_erase _ _⟩
  intro he
  have hr := congrArg (fun p => p.2.val) he
  dsimp [doorPoint] at hr
  apply hne
  apply Register.row_injective
  omega

/-- Moving the signal changes precisely its old and new unlabelled box cells. -/
theorem boxes_setSignal (storage : Bool) (S : Stock I)
    (source dest : Cell (layout storage I).width (layout storage I).height)
    (hsignal : S.signal = (source.1.val, source.2.val))
    (hsource : source ∉ S.stationary storage) :
    (({S with signal := (dest.1.val, dest.2.val)} : Stock I).boxes storage) =
      insert dest ((S.boxes storage).erase source) := by
  rw [boxes_at_signal storage ({S with signal := (dest.1.val, dest.2.val)} : Stock I) dest rfl,
    S.boxes_at_signal storage source hsignal, Finset.erase_insert hsource]
  rfl

end PushPuzzle.PushPush.Doors.Source.Stock
