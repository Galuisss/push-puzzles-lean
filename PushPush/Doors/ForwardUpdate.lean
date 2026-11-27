/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.ForwardCollision
public import PushPush.Doors.MachineStateUpdate

/-! Exact finite inventory updates for physical door collisions. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell)

namespace Stock

variable {I : Instance}

-- Expand the full register inventory while isolating one door.
set_option maxHeartbeats 800000 in
theorem stationary_setRegister (storage : Bool) (S : Stock I)
    (i : Fin I.doors.length) (value : Register) :
    (S.setRegister i value).stationary storage =
      insert (doorCell storage I i value.row (by have := Register.row_bounds value; omega))
        (S.roomFrame storage i) := by
  have hi := Register.row_bounds (S.register i)
  have hfixed : S.registerPoint storage i ∉ (layout storage I).fixed := by
    apply fixed_door_clear storage I i (S.doorPoint storage i) rfl
    · dsimp [doorPoint]
      omega
    · dsimp [doorPoint]
      omega
  ext p
  have hguard : (p.1.val, p.2.val) ∈ (layout storage I).fixed → p ≠ S.doorPoint storage i := by
    intro hp he
    subst p
    exact hfixed hp
  simp only [stationary, registerPoints_setRegister, Layout.mem_raster,
    roomFrame, Finset.mem_union, Finset.mem_insert, Finset.mem_erase,
    registerPoint, doorPoint, doorCell, workCell, Layout.point,
    ne_eq, Prod.ext_iff, Fin.ext_iff] at hguard ⊢
  tauto

/-- A stock whose signal is at one door input has exactly two explicit room actors. -/
theorem boxes_at_door_input (storage : Bool) (S : Stock I) (i : Fin I.doors.length)
    (incoming : Register)
    (hsignal : S.signal = ((layout storage I).rackX - 1,
      doorBase i.val + incoming.row + (layout storage I).shift)) :
    S.boxes storage =
      insert (S.doorPoint storage i)
        (insert (doorCell storage I i incoming.row (by have := Register.row_bounds incoming; omega))
          (S.roomFrame storage i)) := by
  have hx : S.signal.1 < (layout storage I).width := by
    rw [hsignal]
    dsimp
    unfold Layout.width
    omega
  have hy : S.signal.2 < (layout storage I).height := by
    rw [hsignal]
    exact (doorCell storage I i incoming.row (by have := Register.row_bounds incoming; omega)).2.isLt
  rw [S.boxes_eq_insert_signal storage hx hy, S.stationary_eq_insert_doorPoint storage i]
  have he : S.signalCell storage hx hy =
      doorCell storage I i incoming.row (by have := Register.row_bounds incoming; omega) := by
    apply Prod.ext <;> apply Fin.ext
    · exact congrArg Prod.fst hsignal
    · exact congrArg Prod.snd hsignal
  rw [he, Finset.insert_comm]

/-- The old register and incoming signal collide, exchanging their physical roles. -/
theorem collide (storage : Bool) (S : Stock I) (i : Fin I.doors.length)
    (incoming : Register) (hne : S.register i ≠ incoming)
    (hsignal : S.signal = ((layout storage I).rackX - 1,
      doorBase i.val + incoming.row + (layout storage I).shift)) :
    Finite.Reachable 1 (S.canonical storage)
      (({(S.setRegister i incoming) with signal := ((layout storage I).rackX - 1,
        doorBase i.val + collisionRow (S.register i) incoming + (layout storage I).shift)} :
          Stock I).canonical storage) := by
  have hr := door_collision storage I i (S.register i) incoming hne (S.roomFrame storage i)
    (fun p hp => S.stationary_columns storage (Finset.mem_of_mem_erase hp))
    (fun p hp hmem => S.stationary_top storage hp (Finset.mem_of_mem_erase hmem))
    (S.roomFrame_clear storage i)
  have hin := S.boxes_at_door_input storage i incoming hsignal
  change Finite.Reachable 1 ⟨(layout storage I).corner, S.boxes storage⟩ _
  rw [hin]
  convert hr using 1 <;> try rfl
  apply PushFS.State.ext
  · rfl
  let next : Stock I := {(S.setRegister i incoming) with signal := ((layout storage I).rackX - 1,
    doorBase i.val + collisionRow (S.register i) incoming + (layout storage I).shift)}
  have hx : next.signal.1 < (layout storage I).width := by dsimp [next]; unfold Layout.width; omega
  have hy : next.signal.2 < (layout storage I).height := by
    exact (doorCell storage I i (collisionRow (S.register i) incoming)
      (by have := collisionRow_bounds (S.register i) incoming; omega)).2.isLt
  change next.boxes storage = _
  rw [next.boxes_eq_insert_signal storage hx hy]
  change insert (doorCell storage I i (collisionRow (S.register i) incoming)
    (by have := collisionRow_bounds (S.register i) incoming; omega))
    ((S.setRegister i incoming).stationary storage) = _
  rw [S.stationary_setRegister storage i incoming]

end Stock
end PushPuzzle.PushPush.Doors.Source
