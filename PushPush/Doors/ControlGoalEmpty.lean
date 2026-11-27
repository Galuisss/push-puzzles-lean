/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.ControlGoal

/-! Exact-target readout also covers source networks with no doors. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open Cslib.Complexity

private theorem wires_nil_of_no_doors (storage : Bool) (I : Instance) (hzero : I.doors.length = 0) :
    (layout storage I).wires = [] := by
  simp [layout, wires, internalWires, arrivalWires, choiceWires, skipWires, cleanupWires, hzero]

private theorem Stock.signal_of_goals_no_doors (I : Instance) (hzero : I.doors.length = 0)
    (S : Stock I) (hgoal : S.boxes true = (puzzle true I).board.goals) :
    S.signal = ((layout true I).rackX - 1, targetRow I + (layout true I).shift) := by
  let p := workCell true I (targetRow I) (targetRow_fit true I)
  have hstop : (layout true I).stop = targetRow I := by simp [layout, hzero]
  have hp : p ∈ (puzzle true I).board.goals := by
    apply ((layout true I).mem_raster _ _).mpr
    apply Finset.mem_union_right
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨targetRow I, ?_, rfl⟩
    rw [hstop]
    exact List.mem_cons_self
  have hp : p ∈ S.boxes true := hgoal.symm ▸ hp
  have hp := ((layout true I).mem_raster _ _).mp hp
  change ((layout true I).rackX - 1, targetRow I + (layout true I).shift) ∈ S.rawBoxes true at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨row, hrow, he⟩ := ((layout true I).fixed_working_iff _).mp hp
      have hroweq : row = targetRow I := by omega
      exact False.elim (targetRow_free true I (hroweq ▸ hrow))
    · obtain ⟨door, _, _⟩ := Finset.mem_image.mp hp
      have hi := door.isLt
      omega
  · exact (Finset.mem_singleton.mp hp).symm

private theorem ControlPhase.location_of_target_no_doors {I : Instance} (hzero : I.doors.length = 0)
    {source : State} {C : Control true I} (hphase : ControlPhase true I source C)
    (hlabel : source.location ∈ labels I)
    (hpoint : C.signal.point = ((layout true I).rackX - 1,
      targetRow I + (layout true I).shift)) : source.location = I.target := by
  have hh := chamberHeight_ge I
  cases hphase with
  | junction j p hj hp =>
    have hy := congrArg Prod.snd hpoint
    change inputRow I (rank I source.location) j p + (layout true I).shift =
      targetRow I + (layout true I).shift at hy
    have he : inputRow I (rank I source.location) j p = targetRow I := Nat.add_right_cancel hy
    have hl : LaunchRow I (targetRow I) := Or.inr ⟨rank I I.target, 0, Or.inl rfl⟩
    exact False.elim (inputRow_not_launch I _ _ _ hp (he.symm ▸ hl))
  | upper j hj hused =>
    have hy := congrArg Prod.snd hpoint
    change upperRow I (rank I source.location) j + (layout true I).shift =
      targetRow I + (layout true I).shift at hy
    have he : upperRow I (rank I source.location) j = targetRow I := Nat.add_right_cancel hy
    have hid := room_row_injective I hj (slots_pos I) (by omega : 3 < chamberHeight I)
      (by omega : 3 < chamberHeight I) he
    exact (rank_eq_iff I hlabel).mp hid.1
  | lower j hj hused =>
    have hy := congrArg Prod.snd hpoint
    change lowerRow I (rank I source.location) j + (layout true I).shift =
      targetRow I + (layout true I).shift at hy
    have he : lowerRow I (rank I source.location) j = targetRow I := Nat.add_right_cancel hy
    have he' : roomBase I (rank I source.location) j + (chamberHeight I - 3) =
        roomBase I (rank I I.target) 0 + 3 := by
      unfold lowerRow targetRow upperRow at he
      omega
    have hid := room_row_injective I hj (slots_pos I) (by omega : chamberHeight I - 3 < chamberHeight I)
      (by omega : 3 < chamberHeight I) he'
    omega
  | junctionWire index corner j p hj hp htarget =>
    have hi := index.isLt
    have hlen := congrArg List.length (wires_nil_of_no_doors true I hzero)
    simp only [List.length_nil] at hlen
    omega
  | call door channel stored incoming hentry hsession =>
    have hi := door.isLt
    omega
  | result door channel stored incoming keep hentry hsession =>
    have hi := door.isLt
    omega
  | doorWire door channel stored incoming index corner hentry hsession htarget =>
    have hi := door.isLt
    omega

/-- Every safe complete control stock at the exact target witnesses original source acceptance. -/
private theorem Control.SourceSafe.source_of_goals {I : Instance} {C : Control true I}
    (hsafe : C.SourceSafe) (hgoal : C.stock.boxes true = (puzzle true I).board.goals) :
    I ∈ SelfClosingDoor.Reachability := by
  by_cases hdoors : 0 < I.doors.length
  · exact hsafe.source_of_goals_nonempty hdoors hgoal
  · have hzero : I.doors.length = 0 := by omega
    rcases hsafe with haccept | ⟨source, hreach, hphase⟩
    · exact haccept
    · refine ⟨source, hreach, ?_⟩
      exact hphase.location_of_target_no_doors hzero (reachable_location_mem I hreach)
        (Stock.signal_of_goals_no_doors I hzero C.stock hgoal)

/-- The complete safe control machine is sound for actual exact-storage target inventories. -/
theorem Control.Reachable.source_of_goals {I : Instance} {C : Control true I}
    (hr : Control.Reachable (Control.initial true I) C)
    (hgoal : C.stock.boxes true = (puzzle true I).board.goals) :
    I ∈ SelfClosingDoor.Reachability := hr.sourceSafe.source_of_goals hgoal

end PushPuzzle.PushPush.Doors.Source
