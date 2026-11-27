/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ColumnScan
public import PushS.LineWalking
import all PushS.LinePush

/-! A genuine two-push commitment macro on the actual column-reader extension. -/

@[expose] public section
namespace PushPuzzle.Push.ColumnScan.Input

open PushFS PushS

variable (r : Input)

/-- The original source's southeast corner. -/
def sourceCorner : Cell r.width r.height :=
  (⟨r.width - 1, by have := r.width_pos; omega⟩,
    ⟨r.height - 1, by have := r.height_pos; omega⟩)

private theorem door_mem : r.door ∈ r.empty := by simp [empty]
private theorem upper_mem : r.upper ∈ r.empty := by simp [empty]
theorem bottom_mem : r.bottom ∈ r.empty := by simp [empty]

private theorem room_mem {q : Cell r.outputWidth r.outputHeight}
    (hx : q.1.val = r.width + 1) (hy : r.height ≤ q.2.val) : q ∈ r.empty := by
  apply Finset.mem_union_right
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega, hy⟩

private def roomEntry : Cell r.outputWidth r.outputHeight :=
  (⟨r.width + 1, by dsimp [outputWidth]; omega⟩,
    ⟨r.height, by have := r.length_ge_seven; dsimp [outputHeight]; omega⟩)

private def roomBottom : Cell r.outputWidth r.outputHeight :=
  ((r.roomEntry).1, r.bottom.2)

private theorem roomEntry_mem : r.roomEntry ∈ r.empty := r.room_mem rfl (by rfl)

private theorem roomBottom_mem : r.roomBottom ∈ r.empty := by
  apply r.room_mem rfl
  change r.height ≤ r.height + r.length - 1
  have := r.length_ge_seven
  omega

/-- The player position after consuming the upper seal hole. -/
def firstSeal : Cell r.outputWidth r.outputHeight :=
  (r.door.1, ⟨r.outputHeight - 2, by
    have := r.height_pos
    have := r.length_ge_seven
    dsimp [outputHeight]
    omega⟩)

/-- The complete actual hole set after the first north push. -/
def firstSealState : HoleState r.outputWidth r.outputHeight where
  player := r.firstSeal
  empty := insert r.firstSeal (r.empty.erase r.upper)
  player_empty := Finset.mem_insert_self _ _

/-- The complete actual hole set after both north pushes seal the source exit. -/
def sealedState : HoleState r.outputWidth r.outputHeight where
  player := r.landing
  empty := insert r.landing (r.firstSealState.empty.erase r.door)
  player_empty := Finset.mem_insert_self _ _

private theorem separator_holes (q : Cell r.outputWidth r.outputHeight)
    (hx : q.1.val = r.width) :
    q ∈ r.empty ↔ q = r.door ∨ q = r.upper ∨ q = r.bottom := by
  constructor
  · intro hq
    rw [empty, Finset.mem_union] at hq
    rcases hq with hs | ha
    · obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hs
      have he := congrArg (fun q => q.1.val) ha
      have := a.1.isLt
      change a.1.val = q.1.val at he
      omega
    · simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with ((he | he) | he)
      · exact he
      · have hroom := (Finset.mem_filter.mp he).2.1
        omega
      · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp he
        have he := congrArg (fun q => q.1.val) hi
        have := i.isLt
        change i.val = q.1.val at he
        omega
  · rintro (rfl | rfl | rfl)
    · exact r.door_mem
    · exact r.upper_mem
    · exact r.bottom_mem

/-- The first complete north push consumes exactly the upper seal hole. -/
private theorem firstSeal_move :
    Move r.compile.board none .north
      (r.initialState.walk r.bottom r.bottom_mem).toState r.firstSealState.toState := by
  have hlen := r.length_ge_seven
  have hh := r.height_pos
  apply HoleState.move_to_first_hole _ _ .north r.upper (r.length - 2)
    (by omega) rfl ?_ ?_ r.upper_mem ?_ rfl r.compile.board r.compile.walls_empty
  · change -(r.height : ℤ) = -((r.height + r.length - 1 : ℕ) : ℤ) + (r.length - 2 : ℕ) + 1
    omega
  · intro q hl hlo hhi hq
    have hx : q.1.val = r.width := hl
    change -((r.height + r.length - 1 : ℕ) : ℤ) < -(q.2.val : ℤ) at hlo
    change -(q.2.val : ℤ) < -(r.height : ℤ) at hhi
    rcases (r.separator_holes q hx).mp hq with he | he | he
    · have hy := congrArg (fun q => q.2.val) he
      change q.2.val = r.height - 1 at hy
      omega
    · have hy := congrArg (fun q => q.2.val) he
      change q.2.val = r.height at hy
      omega
    · have hy := congrArg (fun q => q.2.val) he
      change q.2.val = r.height + r.length - 1 at hy
      omega
  · change r.firstSeal.1 = r.bottom.1 ∧ r.firstSeal.2.val + 1 = r.bottom.2.val
    exact ⟨rfl, by dsimp [firstSeal, bottom, outputHeight]; omega⟩

/-- The second complete north push consumes the door and reaches the committed landing. -/
private theorem secondSeal_move :
    Move r.compile.board none .north r.firstSealState.toState r.sealedState.toState := by
  have hlen := r.length_ge_seven
  have hh := r.height_pos
  have hdoor : r.door ∈ r.firstSealState.empty := by
    simp only [firstSealState, Finset.mem_insert, Finset.mem_erase]
    right
    refine ⟨?_, r.door_mem⟩
    intro he
    have he' := congrArg (fun q => q.2.val) he
    change r.height - 1 = r.height at he'
    omega
  apply HoleState.move_to_first_hole _ _ .north r.door (r.length - 2)
    (by omega) rfl ?_ ?_ hdoor ?_ rfl r.compile.board r.compile.walls_empty
  · change -((r.height - 1 : ℕ) : ℤ) = -((r.height + r.length - 2 : ℕ) : ℤ) + (r.length - 2 : ℕ) + 1
    omega
  · intro q hl hlo hhi hq
    have hx : q.1.val = r.width := hl
    change -((r.height + r.length - 2 : ℕ) : ℤ) < -(q.2.val : ℤ) at hlo
    change -(q.2.val : ℤ) < -((r.height - 1 : ℕ) : ℤ) at hhi
    simp only [firstSealState, Finset.mem_insert, Finset.mem_erase] at hq
    rcases hq with he | ⟨hne, he⟩
    · have hy := congrArg (fun q => q.2.val) he
      change q.2.val = r.height + r.length - 2 at hy
      omega
    · rcases (r.separator_holes q hx).mp he with he | he | he
      · have hy := congrArg (fun q => q.2.val) he
        change q.2.val = r.height - 1 at hy
        omega
      · exact hne he
      · have hy := congrArg (fun q => q.2.val) he
        change q.2.val = r.height + r.length - 1 at hy
        omega
  · change r.landing.1 = r.firstSeal.1 ∧ r.landing.2.val + 1 = r.firstSeal.2.val
    exact ⟨rfl, by dsimp [landing, firstLevel, firstSeal, outputHeight]; omega⟩

private theorem room_walk : Reachable r.compile.board none
    (r.initialState.walk r.roomEntry r.roomEntry_mem).toState
    (r.initialState.walk r.roomBottom r.roomBottom_mem).toState := by
  exact ((r.initialState.walk r.roomEntry r.roomEntry_mem).walk_vertical
    r.roomBottom r.roomBottom_mem rfl (by
      intro q hx hlo _
      apply r.room_mem
      · exact congrArg Fin.val hx
      · have hle : r.height ≤ r.outputHeight - 1 := by
          have := r.length_ge_seven
          dsimp [outputHeight]
          omega
        change min r.height (r.outputHeight - 1) ≤ q.2.val at hlo
        rwa [Nat.min_eq_left hle] at hlo) r.compile.board r.compile.walls_empty none).1

/-- From the source corner, actual walks and two actual pushes commit to the reader. -/
theorem sealedState_reachable (hcorner : r.initial.player = r.sourceCorner) :
    Reachable r.compile.board none r.compile.initial r.sealedState.toState := by
  have hwall := r.compile.walls_empty
  have hdoor := r.initialState.walk_move r.door_mem
    (d := .east) (by
      change r.door.1.val = r.initial.player.1.val + 1 ∧
        r.door.2 = (r.embed r.initial.player).2
      rw [hcorner]
      constructor
      · change r.width = r.width - 1 + 1
        have := r.width_pos
        omega
      · rfl) r.compile.board hwall none
  have hupper := (r.initialState.walk r.door r.door_mem).walk_move r.upper_mem
    (d := .south) (by
      change r.upper.1 = r.door.1 ∧ r.upper.2.val = r.door.2.val + 1
      exact ⟨rfl, by dsimp [upper, door]; have := r.height_pos; omega⟩)
    r.compile.board hwall none
  have hentry := (r.initialState.walk r.upper r.upper_mem).walk_move r.roomEntry_mem
    (d := .east) (by
      change r.roomEntry.1.val = r.upper.1.val + 1 ∧ r.roomEntry.2 = r.upper.2
      exact ⟨rfl, rfl⟩) r.compile.board hwall none
  have hbottom := (r.initialState.walk r.roomBottom r.roomBottom_mem).walk_move r.bottom_mem
    (d := .west) (by
      change r.bottom.1.val + 1 = r.roomBottom.1.val ∧ r.bottom.2 = r.roomBottom.2
      exact ⟨rfl, rfl⟩) r.compile.board hwall none
  exact (((((Relation.ReflTransGen.single ⟨.east, hdoor⟩).tail ⟨.south, hupper⟩).tail
    ⟨.east, hentry⟩).trans (room_walk r)).tail ⟨.west, hbottom⟩).tail
      ⟨.north, r.firstSeal_move⟩ |>.tail ⟨.north, r.secondSeal_move⟩

end PushPuzzle.Push.ColumnScan.Input
