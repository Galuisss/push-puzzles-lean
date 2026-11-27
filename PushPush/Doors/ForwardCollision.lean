/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.ForwardRooms

/-! Physical collisions of two separated door-slot boxes, including terminal erasure. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell State Direction Adjacent)

/-- Slide a stored box towards the incoming slot. -/
def collisionDirection (moving stationary : Register) : Direction :=
  if moving.row < stationary.row then .south else .north

/-- The moving box stops one row before the stationary incoming box. -/
def collisionRow (moving stationary : Register) : ℕ :=
  if moving.row < stationary.row then stationary.row - 1 else stationary.row + 1

/-- The player's initial support lies one row behind the moving stored box. -/
def collisionSupport (moving stationary : Register) : ℕ :=
  if moving.row < stationary.row then moving.row - 1 else moving.row + 1

private theorem register_separation (left right : Register) (hne : left ≠ right) :
    left.row + 1 < right.row ∨ right.row + 1 < left.row := by
  cases left <;> cases right <;> simp_all [Register.row]

theorem collisionRow_bounds (left right : Register) : 9 ≤ collisionRow left right ∧ collisionRow left right ≤ 81 := by
  have ha := Register.row_bounds left
  have hb := Register.row_bounds right
  unfold collisionRow
  split <;> omega

private theorem collisionSupport_bounds (left right : Register) :
    9 ≤ collisionSupport left right ∧ collisionSupport left right ≤ 81 := by
  have ha := Register.row_bounds left
  unfold collisionSupport
  split <;> omega

/-- The actual maximum slide, surrounded by explicit approach and return walks.
The incoming box becomes the retained register; the old register becomes the outgoing signal. -/
theorem door_collision (storage : Bool) (I : Instance) (i : Fin I.doors.length)
    (moving stationary : Register) (hne : moving ≠ stationary)
    (frame : Finset (Cell (layout storage I).width (layout storage I).height))
    (hcolumns : ∀ p ∈ frame, p.1.val ∈ (layout storage I).columns)
    (htop : ∀ p : Cell (layout storage I).width (layout storage I).height,
      p.2.val = 0 → p ∉ frame)
    (hframe : ∀ p : Cell (layout storage I).width (layout storage I).height,
      p.1.val = (layout storage I).rackX - 1 →
      doorBase i.val + (layout storage I).shift < p.2.val →
      p.2.val < doorBase i.val + (layout storage I).shift + 90 → p ∉ frame) :
    Finite.Reachable 1
      (⟨(layout storage I).corner,
        insert (doorCell storage I i moving.row (by have := Register.row_bounds moving; omega))
          (insert (doorCell storage I i stationary.row (by have := Register.row_bounds stationary; omega)) frame)⟩ :
        PushFS.State (layout storage I).width (layout storage I).height)
      ⟨(layout storage I).corner,
        insert (doorCell storage I i (collisionRow moving stationary)
          (by have := collisionRow_bounds moving stationary; omega))
          (insert (doorCell storage I i stationary.row (by have := Register.row_bounds stationary; omega)) frame)⟩ := by
  have hm := Register.row_bounds moving
  have hs := Register.row_bounds stationary
  have hd := collisionRow_bounds moving stationary
  have hu := collisionSupport_bounds moving stationary
  have hsep := register_separation moving stationary hne
  let source := doorCell storage I i moving.row (by omega)
  let stop := doorCell storage I i stationary.row (by omega)
  let dest := doorCell storage I i (collisionRow moving stationary) (by omega)
  let support := doorCell storage I i (collisionSupport moving stationary) (by omega)
  let d := collisionDirection moving stationary
  have hsource : source ∉ frame := hframe source rfl (by dsimp [source]; omega)
    (by dsimp [source]; omega)
  have hstop_y : 0 < stop.2.val := by
    dsimp [stop]
    omega
  have hsource_y : 0 < source.2.val := by
    dsimp [source]
    omega
  have hdest_y : 0 < dest.2.val := by
    dsimp [dest]
    omega
  have hsource_ne_stop : source ≠ stop := by
    intro he
    have he := congrArg (fun p => p.2.val) he
    dsimp [source, stop] at he
    omega
  have hsupport : support ∉ insert source (insert stop frame) := by
    have hf : support ∉ frame := hframe support rfl (by dsimp [support]; omega)
      (by dsimp [support]; omega)
    simp only [Finset.mem_insert, not_or]
    refine ⟨?_, ?_, hf⟩
    · intro he
      have he := congrArg (fun p => p.2.val) he
      dsimp [support, source] at he
      unfold collisionSupport at he
      split at he <;> omega
    · intro he
      have he := congrArg (fun p => p.2.val) he
      dsimp [support, stop] at he
      unfold collisionSupport at he
      split at he <;> omega
  apply (layout storage I).slide_from_corner (insert stop frame) d source dest stop support
  · intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact (layout storage I).working_mem_columns
    · exact hcolumns p hp
  · intro p hp hmem
    rcases Finset.mem_insert.mp hmem with rfl | hmem
    · omega
    · exact htop p hp hmem
  · exact (layout storage I).working_mem_columns
  · exact (layout storage I).working_mem_columns
  · exact hsource_y
  · exact hdest_y
  · simp only [Finset.mem_insert, not_or]
    exact ⟨hsource_ne_stop, hsource⟩
  · exact hsupport
  · by_cases hlt : moving.row < stationary.row <;>
      simp [d, collisionDirection, hlt, Adjacent, source, support,
        collisionSupport, doorCell, workCell, Layout.point] <;> omega
  · by_cases hlt : moving.row < stationary.row <;>
      simp [d, collisionDirection, hlt, Direction.lane, source, dest, doorCell, workCell, Layout.point]
  · by_cases hlt : moving.row < stationary.row <;>
      simp only [d, collisionDirection, hlt, ite_true, ite_false, Direction.position]
      <;> dsimp [source, dest] <;> simp only [collisionRow, hlt, ite_true, ite_false] <;> omega
  · intro p hl hlo hhi hmem
    have hpx : p.1.val = (layout storage I).rackX - 1 := by
      by_cases hlt : moving.row < stationary.row <;>
        simpa [d, collisionDirection, hlt, Direction.lane, source] using hl
    rcases Finset.mem_insert.mp hmem with he | hp
    · subst p
      by_cases hlt : moving.row < stationary.row <;>
        simp only [d, collisionDirection, hlt, ite_true, ite_false, Direction.position] at hhi
        <;> dsimp [stop, dest] at hhi
        <;> simp only [collisionRow, hlt, ite_true, ite_false] at hhi <;> omega
    · apply hframe p hpx ?_ ?_ hp
      all_goals
        by_cases hlt : moving.row < stationary.row <;>
          simp only [d, collisionDirection, hlt, ite_true, ite_false, Direction.position] at hlo hhi
          <;> dsimp [source, dest] at hlo hhi
          <;> simp only [collisionRow, hlt, ite_true, ite_false] at hlo hhi <;> omega
  · by_cases hlt : moving.row < stationary.row <;>
      simp [d, collisionDirection, hlt, Adjacent, stop, dest, collisionRow,
        doorCell, workCell, Layout.point] <;> omega
  · exact Finset.mem_insert_self _ _

end PushPuzzle.PushPush.Doors.Source
