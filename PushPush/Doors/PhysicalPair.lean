/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.PhysicalColumns

/-! A successful prefix cannot move the adjacent working-column collision pair vertically. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell Direction Adjacent)

theorem Protected.pair_door_no_vertical {storage : Bool} {I : Instance}
    {s t : PushFS.State (layout storage I).width (layout storage I).height}
    (ht : Protected storage I t) (door : Fin I.doors.length) (a : ℕ)
    (hlo : doorBase door.val + (layout storage I).shift + 3 ≤ a)
    (hhi : a + 3 ≤ doorBase door.val + (layout storage I).shift + 90)
    (hc : Room.PairColumn s (doorCell storage I door 0 (by omega)).1
      (doorBase door.val + (layout storage I).shift) a)
    {d : Direction} {n k : ℕ} (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hv : s.player ∉ s.boxes) (hb : t.boxes = r.boxes)
    (hfirstx : (r.cell ⟨1, by omega⟩).1 = (doorCell storage I door 0 (by omega)).1)
    (hfirsty : (r.cell ⟨1, by omega⟩).2.val = a ∨ (r.cell ⟨1, by omega⟩).2.val = a + 1)
    (hd : d = .north ∨ d = .south) : False := by
  have hroom : doorBase door.val + (layout storage I).shift + 90 < (layout storage I).height := by
    have hbnd := (layout storage I).translated_bounds
      (dividers_fit storage I (door_south_divider_mem storage I door.isLt))
    omega
  have hhead : (d = .north ∧ (r.cell ⟨1, by omega⟩).2.val = a + 1) ∨
      (d = .south ∧ (r.cell ⟨1, by omega⟩).2.val = a) := by
    rcases hd with rfl | rfl
    · by_cases hy : (r.cell ⟨1, by omega⟩).2.val = a + 1
      · exact Or.inl ⟨rfl, hy⟩
      · have hy0 := hfirsty.resolve_right hy
        let support : Cell (layout storage I).width (layout storage I).height :=
          ((doorCell storage I door 0 (by omega)).1, ⟨a + 1, by omega⟩)
        have hsupport : Adjacent Direction.north.opposite (r.cell ⟨1, by omega⟩) support := by
          exact ⟨hfirstx.symm, by change a + 1 = (r.cell ⟨1, by omega⟩).2.val + 1; omega⟩
        have hbox : support ∈ s.boxes :=
          (hc support rfl (by dsimp [support]; omega) (by dsimp [support]; omega)).mpr
            (Or.inr (Or.inr (Or.inr rfl)))
        exact False.elim (hv (blocked_support r (by omega) support hsupport hbox))
    · by_cases hy : (r.cell ⟨1, by omega⟩).2.val = a
      · exact Or.inr ⟨rfl, hy⟩
      · have hy1 := hfirsty.resolve_left hy
        let support : Cell (layout storage I).width (layout storage I).height :=
          ((doorCell storage I door 0 (by omega)).1, ⟨a, by omega⟩)
        have hsupport : Adjacent Direction.south.opposite (r.cell ⟨1, by omega⟩) support := by
          exact ⟨hfirstx.symm, by change a + 1 = (r.cell ⟨1, by omega⟩).2.val; omega⟩
        have hbox : support ∈ s.boxes :=
          (hc support rfl (by dsimp [support]; omega) (by dsimp [support]; omega)).mpr
            (Or.inr (Or.inr (Or.inl rfl)))
        exact False.elim (hv (blocked_support r (by omega) support hsupport hbox))
  have hpair := Room.pair_collision r hn hk _ _ a hroom hlo hhi hc hfirstx hhead
  have hlastx : (r.cell ⟨n + k, by omega⟩).1.val = (layout storage I).rackX - 1 := by
    have hfl := r.lane ⟨1, by omega⟩
    have hll := r.lane ⟨n + k, by omega⟩
    have hfx : (r.cell ⟨1, by omega⟩).1.val = (layout storage I).rackX - 1 :=
      congrArg Fin.val hfirstx
    rcases hd with rfl | rfl <;> simp only [Direction.lane] at hfl hll <;> omega
  exact ht.door_neighbors_empty door _ hlastx hpair.2 (hb ▸ r.last_mem_boxes hn)

end PushPuzzle.PushPush.Doors.Source
