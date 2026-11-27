/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.LayoutGeometry
public import PushPush.Doors.RoomSlide

/-! Actual player walking through the empty columns between two-column box bands. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Layout

open PushFS (Cell Direction Adjacent State)

/-- All columns used by fixed pins, room boxes, or a correctly routed signal. -/
def columns (L : Layout) : Finset ℕ :=
  (((List.range L.wires.length).flatMap fun i =>
    [30 * i + 7, 30 * i + 8, 30 * i + 14, 30 * i + 15, 30 * i + 24, 30 * i + 25]) ++
    [L.rackX - 1, L.rackX]).toFinset

private theorem columns_west (L : Layout) {x : ℕ} (hx : x ∈ L.columns) : x ≤ L.rackX := by
  simp only [columns, List.mem_toFinset, List.mem_append, List.mem_flatMap,
    List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with ⟨i, hi, hx⟩ | (rfl | rfl)
  · rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> unfold rackX <;> omega
  · exact Nat.sub_le _ _
  · exact le_rfl

@[simp] private theorem rackX_mem_columns (L : Layout) : L.rackX ∈ L.columns := by
  simp [columns]

@[simp] theorem working_mem_columns (L : Layout) : L.rackX - 1 ∈ L.columns := by
  simp [columns]

private theorem pins_columns (L : Layout) {p : ℕ × ℕ} (hp : p ∈ L.pins) : p.1 ∈ L.columns := by
  obtain ⟨⟨e, i⟩, he, hp⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hp)
  have hi := (List.mem_zipIdx' he).1
  apply List.mem_toFinset.mpr
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨i, List.mem_range.mpr hi, ?_⟩
  simp only [wirePins, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
    dsimp [wireA, wireB, wireC] <;> simp

theorem fixed_columns (L : Layout) {p : ℕ × ℕ} (hp : p ∈ L.fixed) : p.1 ∈ L.columns := by
  rcases Finset.mem_union.mp hp with hp | hp
  · rcases Finset.mem_union.mp hp with hp | hp
    · exact L.pins_columns hp
    · rw [L.rack_column hp]
      exact L.rackX_mem_columns
  · rw [L.blockers_column hp]
    exact L.working_mem_columns

private theorem free_private_column (L : Layout) {i offset : ℕ} (hi : i < L.wires.length)
    (ho : offset = 6 ∨ offset = 9 ∨ offset = 13 ∨ offset = 16 ∨ offset = 23 ∨ offset = 26) :
    30 * i + offset ∉ L.columns := by
  intro hx
  simp only [columns, List.mem_toFinset, List.mem_append, List.mem_flatMap,
    List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with ⟨j, hj, hx⟩ | hx
  · rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hx with hx | hx | hx | hx | hx | hx <;> omega
  · unfold rackX at hx
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hx with hx | hx <;> omega

private theorem free_rack_column (L : Layout) {x : ℕ}
    (hx : x = L.rackX - 2 ∨ x = L.rackX + 1) : x ∉ L.columns := by
  intro hmem
  simp only [columns, List.mem_toFinset, List.mem_append, List.mem_flatMap,
    List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with ⟨i, hi, hmem⟩ | hmem
  · unfold rackX at hx
    rcases hx with hx | hx <;>
      rcases hmem with hmem | hmem | hmem | hmem | hmem | hmem <;> omega
  · unfold rackX at hx hmem
    rcases hx with hx | hx <;> rcases hmem with hmem | hmem <;> omega

/-- Every used column is adjacent to a globally empty column. -/
private theorem column_escape (L : Layout) (x : Fin L.width) (hx : x.val ∈ L.columns) :
    ∃ z : Fin L.width, z.val ∉ L.columns ∧ (x.val + 1 = z.val ∨ z.val + 1 = x.val) := by
  simp only [columns, List.mem_toFinset, List.mem_append, List.mem_flatMap,
    List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with ⟨i, hi, hx⟩ | (hx | hx)
  · rcases hx with hx | hx | hx | hx | hx | hx
    · exact ⟨⟨30 * i + 6, by unfold width rackX; omega⟩,
        free_private_column L hi (by omega), Or.inr (by dsimp; omega)⟩
    · exact ⟨⟨30 * i + 9, by unfold width rackX; omega⟩,
        free_private_column L hi (by omega), Or.inl (by dsimp; omega)⟩
    · exact ⟨⟨30 * i + 13, by unfold width rackX; omega⟩,
        free_private_column L hi (by omega), Or.inr (by dsimp; omega)⟩
    · exact ⟨⟨30 * i + 16, by unfold width rackX; omega⟩,
        free_private_column L hi (by omega), Or.inl (by dsimp; omega)⟩
    · exact ⟨⟨30 * i + 23, by unfold width rackX; omega⟩,
        free_private_column L hi (by omega), Or.inr (by dsimp; omega)⟩
    · exact ⟨⟨30 * i + 26, by unfold width rackX; omega⟩,
        free_private_column L hi (by omega), Or.inl (by dsimp; omega)⟩
  · refine ⟨⟨L.rackX - 2, by unfold width rackX; omega⟩, free_rack_column L (Or.inl rfl),
      Or.inr ?_⟩
    dsimp
    unfold rackX at hx ⊢
    omega
  · exact ⟨⟨L.rackX + 1, by unfold width; omega⟩, free_rack_column L (Or.inr rfl),
      Or.inl (by dsimp; omega)⟩

private theorem walk_column {w h : ℕ} (boxes : Finset (Cell w h)) (x : Fin w)
    (a b : Fin h) (hempty : ∀ y, (x, y) ∉ boxes) :
    Finite.Reachable 1 ⟨(x, a), boxes⟩ ⟨(x, b), boxes⟩ := by
  by_cases hab : a.val ≤ b.val
  · apply Doors.straight_walk_single boxes .south (x, a) (x, b) rfl
    · simpa only [Direction.position] using (Int.ofNat_le.mpr hab)
    · intro p hl _ _
      have hx : p.1 = x := Fin.ext hl
      simpa only [← hx] using hempty p.2
  · apply Doors.straight_walk_single boxes .north (x, a) (x, b) rfl
    · simp only [Direction.position]
      omega
    · intro p hl _ _
      have hx : p.1 = x := Fin.ext hl
      simpa only [← hx] using hempty p.2

private theorem walk_row {w h : ℕ} (boxes : Finset (Cell w h)) (a b : Fin w)
    (y : Fin h) (hempty : ∀ x, (x, y) ∉ boxes) :
    Finite.Reachable 1 ⟨(a, y), boxes⟩ ⟨(b, y), boxes⟩ := by
  by_cases hab : a.val ≤ b.val
  · apply Doors.straight_walk_single boxes .east (a, y) (b, y) rfl
    · simpa only [Direction.position] using (Int.ofNat_le.mpr hab)
    · intro p hl _ _
      have hy : p.2 = y := Fin.ext hl
      simpa only [← hy] using hempty p.1
  · apply Doors.straight_walk_single boxes .west (a, y) (b, y) rfl
    · simp only [Direction.position]
      omega
    · intro p hl _ _
      have hy : p.2 = y := Fin.ext hl
      simpa only [← hy] using hempty p.1

/-- Every empty support cell connects to the actual player corner in both directions. -/
theorem walk_corner (L : Layout) (boxes : Finset (Cell L.width L.height))
    (hcolumns : ∀ p ∈ boxes, p.1.val ∈ L.columns)
    (htop : ∀ p : Cell L.width L.height, p.2.val = 0 → p ∉ boxes)
    (p : Cell L.width L.height) (hp : p ∉ boxes) :
    Finite.Reachable 1 ⟨p, boxes⟩ ⟨L.corner, boxes⟩ ∧
      Finite.Reachable 1 ⟨L.corner, boxes⟩ ⟨p, boxes⟩ := by
  have hfree (x : Fin L.width) (hx : x.val ∉ L.columns) (y : Fin L.height) :
      (x, y) ∉ boxes := fun h => hx (hcolumns _ h)
  obtain ⟨x, hx, hpx, hxp⟩ : ∃ x : Fin L.width, x.val ∉ L.columns ∧
      Finite.Reachable 1 (⟨p, boxes⟩ : State L.width L.height) ⟨(x, p.2), boxes⟩ ∧
      Finite.Reachable 1 (⟨(x, p.2), boxes⟩ : State L.width L.height) ⟨p, boxes⟩ := by
    by_cases hx : p.1.val ∈ L.columns
    · obtain ⟨x, hxfree, he | he⟩ := L.column_escape p.1 hx
      · have ha : Adjacent .east p (x, p.2) := ⟨he.symm, rfl⟩
        exact ⟨x, hxfree, .single ⟨.east, .walk hp ha (hfree x hxfree _) rfl⟩,
          .single ⟨.west, .walk (hfree x hxfree _) ha.reverse hp rfl⟩⟩
      · have ha : Adjacent .west p (x, p.2) := ⟨he, rfl⟩
        exact ⟨x, hxfree, .single ⟨.west, .walk hp ha (hfree x hxfree _) rfl⟩,
          .single ⟨.east, .walk (hfree x hxfree _) ha.reverse hp rfl⟩⟩
    · exact ⟨p.1, hx, .refl, .refl⟩
  let top : Fin L.height := ⟨0, L.height_pos⟩
  have hcorner : L.corner.1.val ∉ L.columns := by
    intro h
    have hw := L.columns_west h
    change L.width - 1 ≤ L.rackX at hw
    unfold width at hw
    omega
  have col_up := walk_column boxes x p.2 top (hfree x hx)
  have col_down := walk_column boxes x top p.2 (hfree x hx)
  have top_out := walk_row boxes x L.corner.1 top (fun x => htop (x, top) rfl)
  have top_back := walk_row boxes L.corner.1 x top (fun x => htop (x, top) rfl)
  have corner_down := walk_column boxes L.corner.1 top L.corner.2 (hfree L.corner.1 hcorner)
  have corner_up := walk_column boxes L.corner.1 L.corner.2 top (hfree L.corner.1 hcorner)
  exact ⟨hpx.trans (col_up.trans (top_out.trans corner_down)),
    corner_up.trans (top_back.trans (col_down.trans hxp))⟩

end PushPuzzle.PushPush.Doors.Layout
