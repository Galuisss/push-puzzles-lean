/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.ProtectedRows
public import PushPush.Doors.CompilerBounds
public import PushPush.Cap

/-! Concrete source layouts satisfy the rack, divider and cap invariants on every successful prefix. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell Direction Adjacent)

variable (storage : Bool) (I : Instance)

theorem initial_supported :
    Supported .east (layout storage I).rackX (puzzle storage I).initial := by
  intro p hp
  change (p.1.val : ℤ) ≤ ((layout storage I).rackX : ℤ)
  exact_mod_cast (layout storage I).initialRaw_west
    (((layout storage I).mem_raster _ _).mp hp)

private theorem layout_rack_eq (L : Layout) :
    line .south L.rackX (L.raster L.goalsRaw) =
      line .south L.rackX (L.raster L.initialRaw) := by
  unfold line
  congr 1
  ext p
  simp only [Finset.mem_filter]
  by_cases hx : p.1.val = L.rackX
  · simp only [show Direction.south.lane p = L.rackX from hx, and_true, L.mem_raster]
    rw [hx, L.goalsRaw_rack_iff, L.initialRaw_rack_iff]
  · simp only [show ¬ Direction.south.lane p = L.rackX from hx, and_false]

private theorem goals_rack {t : PushFS.State (layout storage I).width (layout storage I).height}
    (ht : t.boxes = (puzzle storage I).board.goals) :
    line .south (layout storage I).rackX t.boxes =
      line .south (layout storage I).rackX (puzzle storage I).initial.boxes := by
  have he : t.boxes = ((layout storage I).raster (layout storage I).goalsRaw :
      Finset (Cell (layout storage I).width (layout storage I).height)) := ht
  rw [he]
  exact layout_rack_eq (layout storage I)

theorem divider_guard {g : ℕ} (hg : g ∈ (layout storage I).dividers)
    (p : Cell (layout storage I).width (layout storage I).height)
    (hx : p.1.val = (layout storage I).rackX - 1)
    (hy : p.2.val = g + (layout storage I).shift) :
    DividerGuard (layout storage I).rackX (puzzle storage I).initial p := by
  have hr := (layout storage I).rackX_ge
  have hwidth : (layout storage I).rackX < (layout storage I).width := by
    unfold Layout.width
    omega
  constructor
  · let e : Cell (layout storage I).width (layout storage I).height :=
      (⟨(layout storage I).rackX, hwidth⟩, p.2)
    refine ⟨e, ?_, rfl, ?_⟩
    · change (layout storage I).rackX = p.1.val + 1 ∧ p.2 = p.2
      exact ⟨by omega, rfl⟩
    · intro he
      have he := ((layout storage I).mem_raster _ _).mp he
      change ((layout storage I).rackX, p.2.val) ∈ (layout storage I).initialRaw at he
      rw [hy, (layout storage I).initialRaw_rack_iff] at he
      exact divider_rack_empty storage I hg he
  · intro q hq
    let e : Cell (layout storage I).width (layout storage I).height :=
      (⟨(layout storage I).rackX, hwidth⟩, q.2)
    have hqx : q.1.val = p.1.val := by
      rcases hq with hq | hq <;> exact congrArg Fin.val hq.1
    refine ⟨e, ?_, rfl, ?_⟩
    · change (layout storage I).rackX = q.1.val + 1 ∧ q.2 = q.2
      exact ⟨by omega, rfl⟩
    · apply ((layout storage I).mem_raster _ _).mpr
      change ((layout storage I).rackX, q.2.val) ∈ (layout storage I).initialRaw
      rw [(layout storage I).initialRaw_rack_iff]
      have hneighbor := divider_rack_neighbors storage I hg
      rcases hq with hq | hq
      · have hqy : q.2.val = g + (layout storage I).shift - 1 := by
          have ha := hq.2
          omega
        rw [hqy]
        exact hneighbor.1
      · have hqy : q.2.val = g + (layout storage I).shift + 1 := by
          have ha := hq.2
          omega
        rw [hqy]
        exact hneighbor.2

private theorem goals_divider_isolated
    {t : PushFS.State (layout storage I).width (layout storage I).height}
    (ht : t.boxes = (puzzle storage I).board.goals) {g : ℕ}
    (hg : g ∈ (layout storage I).dividers)
    (p : Cell (layout storage I).width (layout storage I).height)
    (hx : p.1.val = (layout storage I).rackX - 1)
    (hy : p.2.val = g + (layout storage I).shift) : VerticallyIsolated t p := by
  constructor
  · rw [ht]
    apply ((layout storage I).mem_raster _ _).mpr
    rw [hx, hy]
    exact divider_goal_mem storage I hg
  · intro q hq hqb
    rw [ht] at hqb
    have hqb := ((layout storage I).mem_raster _ _).mp hqb
    have hneighbor := divider_goal_neighbors storage I hg
    rcases hq with hq | hq
    · have hqx : q.1.val = (layout storage I).rackX - 1 :=
        (congrArg Fin.val hq.1).trans hx
      have hqy : q.2.val = g + (layout storage I).shift - 1 := by have ha := hq.2; omega
      rw [hqx, hqy] at hqb
      exact hneighbor.1 hqb
    · have hqx : q.1.val = (layout storage I).rackX - 1 :=
        (congrArg Fin.val hq.1).trans hx
      have hqy : q.2.val = g + (layout storage I).shift + 1 := by have ha := hq.2; omega
      rw [hqx, hqy] at hqb
      exact hneighbor.2 hqb

theorem cap_guard {y : ℕ} (hy : y ∈ (layout storage I).caps)
    (q : Cell (layout storage I).width (layout storage I).height)
    (hqx : q.1.val = (layout storage I).rackX - 1)
    (hqy : q.2.val = y + (layout storage I).shift) :
    ∃ g ∈ (layout storage I).dividers,
      ∃ p : Cell (layout storage I).width (layout storage I).height,
        p.1.val = (layout storage I).rackX - 1 ∧
        p.2.val = g + (layout storage I).shift ∧
        CapGuard (layout storage I).rackX (puzzle storage I).initial p q := by
  obtain ⟨g, hg, hgap⟩ := cap_divider_gap_two storage I hy
  have hr := (layout storage I).rackX_ge
  have hb := (layout storage I).translated_bounds (dividers_fit storage I hg)
  have hc := (layout storage I).translated_bounds (caps_fit storage I hy)
  have hwidth : (layout storage I).rackX < (layout storage I).width := by
    unfold Layout.width
    omega
  let p : Cell (layout storage I).width (layout storage I).height :=
    (q.1, ⟨g + (layout storage I).shift, by omega⟩)
  refine ⟨g, hg, p, hqx, rfl, divider_guard storage I hg p hqx rfl, ?_, ?_⟩
  · rcases hgap with hgap | hgap
    · let middle : Cell (layout storage I).width (layout storage I).height :=
        (q.1, ⟨g + (layout storage I).shift + 1, by omega⟩)
      refine ⟨.south, middle, Or.inr rfl, ⟨rfl, rfl⟩, rfl, ?_⟩
      change q.2.val = g + (layout storage I).shift + 1 + 1
      omega
    · let middle : Cell (layout storage I).width (layout storage I).height :=
        (q.1, ⟨g + (layout storage I).shift - 1, by omega⟩)
      refine ⟨.north, middle, Or.inl rfl, ⟨rfl, ?_⟩, rfl, ?_⟩
      · change g + (layout storage I).shift - 1 + 1 = g + (layout storage I).shift
        omega
      · change q.2.val + 1 = g + (layout storage I).shift - 1
        omega
  · let e : Cell (layout storage I).width (layout storage I).height :=
      (⟨(layout storage I).rackX, hwidth⟩, q.2)
    refine ⟨e, ?_, rfl, ?_⟩
    · change (layout storage I).rackX = q.1.val + 1 ∧ q.2 = q.2
      exact ⟨by omega, rfl⟩
    · intro he
      have he := ((layout storage I).mem_raster _ _).mp he
      change ((layout storage I).rackX, q.2.val) ∈ (layout storage I).initialRaw at he
      rw [hqy, (layout storage I).initialRaw_rack_iff] at he
      exact cap_rack_empty storage I hy he

/-- The physical frame properties used by the successful-prefix decoder. -/
structure Protected (s : PushFS.State (layout storage I).width (layout storage I).height) : Prop where
  /-- No successful prefix touches the true boundary. -/
  interior : Interior s
  /-- All boxes remain west of the original rack. -/
  supported : Supported .east (layout storage I).rackX s
  /-- The complete rack occupancy is unchanged. -/
  rack : line .south (layout storage I).rackX s.boxes =
    line .south (layout storage I).rackX (puzzle storage I).initial.boxes
  /-- Every divider remains an isolated box with its two forbidden cells empty. -/
  dividers : ∀ g ∈ (layout storage I).dividers,
    ∀ p : Cell (layout storage I).width (layout storage I).height,
      p.1.val = (layout storage I).rackX - 1 → p.2.val = g + (layout storage I).shift →
        VerticallyIsolated s p
  /-- Every endpoint cap remains on its original cell. -/
  caps : ∀ y ∈ (layout storage I).caps,
    ∀ p : Cell (layout storage I).width (layout storage I).height,
      p.1.val = (layout storage I).rackX - 1 → p.2.val = y + (layout storage I).shift →
        p ∈ s.boxes

/-- The actual exact-storage target certifies the entire physical prefix frame. -/
theorem protected_prefix
    {s t : PushFS.State (layout storage I).width (layout storage I).height}
    (hprefix : Reachable (puzzle storage I).initial s) (hsuffix : Reachable s t)
    (ht : t.boxes = (puzzle storage I).board.goals) : Protected storage I s where
  interior := hsuffix.interior_source (goals_interior storage I ht)
  supported := hprefix.supported (hsuffix.interior_source (goals_interior storage I ht))
    (initial_supported storage I)
  rack := hprefix.rack_frozen hsuffix (initial_supported storage I)
    (goals_interior storage I ht) (goals_rack storage I ht)
  dividers := by
    intro g hg p hx hy
    exact hprefix.divider_frozen hsuffix (initial_supported storage I) (goals_interior storage I ht)
      (goals_rack storage I ht) (divider_guard storage I hg p hx hy)
      (goals_divider_isolated storage I ht hg p hx hy)
  caps := by
    intro y hy q hqx hqy
    obtain ⟨g, hg, p, hpx, hpy, hguard⟩ := cap_guard storage I hy q hqx hqy
    apply hprefix.cap_frozen hsuffix (initial_supported storage I) (goals_interior storage I ht)
      (goals_rack storage I ht) hguard (goals_divider_isolated storage I ht hg p hpx hpy)
    rw [ht]
    apply ((layout storage I).mem_raster _ _).mpr
    rw [hqx, hqy]
    exact cap_goal_mem storage I hy

end PushPuzzle.PushPush.Doors.Source
