/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupportCoordinates

/-! Extra intersections of the two sparse supports are isolated and preserve their initial boxes. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS

/-- A support point has no adjacent point in the same support. -/
@[expose] def Isolated {w h : ℕ} (C : Set (Cell w h)) (q : Cell w h) : Prop :=
  ∀ d r, Adjacent d q r → r ∉ C

/-- Away from the original streets, the two separated sparse supports intersect only in isolated points. -/
theorem SupportCoordinates.crossing_isolated {w h : ℕ} (c : SupportCoordinates w h)
    (hrows : Support.Separated (c.rows ∪ c.cuts))
    (hcolumns : Support.Separated (c.columns ∪ c.guards ∪ c.samples))
    {q : Cell w h} (hq : q ∈ c.first ∩ c.second) (horiginal : q ∉ c.original) :
    Isolated (c.first ∩ c.second) q := by
  have hnot : q.1 ∉ c.columns ∧ q.2 ∉ c.rows := not_or.mp horiginal
  have hx : q.1 ∈ c.columns ∪ c.guards ∪ c.samples := hq.2.resolve_right hnot.2
  have hy : q.2 ∈ c.rows ∪ c.cuts := hq.1.resolve_left hnot.1
  intro d r ha hr
  cases d with
  | north =>
    obtain ⟨hxq, hyr⟩ := ha
    have hrx : r.1 ∉ c.columns := hxq ▸ hnot.1
    have hry : r.2 ∈ c.rows ∪ c.cuts := hr.1.resolve_left hrx
    exact hrows hry hy hyr
  | south =>
    obtain ⟨hxq, hyr⟩ := ha
    have hrx : r.1 ∉ c.columns := hxq ▸ hnot.1
    have hry : r.2 ∈ c.rows ∪ c.cuts := hr.1.resolve_left hrx
    exact hrows hy hry hyr.symm
  | east =>
    obtain ⟨hxr, hyq⟩ := ha
    have hry : r.2 ∉ c.rows := hyq ▸ hnot.2
    have hrx : r.1 ∈ c.columns ∪ c.guards ∪ c.samples := hr.2.resolve_right hry
    exact hcolumns hx hrx hxr.symm
  | west =>
    obtain ⟨hxr, hyq⟩ := ha
    have hry : r.2 ∉ c.rows := hyq ▸ hnot.2
    have hrx : r.1 ∈ c.columns ∪ c.guards ∪ c.samples := hr.2.resolve_right hry
    exact hcolumns hrx hx hxr

/-- Intersections retain the complete-lane reverse-support rule. -/
theorem axisClosed_inter {w h : ℕ} {A C : Set (Cell w h)}
    (hA : Support.AxisClosed A) (hC : Support.AxisClosed C) : Support.AxisClosed (A ∩ C) := by
  intro d p q ha hp hq r hr
  exact ⟨hA ha hp.1 hq.1 r hr, hC ha hp.2 hq.2 r hr⟩

/-- A physical move cannot change a box at an isolated point of its terminal complete-lane support. -/
private theorem isolated_box_move {w h : ℕ} {C : Set (Cell w h)} (hC : Support.AxisClosed C)
    {q : Cell w h} (hi : Isolated C q) {B : Board w h} {cap : Option ℕ}
    {d : Direction} {s t : State w h} (hm : Move B cap d s t) (ht : Support.Supported C t) :
    q ∈ t.boxes ↔ q ∈ s.boxes := by
  cases hm with
  | walk _ _ _ _ hb => rw [hb]
  | @push n hs hn _ r _ hb =>
    have hRun := hC.push_run hs r hn hb ht
    have hfirst : q ≠ r.cell 1 := by
      intro he
      subst q
      have hadj : Adjacent d (r.cell 0) (r.cell 1) := r.adjacent 0
      exact hi _ _ hadj.reverse (hRun 0)
    have hlast : q ≠ r.cell ⟨n + 1, by omega⟩ := by
      intro he
      subst q
      have hadj : Adjacent d (r.cell ⟨n, by omega⟩) (r.cell ⟨n + 1, by omega⟩) := r.adjacent ⟨n, by omega⟩
      exact hi _ _ hadj.reverse (hRun ⟨n, by omega⟩)
    rw [hb]
    simp only [Finset.mem_insert, Finset.mem_erase]
    tauto

/-- Every real step preserves boxes at isolated support intersections. -/
private theorem isolated_box_step {w h : ℕ} {C : Set (Cell w h)} (hC : Support.AxisClosed C)
    {q : Cell w h} (hi : Isolated C q) {B : Board w h} {cap : Option ℕ}
    {s t : State w h} (hm : Step B cap s t) (ht : Support.Supported C t) :
    q ∈ t.boxes ↔ q ∈ s.boxes := by
  obtain ⟨d, hm⟩ := hm
  exact isolated_box_move hC hi hm ht

/-- Terminal support preserves each isolated point's initial occupancy along the whole actual play. -/
theorem isolated_box_reachable {w h : ℕ} {C : Set (Cell w h)} (hC : Support.AxisClosed C)
    {q : Cell w h} (hi : Isolated C q) {B : Board w h} {cap : Option ℕ}
    {s t : State w h} (hr : Reachable B cap s t) (ht : Support.Supported C t) :
    q ∈ t.boxes ↔ q ∈ s.boxes := by
  revert ht
  induction hr with
  | refl => exact fun _ => Iff.rfl
  | tail _ hm ih =>
    intro ht
    exact (isolated_box_step hC hi hm ht).trans (ih (hC.step_source hm ht))

end PushPuzzle.Push.AcceptanceSoundness
