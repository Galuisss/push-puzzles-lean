/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramTrim
public import Push.AcceptanceProgramColumns
public import PushS.PortGatePageWindow
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramColumns
import all PushS.EndpointWalking
import all PushS.PortSegments

/-! The actual public page columns contain their entire canonical outer corridor. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushFS.Reduction PushS PushS.PortLayout SegmentRecipe

private theorem endpoint_corridor_target (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (target : List Bool) (e : Endpoint) (he : e ∈ l.endpoints) (street : EndpointStreet)
    {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val = street.column p e)
    (hy : pageDepth p e.side q < p.Y e.level) : q ∈ targetHoles l p target := by
  obtain ⟨hj, hjm⟩ := l.endpoints_level_bounds p hl hM he
  have hd : pageDepth p e.side q ≤ street.limit p e := by
    have hr := readDepth_eq p hj hjm
    cases street <;> simp only [EndpointStreet.limit] <;> omega
  have hq : q = l.endpointStreetCell p hl ha e he street (pageDepth p e.side q) hd := by
    apply Prod.ext (Fin.ext hx)
    apply Fin.ext
    have hrow := q.2.isLt
    dsimp only [endpointStreetCell]
    cases e.side <;> simp only [pageDepth, reduceCtorEq, ite_true, ite_false]
    omega
  rw [hq]
  exact l.endpointStreet_hole p hl hM ha (l.canonical target) e he street _ hd

private theorem gate_corridor_target (l : PortLayout) (p : Scales.Parameters)
    (target : List Bool) (middle : ℕ) (hi : middle ∈ l.gateCenterCoordinates)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val ∈ [p.x middle - 2, p.x middle + 6, p.x middle + 8, p.x middle + 12])
    (hy0 : 1 ≤ pageDepth p .lower q) (hy : pageDepth p .lower q < p.Y 1) :
    q ∈ targetHoles l p target := by
  have hread := readDepth_eq p le_rfl p.levels_pos
  have hhigh := readDepth_add_lt_H p 1
  apply (mem_holes _ q).mpr
  let s := PortLayout.segment q.1.val (onSide (coordinates p) .lower 1) q.1.val
    (onSide (coordinates p) .lower (readDepth p 1 - 1))
  refine ⟨s, List.mem_append_left _ (l.gateFixedSegments_mem_fixed p hi ?_), ?_⟩
  · apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨q.1.val, hx, rfl⟩
  · have hrow := q.2.isLt
    simp only [s, PortLayout.segment, Segment.Contains, onSide, coordinates,
      pageDepth, reduceCtorEq, ite_false, min_self, max_self] at hy0 hy ⊢
    left
    refine ⟨trivial, trivial, ?_, ?_⟩ <;> omega

/-- Each genuine public column carries every depth from one through its level minus one. -/
theorem pageColumn_corridor_target (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (target : List Bool) (side : Side) {a : PageColumn}
    (hac : a ∈ pageColumns l p side) (hpublic : a.privateColumn = false)
    {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val = a.column)
    (hy0 : 1 ≤ pageDepth p side q) (hy : pageDepth p side q < p.Y a.level) :
    q ∈ targetHoles l p target := by
  unfold pageColumns at hac
  rcases List.mem_append.mp hac with he | hg
  · obtain ⟨e, hefilter, hac⟩ := List.mem_flatMap.mp he
    obtain ⟨hendpoint, hs⟩ := List.mem_filter.mp hefilter
    have hs : e.side = side := by simpa using hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hac
    rcases hac with rfl | rfl
    · exact endpoint_corridor_target l p hl hM ha target e hendpoint .f hx (by simpa only [hs] using hy)
    · exact endpoint_corridor_target l p hl hM ha target e hendpoint .r hx (by simpa only [hs] using hy)
  · split at hg
    next hs =>
      subst side
      obtain ⟨i, hi, hac⟩ := List.mem_flatMap.mp hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hac
      rcases hac with rfl | rfl | rfl | rfl | rfl
      all_goals simp only [Bool.true_eq_false] at hpublic
      all_goals apply gate_corridor_target l p target i hi _ hy0 hy
      all_goals simp [hx]
    next hs => cases hg

end PushPuzzle.Push.AcceptanceProgram
