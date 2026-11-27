/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.QuotasRegions

/-! Every literal quota cut lies at a shared fixed box or beyond its complete grid line. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Layout

open PushFS (Cell Direction Adjacent)
open Push.AcceptanceProgram

/-- Static inventory and the parked accepting signal, shared by every stable door assignment. -/
def readerShared (L : Layout) : Finset (ℕ × ℕ) :=
  L.fixed ∪ { (L.rackX - 1, L.stop + L.shift) }

theorem rackProbe_mem (L : Layout) {row : ℕ} (hrow : row ∈ L.rackProbeRows) :
    (L.rackX, row) ∈ L.fixed := by
  obtain ⟨p, hp, he⟩ := List.mem_map.mp hrow
  have hmem : p ∈ L.rack := List.mem_toFinset.mpr hp
  have hx := L.rack_column hmem
  have hp : p = (L.rackX, row) := Prod.ext hx he
  rw [← hp]
  exact Finset.mem_union_left _ (Finset.mem_union_right _ hmem)

theorem marker_mem (L : Layout) {row : ℕ} (hrow : row ∈ L.markerRows) :
    (L.rackX - 1, row) ∈ L.readerShared := by
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hrow
  rcases List.mem_append.mp hy with hy | hy
  · apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨y, hy, rfl⟩)
  · have he := List.mem_singleton.mp hy
    subst y
    exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

theorem dividerNeighbor_mem (L : Layout) {row : ℕ} (hrow : row ∈ L.dividerNeighbors) :
    (L.rackX, row) ∈ L.fixed := by
  obtain ⟨g, hg, hr⟩ := List.mem_flatMap.mp hrow
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  apply List.mem_toFinset.mpr
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨g, hg, ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
  rcases hr with rfl | rfl <;> simp

private theorem probe_boundary_shared (L : Layout) {request : ℕ × ℕ}
    (hr : request ∈ L.probeRequests) (p : Cell L.width L.height)
    (hl : Direction.east.lane p = request.1) (hp : prefixRank .east p = request.2) :
    (p.1.val, p.2.val) ∈ L.readerShared := by
  rcases request with ⟨row, span⟩
  simp only [probeRequests, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨y, hy, he⟩ | ⟨y, hy, he⟩
  · have hrow := congrArg Prod.fst he
    have hspan := congrArg Prod.snd he
    dsimp at hrow hspan
    have hx : p.1.val = L.rackX := by
      simp only [prefixRank] at hp
      unfold width rackX at hp hspan ⊢
      have hb := p.1.isLt
      unfold width rackX at hb
      omega
    have hy' : p.2.val ∈ L.rackProbeRows := by
      simp only [Direction.lane] at hl
      exact (hl.trans hrow.symm) ▸ hy
    rw [hx]
    exact Finset.mem_union_left _ (L.rackProbe_mem hy')
  · have hrow := congrArg Prod.fst he
    have hspan := congrArg Prod.snd he
    dsimp at hrow hspan
    have hx : p.1.val = L.rackX - 1 := by
      simp only [prefixRank] at hp
      unfold width rackX at hp hspan ⊢
      have hb := p.1.isLt
      unfold width rackX at hb
      omega
    have hy' : p.2.val ∈ L.markerRows := by
      simp only [Direction.lane] at hl
      exact (hl.trans hrow.symm) ▸ hy
    rw [hx]
    exact L.marker_mem hy'

/-- The next coordinate beyond any of the seven literal fronts is already a shared box. -/
theorem quota_boundary_shared (L : Layout) (side : Direction) (requests : List (ℕ × ℕ))
    (hstage : Template.read side requests ∈ L.quotaTemplates) {request : ℕ × ℕ}
    (hr : request ∈ requests) (p : Cell L.width L.height)
    (hl : side.lane p = request.1) (hp : prefixRank side p = request.2) :
    (p.1.val, p.2.val) ∈ L.readerShared := by
  simp only [quotaTemplates, List.mem_cons, List.not_mem_nil, or_false] at hstage
  rcases hstage with he | he | he | he | he | he | he
  · cases he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [prefixRank] at hp <;>
      have hb := p.2.isLt <;> omega
  · cases he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [prefixRank] at hp <;>
      have hb := p.1.isLt <;> omega
  · cases he
    exact False.elim (List.not_mem_nil hr)
  · cases he
    exact L.probe_boundary_shared hr p hl hp
  · cases he
    exact False.elim (List.not_mem_nil hr)
  · cases he
    obtain ⟨row, hrow, he⟩ := List.mem_map.mp hr
    have hy := congrArg Prod.fst he
    have hx := congrArg Prod.snd he
    dsimp at hy hx
    simp only [prefixRank] at hp
    simp only [Direction.lane] at hl
    rw [hp, ← hx]
    apply Finset.mem_union_left
    exact L.dividerNeighbor_mem ((hl.trans hy.symm) ▸ hrow)
  · cases he
    obtain ⟨x, _, he⟩ := List.mem_map.mp hr
    have he := congrArg Prod.snd he
    simp only [prefixRank] at hp
    dsimp at he
    have hb := p.2.isLt
    omega

/-- Moving one cell into a side's scan line increases its prefix rank by one. -/
theorem adjacent_prefixRank {w h : ℕ} (side : Direction) {p q : Cell w h}
    (ha : Adjacent side.opposite p q) : prefixRank side q = prefixRank side p + 1 := by
  have hp := p.1.isLt
  have hq := q.1.isLt
  have hp' := p.2.isLt
  have hq' := q.2.isLt
  cases side <;> simp only [Direction.opposite, Adjacent] at ha <;>
    simp only [prefixRank] <;> omega

/-- A blocked boundary coordinate keeps every removed hole run whole. -/
theorem prefix_no_split {w h : ℕ} (side : Direction) (lane span : ℕ)
    (E : Finset (Cell w h))
    (hblocked : ∀ p : Cell w h, side.lane p = lane → prefixRank side p = span → p ∉ E)
    {p q : Cell w h} (hq : q ∈ E) (hql : side.lane q = lane)
    (hfront : prefixRank side p < span) (hback : span ≤ prefixRank side q) :
    ¬ Adjacent side.opposite p q := by
  intro ha
  have hr := adjacent_prefixRank side ha
  exact hblocked q hql (by omega) hq

end PushPuzzle.PushPush.Doors.Layout
