/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramPrefix
public import Push.AcceptanceProgramMargins
import all Push.AcceptanceProgramLayout
import all PushS.PortSegments
import all PushS.EndpointWalking

/-! Actual marker depths place every public f/r walk inside the first target-prefix trims. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS PushS.PortLayout

/-- Physical depth from the selected page's outer frame. -/
def pageDepth (p : Scales.Parameters) (side : Side) (q : Cell (p.W + 1) (p.H + 1)) : ℕ :=
  if side = .upper then q.2.val else p.H - q.2.val

/-- The literal trim covers exactly each public column before its first interlevel marker. -/
theorem mem_trim_region (l : PortLayout) (p : Scales.Parameters) (side : Side)
    (q : Cell (p.W + 1) (p.H + 1)) : q ∈ (trimRound l p side).region ↔
    ∃ a ∈ pageColumns l p side, a.privateColumn = false ∧
      q.1.val = a.column ∧ pageDepth p side q < trimDepth p a.level := by
  cases side <;> simp [trimRound, Template.region, mem_readRegion, pageDepth, prefixRank, Direction.lane, and_assoc]

/-- The first marker lies strictly deeper than every public corridor on its actual level. -/
theorem trimDepth_gt_work (p : Scales.Parameters) {j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ p.levels) :
    p.Y j + 2 < trimDepth p j := by
  rw [trimDepth]
  split
  · have := p.interlevel_margin j hj
    omega
  · have he : j = p.levels := by omega
    subst j
    have houter := p.outer_distance
    have hmul := Nat.mul_le_mul_right (p.Y p.levels + p.L p.levels + 10)
      (show 1 ≤ 8 * (p.axes + 1) by omega)
    simp only [Nat.one_mul] at hmul
    have hb : p.Y p.levels ≤ p.b p.levels := by
      unfold Scales.Parameters.b
      omega
    omega

/-- Each actual ordinary endpoint emits both of its public f/r columns into its own page's trim. -/
theorem endpoint_trim_column (l : PortLayout) (p : Scales.Parameters) (e : Endpoint)
    (he : e ∈ l.endpoints) (street : EndpointStreet) :
    ∃ a ∈ pageColumns l p e.side, a.column = street.column p e ∧
      a.level = e.level ∧ a.privateColumn = false := by
  cases street
  · refine ⟨⟨EndpointStreet.f.column p e, e.level, false⟩, ?_, rfl, rfl, rfl⟩
    unfold pageColumns
    apply List.mem_append_left
    apply List.mem_flatMap.mpr
    refine ⟨e, List.mem_filter.mpr ⟨?_, by simp⟩, ?_⟩
    · exact he
    · simp only [List.mem_cons]
      exact Or.inl trivial
  · refine ⟨⟨EndpointStreet.r.column p e, e.level, false⟩, ?_, rfl, rfl, rfl⟩
    unfold pageColumns
    apply List.mem_append_left
    apply List.mem_flatMap.mpr
    refine ⟨e, List.mem_filter.mpr ⟨?_, by simp⟩, ?_⟩
    · exact he
    · simp only [List.mem_cons]
      exact Or.inr (Or.inl trivial)

/-- A genuine endpoint's whole public column prefix is read before its first marker. -/
theorem endpoint_column_trim (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (e : Endpoint) (he : e ∈ l.endpoints)
    (street : EndpointStreet) (q : Cell (p.W + 1) (p.H + 1))
    (hx : q.1.val = street.column p e) (hy : pageDepth p e.side q ≤ p.Y e.level + 2) :
    q ∈ (trimRound l p e.side).region := by
  obtain ⟨a, ha, hx', hj, hprivate⟩ := endpoint_trim_column l p e he street
  obtain ⟨hjlo, hjhi⟩ := l.endpoints_level_bounds p hl hM he
  apply (mem_trim_region l p e.side q).mpr
  refine ⟨a, ha, hprivate, hx.trans hx'.symm, ?_⟩
  rw [hj]
  exact hy.trans_lt (trimDepth_gt_work p hjlo hjhi)

end PushPuzzle.Push.AcceptanceProgram

namespace PushPuzzle.PushS.PortLayout

open PushFS PushFS.Reduction SegmentRecipe

/-- Every actual f/r corridor cell has its emitted column and lies within the endpoint's public depth. -/
private theorem acceptanceEndpointCorridor (l : PortLayout) (p : Scales.Parameters) (e : Endpoint)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1)
      ((endpointFixedSegments l (coordinates p) e).take 2)) :
    ∃ street : EndpointStreet, q.1.val = street.column p e ∧
      Push.AcceptanceProgram.pageDepth p e.side q ≤ readDepth p e.level + 2 := by
  obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hq
  dsimp only [endpointFixedSegments] at hs
  simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
    List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · refine ⟨.f, ?_, ?_⟩
    · change q.1.val = (auxiliary (coordinates p) e).1
      simp only [segment, Segment.Contains, min_self, max_self] at hc
      omega
    · cases hside : e.side <;>
        simp only [Push.AcceptanceProgram.pageDepth, hside, reduceCtorEq, ite_true, ite_false,
          onSide, segment, Segment.Contains, coordinates, Coordinates.depth, readDepth] at hc ⊢ <;> omega
  · refine ⟨.r, ?_, ?_⟩
    · change q.1.val = (auxiliary (coordinates p) e).2
      simp only [segment, Segment.Contains, min_self, max_self] at hc
      omega
    · cases hside : e.side <;>
        simp only [Push.AcceptanceProgram.pageDepth, hside, reduceCtorEq, ite_true, ite_false,
          onSide, segment, Segment.Contains, coordinates, Coordinates.depth, readDepth] at hc ⊢ <;> omega

/-- The actual first four gate segments are its public lower-page columns, within the first-level depth. -/
private theorem acceptanceGateCorridors (p : Scales.Parameters) (middle : ℕ)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1)
      ((gateFixedSegments (coordinates p) middle).take 4)) :
    q.1.val ∈ [p.x middle - 2, p.x middle + 6, p.x middle + 8, p.x middle + 12] ∧
      Push.AcceptanceProgram.pageDepth p .lower q ≤ readDepth p 1 + 2 := by
  obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hq
  have hs' : s ∈ [p.x middle - 2, p.x middle + 6, p.x middle + 8, p.x middle + 12].map
      (fun col => segment col (onSide (coordinates p) .lower 1) col
        (onSide (coordinates p) .lower (readDepth p 1 - 1))) := by
    simpa only [gateFixedSegments, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, List.take_succ_cons, List.take_zero, Coordinates.x, Coordinates.depth,
      coordinates, readDepth, Scales.Parameters.x] using hs
  obtain ⟨col, hcol, rfl⟩ := List.mem_map.mp hs'
  have hx : q.1.val = col := by
    simp only [segment, Segment.Contains, min_self, max_self] at hc
    omega
  refine ⟨hx.symm ▸ hcol, ?_⟩
  simp only [Push.AcceptanceProgram.pageDepth, ite_false, reduceCtorEq,
    onSide, segment, Segment.Contains, coordinates] at hc ⊢
  omega

end PushPuzzle.PushS.PortLayout

namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS PushS.PortLayout

/-- Both literal emitted ordinary public corridors are entirely consumed by their actual first trim. -/
theorem endpoint_corridors_trim (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (e : Endpoint) (he : e ∈ l.endpoints)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1)
      ((endpointFixedSegments l (coordinates p) e).take 2)) :
    q ∈ (trimRound l p e.side).region := by
  obtain ⟨street, hx, hy⟩ := l.acceptanceEndpointCorridor p e hq
  obtain ⟨hjlo, hjhi⟩ := l.endpoints_level_bounds p hl hM he
  rw [readDepth_eq p hjlo hjhi] at hy
  exact endpoint_column_trim l p hl hM e he street q hx hy

/-- The four literal public gate corridors are included in the first lower-page trim. -/
theorem gate_corridors_trim (l : PortLayout) (p : Scales.Parameters) (middle : ℕ)
    (hi : middle ∈ l.gateCenterCoordinates) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1)
      ((gateFixedSegments (coordinates p) middle).take 4)) :
    q ∈ (trimRound l p .lower).region := by
  obtain ⟨hcol, hy⟩ := acceptanceGateCorridors p middle hq
  have hentry : (⟨q.1.val, 1, false⟩ : PageColumn) ∈ pageColumns l p .lower := by
    simp only [pageColumns, ite_true, List.mem_append]
    right
    apply List.mem_flatMap.mpr
    refine ⟨middle, hi, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcol ⊢
    rcases hcol with he | he | he | he <;> simp only [he] <;> tauto
  apply (mem_trim_region l p .lower q).mpr
  refine ⟨⟨q.1.val, 1, false⟩, hentry, rfl, rfl, ?_⟩
  rw [readDepth_eq p le_rfl p.levels_pos] at hy
  exact hy.trans_lt (trimDepth_gt_work p le_rfl p.levels_pos)

end PushPuzzle.Push.AcceptanceProgram
