/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessCentral
public import Push.AcceptanceProgramCut
public import PushS.PortStreetSupport
import all Push.AcceptanceProgramLayout
import all PushS.PortSegments

/-! The two actual sparse supports used by the multilevel endpoint certificate. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

/-- Complete selected rows and columns, together with the actual three acceptance additions. -/
structure SupportCoordinates (w h : ℕ) where
  columns : Set (Fin w)
  rows : Set (Fin h)
  cuts : Set (Fin h)
  guards : Set (Fin w)
  samples : Set (Fin w)

/-- Original physical streets of these coordinates. -/
@[expose] def SupportCoordinates.original {w h : ℕ} (c : SupportCoordinates w h) : Set (Cell w h) :=
  Support.streets c.columns c.rows

/-- Original columns together with working rows and all acceptance-cut rows. -/
@[expose] def SupportCoordinates.first {w h : ℕ} (c : SupportCoordinates w h) : Set (Cell w h) :=
  Support.streets c.columns (c.rows ∪ c.cuts)

/-- Original, guard and sample columns together with the original working rows. -/
@[expose] def SupportCoordinates.second {w h : ℕ} (c : SupportCoordinates w h) : Set (Cell w h) :=
  Support.streets (c.columns ∪ c.guards ∪ c.samples) c.rows

/-- The literal coordinate families of the actual marked source and its static acceptance program. -/
@[expose] def supportCoordinates (l : PortLayout) (p : Scales.Parameters) :
    SupportCoordinates (p.W + 1) (p.H + 1) where
  columns := l.streetColumnSet p
  rows := l.workingRowSet p
  cuts := {y | y.val ∈ cutRows p}
  guards := {x | x.val ∈ AcceptanceProgram.guards l p}
  samples := {x | x.val ∈ AcceptanceProgram.samples l p}

/-- The static working-row enumeration and the actual physical row set agree exactly. -/
theorem working_rows_iff (l : PortLayout) (p : Scales.Parameters) (y : Fin (p.H + 1)) :
    y.val ∈ workRows l p ↔ y ∈ l.workingRowSet p := by
  exact List.mem_toFinset

/-- Numeric membership interface for the first actual sparse support. -/
theorem first_support_iff (l : PortLayout) (p : Scales.Parameters) (q : Cell (p.W + 1) (p.H + 1)) :
    q ∈ (supportCoordinates l p).first ↔
      q.1.val ∈ l.streetColumnCoordinates p ∨ q.2.val ∈ workRows l p ∪ cutRows p := by
  simp only [SupportCoordinates.first, supportCoordinates, Support.streets, Set.mem_ofPred_eq,
    Set.mem_union, Finset.mem_union, working_rows_iff]
  rfl

/-- Numeric membership interface for the second actual sparse support. -/
theorem second_support_iff (l : PortLayout) (p : Scales.Parameters) (q : Cell (p.W + 1) (p.H + 1)) :
    q ∈ (supportCoordinates l p).second ↔
      q.1.val ∈ (l.streetColumnCoordinates p).toFinset ∪ guards l p ∪ samples l p ∨
        q.2.val ∈ workRows l p := by
  simp only [SupportCoordinates.second, supportCoordinates, Support.streets, Set.mem_ofPred_eq,
    Set.mem_union, Finset.mem_union, List.mem_toFinset, working_rows_iff]
  rfl

private theorem depth_mod_four (p : Scales.Parameters) (j : ℕ) : p.Y j % 4 = 0 := by
  simp [Scales.Parameters.Y, Scales.Parameters.A, Scales.Parameters.Q, Nat.mul_mod]

private theorem height_mod_two (p : Scales.Parameters) : p.H % 2 = 0 := by
  simp [Scales.Parameters.H]

/-- Every actual central, half-depth and interlevel acceptance row has even coordinate. -/
theorem cut_rows_even (p : Scales.Parameters) {row : ℕ} (hr : row ∈ cutRows p) : row % 2 = 0 := by
  simp only [cutRows, List.mem_toFinset, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (hr | hr) | hr
  · rw [hr]
    simp [Scales.Parameters.D, Scales.Parameters.A, Scales.Parameters.Q, Nat.mul_mod]
  · have hY := depth_mod_four p 1
    have hH := height_mod_two p
    omega
  · obtain ⟨j, _, hr⟩ := List.mem_flatMap.mp hr
    have hY := depth_mod_four p (j + 1)
    have hN := depth_mod_four p (j + 2)
    have hH := height_mod_two p
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with hr | hr <;> omega

/-- Original working rows together with every actual acceptance-cut row contain no consecutive coordinates. -/
theorem rows_separated (l : PortLayout) (p : Scales.Parameters) :
    Support.Separated ((supportCoordinates l p).rows ∪ (supportCoordinates l p).cuts) := by
  intro a b ha hb he
  have heven (y : Fin (p.H + 1)) (hy : y ∈ (supportCoordinates l p).rows ∪ (supportCoordinates l p).cuts) :
      y.val % 2 = 0 := by
    rcases hy with hy | hy
    · exact l.workingRowSet_even p hy
    · exact cut_rows_even p hy
  have := heven a ha
  have := heven b hb
  omega

/-- Every short-train sample column has even coordinate. -/
theorem sample_columns_even (l : PortLayout) (p : Scales.Parameters) {x : ℕ}
    (hx : x ∈ samples l p) : x % 2 = 0 := by
  obtain ⟨i, hi, hx⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hx)
  have he : p.x i % 2 = 0 := by
    simp [Scales.Parameters.x, Scales.Parameters.D, Scales.Parameters.A, Scales.Parameters.Q, Nat.mul_mod]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with hx | hx <;> omega

/-- The original columns and actual sample columns form one separated coordinate family. -/
theorem columns_samples_separated (l : PortLayout) (p : Scales.Parameters) :
    Support.Separated ((supportCoordinates l p).columns ∪ (supportCoordinates l p).samples) := by
  intro a b ha hb he
  have heven (x : Fin (p.W + 1)) (hx : x ∈ (supportCoordinates l p).columns ∪ (supportCoordinates l p).samples) :
      x.val % 2 = 0 := by
    rcases hx with hx | hx
    · exact l.streetColumnSet_even p hx
    · exact sample_columns_even l p hx
  have := heven a ha
  have := heven b hb
  omega

/-- After filling the new marker holes, the actual canonical initial state already has only original-street holes. -/
theorem canonical_filled_original_supported (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : List Bool) :
    Support.Supported (supportCoordinates l p).original
      (Blocked.fill (l.canonicalInstance p hl hM ha initial target).initial (newCentralMarkers l p)) := by
  intro q hq
  have hh : q ∉ (l.canonicalInstance p hl hM ha initial target).initial.boxes ∧ q ∉ newCentralMarkers l p := by
    change q ∉ (l.canonicalInstance p hl hM ha initial target).initial.boxes ∪ newCentralMarkers l p at hq
    exact ⟨fun hb => hq (Finset.mem_union_left _ hb), fun hm => hq (Finset.mem_union_right _ hm)⟩
  have hsource : PushS.holes (l.canonicalInstance p hl hM ha initial target).initial = targetHoles l p initial :=
    l.physicalInstance_initial_holes p hl hM ha (l.canonical initial) (l.canonical target)
  have he : q ∈ targetHoles l p initial := by
    rw [← hsource]
    exact (PushS.mem_holes _).mpr hh.1
  by_cases hc : q ∈ l.centralMarkers p
  · have hy : q.2.val = p.D := by
      by_contra hy
      exact hh.2 (Finset.mem_filter.mpr ⟨hc, hy⟩)
    have hf := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hc).1).2
    have haux := l.acceptanceOriginalAux_mem p hl hM ha (l.acceptanceCutAux p (l.canonical initial) he hf hy)
    exact Or.inl (List.mem_toFinset.mp (Finset.mem_sdiff.mp haux).1)
  · have hs := l.encoded_without_central_supported p hl hM (l.canonical initial)
      (l.canonicalInstance p hl hM ha initial target).initial hsource
    apply hs q
    change q ∉ (l.canonicalInstance p hl hM ha initial target).initial.boxes ∪ l.centralMarkers p
    intro hm
    exact (Finset.mem_union.mp hm).elim hh.1 hc

end PushPuzzle.Push.AcceptanceSoundness
