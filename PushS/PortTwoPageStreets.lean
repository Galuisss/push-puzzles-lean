/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.PortStreetSeparation
public import PushS.PortCentralMarkers
public import PushS.CutSupport
public import PushS.PortEndpointIndexing
import all PushS.PortSegments
import all PushS.PortStreetSeparation
import all PushS.PortSignalLocality
import all PushS.PortCoreCrossing

/-!
# The actual two-page street system

The main columns contain every original axis and both side frames. Actual page columns union
to the original street columns. Every other selected column has its emitted blocking hole at
the central cut; these blockers belong to the actual permanent central-marker set.
-/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction

/-- The actual column list on one physical page. -/
def pageColumnCoordinates (l : PortLayout) (p : Scales.Parameters) (side : Side) : List ℕ :=
  pageColumns l (coordinates p) side

/-- Original axes together with both vertical frame columns. -/
def mainColumnCoordinates (l : PortLayout) (p : Scales.Parameters) : List ℕ :=
  [0, p.W] ++ axisColumns l (coordinates p)

/-- Actual finite selected columns on one physical page. -/
@[expose] def pageColumnSet (l : PortLayout) (p : Scales.Parameters) (side : Side) :
    Set (Fin (p.W + 1)) := {x | x.val ∈ pageColumnCoordinates l p side}

/-- The actual frame columns and axes, which cross the central cut. -/
@[expose] def mainColumnSet (l : PortLayout) (p : Scales.Parameters) : Set (Fin (p.W + 1)) :=
  {x | x.val ∈ mainColumnCoordinates l p}

/-- A main column is exactly a side frame or an actual numbered axis. -/
theorem mainColumnSet_iff (l : PortLayout) (p : Scales.Parameters) (x : Fin (p.W + 1)) :
    x ∈ mainColumnSet l p ↔ x.val = 0 ∨ x.val = p.W ∨ ∃ i < l.portCount, x.val = p.x i := by
  have hc (i : ℕ) : (coordinates p).x i = p.x i := rfl
  simp [mainColumnSet, mainColumnCoordinates, axisColumns, List.mem_map, eq_comm, hc]

private theorem endpoint_columns_mem (l : PortLayout) (p : Scales.Parameters)
    (e : Endpoint) (he : e ∈ l.endpoints) {x : ℕ}
    (hx : x ∈ [(auxiliary (coordinates p) e).1, p.x e.port, (auxiliary (coordinates p) e).2]) :
    x ∈ pageColumns l (coordinates p) e.side := by
  simp only [pageColumns, List.mem_append, or_assoc]
  refine Or.inr (Or.inl (List.mem_flatMap.mpr ⟨e, ?_, hx⟩))
  exact List.mem_filter.mpr ⟨he, by simp⟩

private theorem pageColumn_mem_street (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (side : Side) {x : ℕ}
    (hx : x ∈ pageColumns l (coordinates p) side) : x ∈ streetColumns l (coordinates p) := by
  simp only [pageColumns, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hx
  change x = 0 ∨ x = p.W ∨ _ at hx
  simp only [streetColumns, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc]
  rcases hx with hx | hx | hx | hx
  · exact Or.inl hx
  · exact Or.inr (Or.inl hx)
  · obtain ⟨e, he, hx⟩ := List.mem_flatMap.mp hx
    have hem := List.mem_of_mem_filter he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | hx | hx
    · right; right; right
      apply List.mem_append_left
      exact List.mem_flatMap.mpr ⟨e, hem, by simp [hx]⟩
    · right; right; left
      apply List.mem_map.mpr
      exact ⟨e.port, List.mem_range.mpr (l.endpoints_port_lt hl hem), hx.symm⟩
    · right; right; right
      apply List.mem_append_left
      exact List.mem_flatMap.mpr ⟨e, hem, by simp [hx]⟩
  · split at hx
    · obtain ⟨i, hi, hx⟩ := List.mem_flatMap.mp hx
      rcases List.mem_cons.mp hx with hx | hx
      · obtain ⟨kind, first, hg, rfl⟩ := center_gate_mem l hi
        right; right; left
        exact List.mem_map.mpr ⟨first + 1,
          List.mem_range.mpr (gate_middle_lt l hl hg), hx.symm⟩
      · right; right; right
        apply List.mem_append_right
        exact List.mem_flatMap.mpr ⟨i, hi, hx⟩
    · cases hx

private theorem streetColumn_mem_page (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) {x : ℕ} (hx : x ∈ streetColumns l (coordinates p)) :
    x ∈ pageColumns l (coordinates p) .upper ∨ x ∈ pageColumns l (coordinates p) .lower := by
  simp only [streetColumns, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hx
  change x = 0 ∨ x = p.W ∨ _ at hx
  rcases hx with hx | hx | hx | hx
  · left
    simp [pageColumns, hx, show (coordinates p).W = p.W from rfl]
  · left
    simp [pageColumns, hx, show (coordinates p).W = p.W from rfl]
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact Or.inl (axis_in_pageColumns l p hl .upper (List.mem_range.mp hi))
  · rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨e, he, hx⟩ := List.mem_flatMap.mp hx
      have hx' : x ∈ [(auxiliary (coordinates p) e).1, p.x e.port,
          (auxiliary (coordinates p) e).2] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
        tauto
      have hp := endpoint_columns_mem l p e he hx'
      cases hs : e.side with
      | upper => exact Or.inl (hs ▸ hp)
      | lower => exact Or.inr (hs ▸ hp)
    · obtain ⟨i, hi, hx⟩ := List.mem_flatMap.mp hx
      right
      simp only [pageColumns, List.mem_append, or_assoc, ite_true]
      exact Or.inr (Or.inr (List.mem_flatMap.mpr ⟨i, hi, List.mem_cons_of_mem _ hx⟩))

/-- The actual upper and lower page columns together are exactly the original streets. -/
theorem pageColumnSet_union (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid) :
    pageColumnSet l p .upper ∪ pageColumnSet l p .lower = streetColumnSet l p := by
  ext x
  constructor
  · intro hx
    exact hx.elim (pageColumn_mem_street l p hl .upper) (pageColumn_mem_street l p hl .lower)
  · exact streetColumn_mem_page l p hl

/-- Every actual main axis and side-frame column occurs on both physical pages. -/
theorem mainColumnSet_subset_pageColumnSet (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (side : Side) : mainColumnSet l p ⊆ pageColumnSet l p side := by
  intro x hx
  rcases (mainColumnSet_iff l p x).mp hx with hx | hx | ⟨i, hi, hx⟩
  · change x.val ∈ pageColumns l (coordinates p) side
    simp [pageColumns, hx, show (coordinates p).W = p.W from rfl]
  · change x.val ∈ pageColumns l (coordinates p) side
    simp [pageColumns, hx, show (coordinates p).W = p.W from rfl]
  · change x.val ∈ pageColumns l (coordinates p) side
    rw [hx]
    exact axis_in_pageColumns l p hl side hi

/-- The actual two-page coordinate data and proved sparse-street fields. -/
@[expose] def twoPageStreets (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid) :
    Support.TwoPageStreets (p.W + 1) (p.H + 1) where
  cut := ⟨p.D, by unfold Scales.Parameters.H; omega⟩
  top := pageColumnSet l p .upper
  bottom := pageColumnSet l p .lower
  main := mainColumnSet l p
  rows := workingRowSet l p
  main_top := mainColumnSet_subset_pageColumnSet l p hl .upper
  main_bottom := mainColumnSet_subset_pageColumnSet l p hl .lower
  columns_separated := by rw [pageColumnSet_union l p hl]; exact l.streetColumnSet_separated p
  rows_separated := l.workingRowSet_separated p

private theorem cut_not_streetRow (p : Scales.Parameters) :
    p.D ∉ streetRows (coordinates p) := by
  have hD := readDepth_add_lt_D p 0
  have hH : p.H = 2 * p.D := rfl
  intro hy
  change p.D ∈ [0, p.H] ++ _ at hy
  rcases List.mem_append.mp hy with hy | hy
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    omega
  · obtain ⟨j, _, hy⟩ := List.mem_flatMap.mp hy
    have hd := readDepth_add_lt_D p (j + 1)
    change p.D ∈ [readDepth p (j + 1), readDepth p (j + 1) + 2,
      p.H - readDepth p (j + 1), p.H - (readDepth p (j + 1) + 2)] at hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    omega

private theorem shiftPoint_cut (p : Scales.Parameters) (guards : List ℕ) (x : ℕ) :
    shiftPoint guards (streetRows (coordinates p)) (point x p.D) = point x p.D := by
  simp [shiftPoint, point, segment, cut_not_streetRow]

private theorem auxiliary_cut_mem_fixed (l : PortLayout) (p : Scales.Parameters) {x : ℕ}
    (hx : x ∈ originalAuxiliary l (coordinates p)) : point x p.D ∈ l.fixedSegments p := by
  have hbase : point x p.D ∈ interiorFixed l (coordinates p) := by
    unfold interiorFixed
    apply List.mem_append_right
    exact List.mem_map.mpr ⟨x, hx, rfl⟩
  unfold fixedSegments
  apply List.mem_append_right
  unfold markedInterior
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_left
  split
  · exact List.mem_map.mpr ⟨point x p.D, hbase, shiftPoint_cut p _ x⟩
  · exact hbase

/-- Every non-main original street column has its actual emitted central blocking hole. -/
theorem central_cut_mem_markers (l : PortLayout) (p : Scales.Parameters)
    (q : Cell (p.W + 1) (p.H + 1)) (hy : q.2.val = p.D)
    (hx : q.1 ∈ streetColumnSet l p) (hm : q.1 ∉ mainColumnSet l p) :
    q ∈ l.centralMarkers p := by
  have hx0 : q.1.val ≠ 0 := fun h => hm ((mainColumnSet_iff l p q.1).mpr (Or.inl h))
  have hxW : q.1.val ≠ p.W :=
    fun h => hm ((mainColumnSet_iff l p q.1).mpr (Or.inr (Or.inl h)))
  have haux : q.1.val ∈ originalAuxiliary l (coordinates p) := by
    change q.1.val ∈ streetColumns l (coordinates p) at hx
    simp only [streetColumns, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hx
    rcases hx with hx | hx | hx | hx
    · exact False.elim (hx0 hx)
    · exact False.elim (hxW hx)
    · obtain ⟨i, hi, he⟩ := List.mem_map.mp hx
      exact False.elim (hm ((mainColumnSet_iff l p q.1).mpr
        (Or.inr (Or.inr ⟨i, List.mem_range.mp hi, he.symm⟩))))
    · exact hx
  have hf : q ∉ Boundary.frame := by
    intro hq
    obtain ⟨d, hd⟩ := (Boundary.mem_frame q).mp hq
    have hD := readDepth_add_lt_D p 0
    have hH : p.H = 2 * p.D := rfl
    cases d <;> simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and] at hd <;>
      omega
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_sdiff.mpr ⟨?_, hf⟩, by omega⟩
  apply (SegmentRecipe.mem_holes _ q).mpr
  refine ⟨point q.1.val p.D, auxiliary_cut_mem_fixed l p haux, ?_⟩
  simp [point, segment, Segment.Contains, hy]

/-- Every blocker of the actual two-page system is an actual permanent central marker. -/
theorem twoPageStreets_blockers_subset (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) : (l.twoPageStreets p hl).blockers ⊆ l.centralMarkers p := by
  intro q hq
  obtain ⟨hy, hx, hm⟩ := ((l.twoPageStreets p hl).mem_blockers q).mp hq
  have hy' := congrArg Fin.val hy
  change q.2.val = p.D at hy'
  change q.1 ∈ pageColumnSet l p .upper ∪ pageColumnSet l p .lower at hx
  rw [pageColumnSet_union l p hl] at hx
  exact l.central_cut_mem_markers p q hy' hx hm

end PushPuzzle.PushS.PortLayout
