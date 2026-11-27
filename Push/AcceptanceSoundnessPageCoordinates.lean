/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupportCoordinatesGeometry
public import Push.AcceptanceSoundnessSupportFreeze
public import PushS.PortPageSupport
import all Push.AcceptanceProgramLayout
import all PushS.PortTwoPageStreets

/-! The actual two-page versions of the two sparse acceptance supports. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

/-- The original page columns with every literal acceptance-cut row added. -/
@[expose] def twoPageFirst (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid) :
    Support.TwoPageStreets (p.W + 1) (p.H + 1) :=
  { l.twoPageStreets p hl with
    rows := (supportCoordinates l p).rows ∪ (supportCoordinates l p).cuts
    rows_separated := rows_separated l p }

/-- Guard and sample columns are added to each page, retaining the original shared main axes. -/
@[expose] def twoPageSecond (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid) :
    Support.TwoPageStreets (p.W + 1) (p.H + 1) where
  cut := (l.twoPageStreets p hl).cut
  top := l.pageColumnSet p .upper ∪ (supportCoordinates l p).guards ∪ (supportCoordinates l p).samples
  bottom := l.pageColumnSet p .lower ∪ (supportCoordinates l p).guards ∪ (supportCoordinates l p).samples
  main := l.mainColumnSet p
  rows := l.workingRowSet p
  main_top _ h := Or.inl (Or.inl ((l.twoPageStreets p hl).main_top h))
  main_bottom _ h := Or.inl (Or.inl ((l.twoPageStreets p hl).main_bottom h))
  columns_separated := by
    have he : (l.pageColumnSet p .upper ∪ (supportCoordinates l p).guards ∪ (supportCoordinates l p).samples) ∪
        (l.pageColumnSet p .lower ∪ (supportCoordinates l p).guards ∪ (supportCoordinates l p).samples) =
        (supportCoordinates l p).columns ∪ (supportCoordinates l p).guards ∪ (supportCoordinates l p).samples := by
      rw [show (supportCoordinates l p).columns = l.pageColumnSet p .upper ∪ l.pageColumnSet p .lower from
        (l.pageColumnSet_union p hl).symm]
      ext x
      simp only [Set.mem_union]
      tauto
    rw [he]
    exact columns_separated l p hl
  rows_separated := l.workingRowSet_separated p

/-- The first extension keeps exactly the original central auxiliary blockers. -/
theorem twoPageFirst_blockers_subset (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid) :
    (twoPageFirst l p hl).blockers ⊆ l.centralMarkers p :=
  l.twoPageStreets_blockers_subset p hl

/-- Every blocker of the second extension is an actual permanent central hole or a background box. -/
theorem twoPageSecond_blockers_subset (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid) :
    (twoPageSecond l p hl).blockers ⊆ l.geometricBlockers p := by
  intro q hq
  obtain ⟨hy, hx, hmain⟩ := ((twoPageSecond l p hl).mem_blockers q).mp hq
  by_cases hc : q ∈ l.centralMarkers p
  · exact Finset.mem_union_left _ hc
  · apply Finset.mem_union_right
    apply (l.mem_backgroundBoxes p q).mpr
    refine ⟨?_, hc⟩
    rintro (hcol | hrow)
    · have horiginal : q.1 ∈ (l.twoPageStreets p hl).top ∪ (l.twoPageStreets p hl).bottom := by
        change q.1 ∈ l.pageColumnSet p .upper ∪ l.pageColumnSet p .lower
        rw [l.pageColumnSet_union p hl]
        exact hcol
      exact hc (l.twoPageStreets_blockers_subset p hl
        (((l.twoPageStreets p hl).mem_blockers q).mpr ⟨hy, horiginal, hmain⟩))
    · have hval : q.2.val = p.D := congrArg Fin.val hy
      have hrow := (working_rows_iff l p q.2).mpr hrow
      have hnot := work_rows_central_gap l p hrow
      omega

/-- Both page supports satisfy the literal reverse-support rule at their computed blockers. -/
theorem twoPageFirst_relativeClosed (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid) :
    Support.RelativeClosed (twoPageFirst l p hl).support (twoPageFirst l p hl).blockers :=
  (twoPageFirst l p hl).relativeClosed

theorem twoPageSecond_relativeClosed (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid) :
    Support.RelativeClosed (twoPageSecond l p hl).support (twoPageSecond l p hl).blockers :=
  (twoPageSecond l p hl).relativeClosed

/-- Outside the original physical pages, the two extensions meet only in isolated points. -/
theorem page_extra_intersection_isolated (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ (twoPageFirst l p hl).support ∩ (twoPageSecond l p hl).support)
    (ho : q ∉ (l.twoPageStreets p hl).support) :
    Isolated ((twoPageFirst l p hl).support ∩ (twoPageSecond l p hl).support) q := by
  let P := l.twoPageStreets p hl
  let A := twoPageFirst l p hl
  let C := twoPageSecond l p hl
  have hnot : q.2 ∉ P.rows ∧ q ∉ P.vertical := not_or.mp ho
  have hqy : q.2 ∈ A.rows := hq.1.resolve_right hnot.2
  have hqx : q.1 ∈ C.top ∪ C.bottom := C.system.vertical_columns q (hq.2.resolve_left hnot.1)
  have hqG : q ∉ P.blockers := by
    intro hb
    obtain ⟨hcut, hcol, _⟩ := (P.mem_blockers q).mp hb
    rcases hcol with ht | hb
    · exact hnot.2 (Or.inr (Or.inl ⟨ht, by rw [hcut]⟩))
    · exact hnot.2 (Or.inr (Or.inr ⟨hb, by rw [hcut]⟩))
  have hcut : P.cut ∈ A.rows := by
    apply Or.inr
    change p.D ∈ cutRows p
    simp only [cutRows, List.mem_toFinset, List.mem_append, List.mem_cons]
    exact Or.inl (Or.inl trivial)
  have hv (d : Direction) (hd : d = .north ∨ d = .south) (r : Cell (p.W + 1) (p.H + 1))
      (ha : Adjacent d q r) (hr : r ∈ A.support ∩ C.support) : False := by
    have hnrow : r.2 ∉ A.rows := by
      intro hrow
      rcases hd with rfl | rfl
      · exact A.rows_separated hrow hqy ha.2
      · exact A.rows_separated hqy hrow ha.2.symm
    have hrvert : r ∈ P.vertical := hr.1.resolve_left hnrow
    have hrG : r ∉ P.blockers := by
      intro hb
      have he := ((P.mem_blockers r).mp hb).1
      exact hnrow (he.symm ▸ hcut)
    apply hnot.2
    have hd' : d.opposite = .north ∨ d.opposite = .south := by
      rcases hd with rfl | rfl <;> simp only [Direction.opposite, true_or, or_true]
    exact P.system.vertical_closed d.opposite hd' r q ha.reverse hrvert hrG hqG
  intro d r ha hr
  cases d with
  | north => exact hv .north (Or.inl rfl) r ha hr
  | south => exact hv .south (Or.inr rfl) r ha hr
  | east =>
    have hnrow : r.2 ∉ P.rows := ha.2 ▸ hnot.1
    have hrx := C.system.vertical_columns r (hr.2.resolve_left hnrow)
    exact C.columns_separated hqx hrx ha.1.symm
  | west =>
    have hnrow : r.2 ∉ P.rows := ha.2 ▸ hnot.1
    have hrx := C.system.vertical_columns r (hr.2.resolve_left hnrow)
    exact C.columns_separated hrx hqx ha.1

/-- Filling the genuine central markers leaves the exact original physical page support initially. -/
theorem canonical_filled_page_supported (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : List Bool) :
    Support.Supported (l.twoPageStreets p hl).support
      (Blocked.fill (l.canonicalInstance p hl hM ha initial target).initial (l.centralMarkers p)) := by
  apply l.encoded_without_central_page_supported p hl hM (l.canonical initial)
  exact l.physicalInstance_initial_holes p hl hM ha (l.canonical initial) (l.canonical target)

end PushPuzzle.Push.AcceptanceSoundness
