/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.PortEndpointOuterWall
public import PushS.EndpointWalking
import all PushS.PortEndpointOuterWall
import all PushS.PortEndpointWide
import all PushS.PortEndpointLocality
import all PushS.PortEndpointSeparation
import all PushS.PortWideGeometry
import all PushS.PortCentralStrip
import all PushS.PortSegments

/-! Actual inner walls beyond last-level r streets on the selected shallower rows. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

private def InnerRow (p : Scales.Parameters) (e : Endpoint)
    (g q : Cell (p.W + 1) (p.H + 1)) : Prop :=
  q.2 = g.2 ∧ (if e.inward then EndpointStreet.r.column p e < q.1.val ∧ q.1.val ≤ g.1.val
    else g.1.val ≤ q.1.val ∧ q.1.val < EndpointStreet.r.column p e)

/-- Full cells strictly beyond the r street and up to an actual inward wide separator. -/
noncomputable def endpointInnerWall (l : PortLayout) (p : Scales.Parameters) (e : Endpoint)
    {v : ℕ} (g : EndpointWideSeparator l p e v) : Finset (Cell (p.W + 1) (p.H + 1)) := by
  classical
  exact Finset.univ.filter fun q => q ∉ l.centralMarkers p ∧ q ∉ l.wideSeparatorHoles p ∧
    InnerRow p e g.cell q

private theorem mem_endpointInnerWall (l : PortLayout) (p : Scales.Parameters) (e : Endpoint)
    {v : ℕ} (g : EndpointWideSeparator l p e v) (q : Cell (p.W + 1) (p.H + 1)) :
    q ∈ l.endpointInnerWall p e g ↔ q ∉ l.centralMarkers p ∧ q ∉ l.wideSeparatorHoles p ∧
      InnerRow p e g.cell q := by
  classical
  simp only [endpointInnerWall, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem inner_interval (p : Scales.Parameters) (e : Endpoint)
    {g q : Cell (p.W + 1) (p.H + 1)} (hq : InnerRow p e g q) :
    if e.inward then p.x e.port < q.1.val ∧ q.1.val ≤ g.1.val
      else g.1.val ≤ q.1.val ∧ q.1.val < p.x e.port := by
  have hb := hq.2
  rw [EndpointStreet.column_r] at hb
  cases hd : e.inward <;> simp only [hd, Bool.false_eq_true, ite_true, ite_false] at hb ⊢ <;> omega

private theorem inner_window_not_hole (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) {e : Endpoint} (he : e ∈ l.endpoints)
    {q : Cell (p.W + 1) (p.H + 1)} (hw : q ∈ endpointPageWindow p e)
    (hin : if e.inward then EndpointStreet.r.column p e < q.1.val
      else q.1.val < EndpointStreet.r.column p e) :
    q ∉ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) := by
  rw [l.encodedSegments_endpointPageWindow p hl hM ha state e he q hw]
  rw [EndpointStreet.column_r] at hin
  intro hq
  obtain ⟨s, hs, hq⟩ := (SegmentRecipe.mem_holes _ q).mp hq
  rcases List.mem_append.mp hs with hs | hs
  · have hb := own_fixed_span l p hl hM he ((mem_pointHoles _ _).mpr ⟨s, hs, hq⟩)
    cases hd : e.inward <;> simp only [hd, Bool.false_eq_true, ite_true, ite_false] at hb hin <;> omega
  · have hb := endpoint_near p state e ((mem_pointHoles _ _).mpr ⟨s, hs, hq⟩)
    have hc : (coordinates p).x e.port = p.x e.port := rfl
    cases hd : e.inward <;> simp only [hd, Bool.false_eq_true, ite_true, ite_false, hc] at hb hin <;> omega

/-- Every actual selected inner wall starts full at every ordinary endpoint level. -/
theorem endpointInnerWall_initial_full_general (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) (e : Endpoint) (he : e ∈ l.endpoints)
    {v : ℕ} (g : EndpointWideSeparator l p e v) (hv : v ∈ l.workingDepthCoordinates p) :
    l.endpointInnerWall p e g ⊆ (l.physicalInstance p hl hM ha initial target).initial.boxes := by
  intro q hq
  obtain ⟨hc, hw, hrow⟩ := (mem_endpointInnerWall l p e g q).mp hq
  by_cases hx : Nat.dist q.1.val (p.x e.port) ≤ p.L p.levels + 16
  · have hwindow := l.endpointPageWindow_of_workingDepth p e hv q
      ((congrArg Fin.val hrow.1).trans g.row) hx
    have hin : if e.inward then EndpointStreet.r.column p e < q.1.val
        else q.1.val < EndpointStreet.r.column p e := by
      have hb := hrow.2
      cases hd : e.inward <;> simp only [hd, Bool.false_eq_true, ite_true, ite_false] at hb ⊢ <;> omega
    have hnot := inner_window_not_hole l p hl hM ha initial he hwindow hin
    change q ∈ (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p initial))ᶜ
    exact Finset.mem_compl.mpr hnot
  · apply l.encodedSegments_far_from_axes_full p hl hM initial _
      (l.physicalInstance_initial_holes p hl hM ha initial target)
      (inward_interval_off_frame l p hl ha he g hrow.1 (inner_interval p e hrow)) hc hw
    apply inward_interval_far_axes l p hl hM ha he g (inner_interval p e hrow)
    omega

/-- An actual shallow inner wall is initially full at the last allocated endpoint level. -/
theorem endpointInnerWall_initial_full (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) (e : Endpoint) (he : e ∈ l.endpoints)
    {v : ℕ} (g : EndpointWideSeparator l p e v) (hv : v ∈ l.workingDepthCoordinates p)
    (_hve : v < readDepth p e.level) (_heM : e.level = p.levels) :
    l.endpointInnerWall p e g ⊆ (l.physicalInstance p hl hM ha initial target).initial.boxes :=
  l.endpointInnerWall_initial_full_general p hl hM ha initial target e he g hv

private theorem inner_row_not_column (l : PortLayout) (p : Scales.Parameters) (e : Endpoint)
    {v : ℕ} (g : EndpointWideSeparator l p e v) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : InnerRow p e g.cell q) : q.1 ∉ l.pageColumnSet p e.side := by
  intro hc
  have hcol := g.columns _ hc (inner_interval p e hq)
  have hb := hq.2
  rw [EndpointStreet.column_r] at hb
  cases hd : e.inward <;> simp only [hd, Bool.false_eq_true, ite_true, ite_false] at hb hcol <;> omega

private theorem inner_row_point (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (e : Endpoint) {v : ℕ} (g : EndpointWideSeparator l p e v)
    (q : Cell (p.W + 1) (p.H + 1)) (hq : InnerRow p e g.cell q) :
    q ∈ l.endpointInnerWall p e g ∨ q ∈ l.pageFrozenBlockers p hl := by
  by_cases hmarkers : q ∈ l.centralMarkers p ∨ q ∈ l.wideSeparatorHoles p
  · exact Or.inr (marker_outer_blocker l p hl hmarkers)
  · have hn := not_or.mp hmarkers
    exact Or.inl ((mem_endpointInnerWall l p e g q).mpr ⟨hn.1, hn.2, hq⟩)

/-- Actual shallow inner walls are anchored horizontally at their wide hole and vertically
at the two-page frozen background. -/
theorem endpointInnerWall_anchored (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (e : Endpoint) {v : ℕ} (g : EndpointWideSeparator l p e v)
    (hv : v ∈ l.workingDepthCoordinates p) :
    Freeze.Anchored (l.endpointInnerWall p e g) (l.pageFrozenBlockers p hl) := by
  intro d q hq
  obtain ⟨_, hw, hrow⟩ := (mem_endpointInnerWall l p e g q).mp hq
  obtain ⟨r, ha, hr⟩ := l.workingRow_north_blocker p hl e.side hv q
    ((congrArg Fin.val hrow.1).trans g.row) (inner_row_not_column l p e g hrow)
  have hn : Freeze.Ray (l.endpointInnerWall p e g) (l.pageFrozenBlockers p hl) .north q := .hit ha hr
  have hh : Freeze.Ray (l.endpointInnerWall p e g) (l.pageFrozenBlockers p hl) .east q ∨
      Freeze.Ray (l.endpointInnerWall p e g) (l.pageFrozenBlockers p hl) .west q := by
    have hneq : q.1.val ≠ g.cell.1.val :=
      fun hx => hw ((Prod.ext (Fin.ext hx) hrow.1).symm ▸ g.hole)
    have hb := hrow.2
    have hg := marker_outer_blocker l p hl (Or.inr g.hole)
    cases hd : e.inward with
    | false =>
      simp only [hd, Bool.false_eq_true, ite_false] at hb
      apply Or.inr
      apply Freeze.Ray.west_of_interval hrow.1 (by omega) hg
      intro s hy hxg hx
      apply inner_row_point l p hl e g s
      refine ⟨hy.trans hrow.1, ?_⟩
      simp only [hd, Bool.false_eq_true, ite_false]
      omega
    | true =>
      simp only [hd, ite_true] at hb
      apply Or.inl
      apply Freeze.Ray.east_of_interval hrow.1 (by omega) hg
      intro s hy hx hxg
      apply inner_row_point l p hl e g s
      refine ⟨hy.trans hrow.1, ?_⟩
      simp only [hd, ite_true]
      omega
  cases d with
  | north => exact Or.inl hn
  | south => exact Or.inr hn
  | east => exact hh
  | west => exact hh.symm

/-- A single selected shallow inner wall extends the actual page freezing closure. -/
theorem endpointInnerWall_closure (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) (e : Endpoint) (he : e ∈ l.endpoints)
    {v : ℕ} (g : EndpointWideSeparator l p e v) (hv : v ∈ l.workingDepthCoordinates p)
    (hve : v < readDepth p e.level) (heM : e.level = p.levels) :
    Freeze.Closure (l.physicalInstance p hl hM ha initial target).initial (l.pageBlockers p hl)
      (l.pageFrozenBlockers p hl ∪ l.endpointInnerWall p e g) :=
  .add (l.pageBackground_closure p hl hM ha initial target)
    (l.endpointInnerWall_initial_full p hl hM ha initial target e he g hv hve heM)
    (l.endpointInnerWall_anchored p hl e g hv)

/-- One step beyond the r street in its inward direction meets the selected inner wall
or an established page blocker. -/
theorem endpointInnerWall_guard (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (e : Endpoint) {v : ℕ} (g : EndpointWideSeparator l p e v)
    {q r : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val = EndpointStreet.r.column p e)
    (hy : q.2.val = if e.side = .upper then v else p.H - v)
    (ha : Adjacent (if e.inward then .east else .west) q r) :
    r ∈ l.endpointInnerWall p e g ∪ l.pageFrozenBlockers p hl := by
  apply Finset.mem_union.mpr
  apply inner_row_point l p hl e g r
  have hqrow : q.2 = g.cell.2 := Fin.ext (hy.trans g.row.symm)
  have hry : r.2 = q.2 := by
    cases hd : e.inward <;> simp only [hd, Bool.false_eq_true, ite_true, ite_false] at ha <;> exact ha.2
  refine ⟨hry.trans hqrow, ?_⟩
  rw [EndpointStreet.column_r] at hx
  have hg := g.forward
  cases hd : e.inward <;>
    simp only [hd, Bool.false_eq_true, ite_true, ite_false, Adjacent, EndpointStreet.column_r] at hx ha hg ⊢ <;> omega

end PushPuzzle.PushS.PortLayout
