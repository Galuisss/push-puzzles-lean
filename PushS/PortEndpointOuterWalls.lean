/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.PortEndpointOuterWall
public import PushS.EndpointWalking
import all PushS.PortEndpointOuterWall
import all PushS.PortCentralStrip
import all PushS.PortWideGeometry
import all PushS.PortSegments

/-!
# Complete outer-wall guards of a last-level ordinary endpoint

The actual finite working-depth list supplies one proved outer wide separator per row.
Their outer walls form one finite anchored region. Every outward horizontal exit from the
f corridor at a selected working row encounters this region or an existing page blocker.
-/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS

private noncomputable def outerSeparator (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (e : Endpoint) (he : e ∈ l.endpoints) (heM : e.level = p.levels)
    (v : {v // v ∈ (l.workingDepthCoordinates p).toFinset}) : EndpointOuterWideSeparator l p e v.val :=
  Classical.choice (l.endpointOuterWideSeparator_nonempty p hl hM ha he
    (List.mem_toFinset.mp v.property) (by
      have hv := workingRows_le_last l p (List.mem_toFinset.mp v.property)
      rwa [heM, readDepth_eq p p.levels_pos le_rfl]))

/-- The complete finite family of actual outer rows for one last-level ordinary endpoint. -/
noncomputable def endpointOuterWalls (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (e : Endpoint) (he : e ∈ l.endpoints) (heM : e.level = p.levels) :
    Finset (Cell (p.W + 1) (p.H + 1)) :=
  (l.workingDepthCoordinates p).toFinset.attach.biUnion fun v =>
    l.endpointOuterWall p e (outerSeparator l p hl hM ha e he heM v)

/-- Every box in the complete chosen outer-wall family is initially present. -/
theorem endpointOuterWalls_initial_full (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) (e : Endpoint) (he : e ∈ l.endpoints) (heM : e.level = p.levels) :
    l.endpointOuterWalls p hl hM ha e he heM ⊆
      (l.physicalInstance p hl hM ha initial target).initial.boxes := by
  intro q hq
  obtain ⟨v, _, hq⟩ := Finset.mem_biUnion.mp hq
  exact l.endpointOuterWall_initial_full p hl hM ha initial target e he _
    (List.mem_toFinset.mp v.property) heM hq

/-- All chosen outer rows are anchored simultaneously to the actual page blockers. -/
theorem endpointOuterWalls_anchored (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (e : Endpoint) (he : e ∈ l.endpoints) (heM : e.level = p.levels) :
    Freeze.Anchored (l.endpointOuterWalls p hl hM ha e he heM) (l.pageFrozenBlockers p hl) := by
  apply Freeze.Anchored.biUnion
  intro v _
  exact l.endpointOuterWall_anchored p hl e _ (List.mem_toFinset.mp v.property)

/-- One concrete freezing closure adds every selected outer row of the endpoint. -/
theorem endpointOuterWalls_closure (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) (e : Endpoint) (he : e ∈ l.endpoints) (heM : e.level = p.levels) :
    Freeze.Closure (l.physicalInstance p hl hM ha initial target).initial (l.pageBlockers p hl)
      (l.endpointOuterWalls p hl hM ha e he heM ∪ l.pageFrozenBlockers p hl) := by
  have hc := Freeze.Closure.add (l.pageBackground_closure p hl hM ha initial target)
    (l.endpointOuterWalls_initial_full p hl hM ha initial target e he heM)
    (l.endpointOuterWalls_anchored p hl hM ha e he heM)
  have heq : (l.pageFrozenBlockers p hl ∪ l.endpointOuterWalls p hl hM ha e he heM :
      Finset (Cell (p.W + 1) (p.H + 1))) =
      l.endpointOuterWalls p hl hM ha e he heM ∪ l.pageFrozenBlockers p hl := Finset.union_comm _ _
  exact heq ▸ hc

/-- An outward horizontal step from the actual f column hits that row's wall or a page blocker. -/
theorem endpointOuterWall_guard (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (e : Endpoint) {v : ℕ} (g : EndpointOuterWideSeparator l p e v)
    {q r : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val = EndpointStreet.f.column p e)
    (hy : q.2.val = if e.side = .upper then v else p.H - v)
    (ha : Adjacent (if e.inward then .west else .east) q r) :
    r ∈ l.endpointOuterWall p e g ∪ l.pageFrozenBlockers p hl := by
  apply Finset.mem_union.mpr
  apply outer_row_point l p hl e g r
  have hqrow : q.2 = g.cell.2 := Fin.ext (hy.trans g.row.symm)
  have hry : r.2 = q.2 := by
    cases hd : e.inward <;> simp only [hd, Bool.false_eq_true, ite_true, ite_false] at ha <;>
      exact ha.2
  refine ⟨hry.trans hqrow, ?_⟩
  rw [EndpointStreet.column_f] at hx
  have hg := g.outward
  cases hd : e.inward <;>
    simp only [hd, Bool.false_eq_true, ite_true, ite_false, Adjacent] at hx ha hg ⊢ <;> omega

private theorem selected_depth (l : PortLayout) (p : Scales.Parameters) (side : Side)
    {q : Cell (p.W + 1) (p.H + 1)} (hy : q.2 ∈ l.workingRowSet p)
    (hf : q ∉ Boundary.frame)
    (hdepth : (if side = .upper then q.2.val else p.H - q.2.val) ≤ p.Y p.levels + 2) :
    ∃ v ∈ l.workingDepthCoordinates p, q.2.val = if side = .upper then v else p.H - v := by
  rcases (l.workingRowSet_iff p q.2).mp hy with hn | hs | ⟨v, hv, hrow⟩
  · exact False.elim (hf ((Boundary.mem_frame q).mpr ⟨.north, by
      simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and, hn]⟩))
  · exact False.elim (hf ((Boundary.mem_frame q).mpr ⟨.south, by
      simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and, hs]⟩))
  · refine ⟨v, hv, ?_⟩
    have hvmax := workingRows_le_last l p hv
    have hD := last_depth_margin p
    have hH : p.H = 2 * p.D := rfl
    have hqy := q.2.isLt
    cases hside : side <;> simp only [hside, reduceCtorEq, ite_true, ite_false] at hdepth ⊢ <;>
      rcases hrow with hrow | hrow <;> omega

/-- Every outward horizontal exit from the actual last-level f corridor at a selected row
meets its concrete finite outer-wall closure. -/
theorem endpointOuterWalls_guard (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (e : Endpoint) (he : e ∈ l.endpoints) (heM : e.level = p.levels)
    {q r : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val = EndpointStreet.f.column p e)
    (hy : q.2 ∈ l.workingRowSet p) (hf : q ∉ Boundary.frame)
    (hdepth : (if e.side = .upper then q.2.val else p.H - q.2.val) ≤ p.Y p.levels + 2)
    (hadj : Adjacent (if e.inward then .west else .east) q r) :
    r ∈ l.endpointOuterWalls p hl hM ha e he heM ∪ l.pageFrozenBlockers p hl := by
  obtain ⟨v, hv, hrow⟩ := selected_depth l p e.side hy hf hdepth
  let v' : {v // v ∈ (l.workingDepthCoordinates p).toFinset} := ⟨v, List.mem_toFinset.mpr hv⟩
  have hg := l.endpointOuterWall_guard p hl e (outerSeparator l p hl hM ha e he heM v') hx hrow hadj
  rcases Finset.mem_union.mp hg with hw | hp
  · apply Finset.mem_union_left
    exact Finset.mem_biUnion.mpr ⟨v', Finset.mem_attach _ _, hw⟩
  · exact Finset.mem_union_right _ hp

end PushPuzzle.PushS.PortLayout
