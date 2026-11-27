/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortEndpointFrontRod
import all PushS.EndpointWalking
import all PushS.PortSegments
import all PushS.PortEndpointLocality
import all PushS.PortEndpointRWall
import all PushS.PortEndpointBranch
import all PushS.PortPageBackground
import all PushS.PortStreetSupport
import all PushS.PortBackground
import all PushS.PortEndpointOuterWalls
import all PushS.PortStreetSeparation
import all PushS.PortWideGeometry

/-! The actual r corridors and selected one-cell inward reader branches. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

/-- The complete ordinary r corridor up to the cell before its work row. -/
@[expose] noncomputable def endpointRWalk (p : Scales.Parameters) (e : Endpoint) :
    Finset (Cell (p.W + 1) (p.H + 1)) := by
  classical
  exact Finset.univ.filter fun q => q.1.val = EndpointStreet.r.column p e ∧
    ∃ v < readDepth p e.level, q.2.val = if e.side = .upper then v else p.H - v

/-- Actual one-cell short branches at all selected rows before the endpoint work row. -/
@[expose] noncomputable def endpointShortBranches (l : PortLayout) (p : Scales.Parameters)
    (e : Endpoint) : Finset (Cell (p.W + 1) (p.H + 1)) := by
  classical
  exact Finset.univ.filter fun q =>
    q.1.val = (if e.inward then p.x e.port + 1 else p.x e.port - 1) ∧
      ∃ v ∈ l.workingDepthCoordinates p, v < readDepth p e.level ∧
        q.2.val = if e.side = .upper then v else p.H - v

/-- The frame and the endpoint's actual r corridor with all its short reader branches. -/
@[expose] noncomputable def endpointReaderWalk (l : PortLayout) (p : Scales.Parameters)
    (e : Endpoint) : Finset (Cell (p.W + 1) (p.H + 1)) :=
  Boundary.frame ∪ (endpointRWalk p e ∪ l.endpointShortBranches p e)

private theorem mem_endpointRWalk (p : Scales.Parameters) (e : Endpoint)
    (q : Cell (p.W + 1) (p.H + 1)) :
    q ∈ endpointRWalk p e ↔ q.1.val = EndpointStreet.r.column p e ∧
      ∃ v < readDepth p e.level, q.2.val = if e.side = .upper then v else p.H - v := by
  classical
  simp only [endpointRWalk, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem mem_endpointShortBranches (l : PortLayout) (p : Scales.Parameters)
    (e : Endpoint) (q : Cell (p.W + 1) (p.H + 1)) :
    q ∈ l.endpointShortBranches p e ↔
      q.1.val = (if e.inward then p.x e.port + 1 else p.x e.port - 1) ∧
      ∃ v ∈ l.workingDepthCoordinates p, v < readDepth p e.level ∧
        q.2.val = if e.side = .upper then v else p.H - v := by
  classical
  simp only [endpointShortBranches, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem mem_endpointRWalk_iff (p : Scales.Parameters) (e : Endpoint)
    (q : Cell (p.W + 1) (p.H + 1)) :
    q ∈ endpointRWalk p e ↔ q.1.val = EndpointStreet.r.column p e ∧
      (if e.side = .upper then q.2.val < readDepth p e.level
        else p.H - readDepth p e.level < q.2.val) := by
  have hY := readDepth_add_lt_H p e.level
  have hqy := q.2.isLt
  rw [mem_endpointRWalk]
  cases e.side <;> simp only [reduceCtorEq, ite_true, ite_false]
  · exact ⟨fun ⟨hx, v, hv, hy⟩ => ⟨hx, by omega⟩, fun ⟨hx, hy⟩ => ⟨hx, q.2.val, hy, rfl⟩⟩
  · constructor
    · rintro ⟨hx, v, hv, hy⟩
      exact ⟨hx, by omega⟩
    · rintro ⟨hx, hy⟩
      exact ⟨hx, p.H - q.2.val, by omega, by omega⟩

/-- Every point of the actual r corridor is emitted as a hole of the complete board. -/
theorem endpointRWalk_subset_encoded (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) (e : Endpoint) (he : e ∈ l.endpoints) :
    endpointRWalk p e ⊆ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) := by
  intro q hq
  obtain ⟨hx, v, hv, hy⟩ := (mem_endpointRWalk p e q).mp hq
  have hd : v ≤ EndpointStreet.r.limit p e := by change v ≤ readDepth p e.level - 1; omega
  have hc : q = l.endpointStreetCell p hl ha e he .r v hd := Prod.ext (Fin.ext hx) (Fin.ext hy)
  rw [hc]
  exact l.endpointStreet_hole p hl hM ha state e he .r v hd

/-- Every actual selected short branch remains a literal hole of the complete marked encoding. -/
theorem endpointShortBranches_subset_encoded (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels)
    (state : SignalState) (e : Endpoint) (he : e ∈ l.endpoints) :
    l.endpointShortBranches p e ⊆
      SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) := by
  intro q hq
  obtain ⟨hx, v, hv, hlt, hy⟩ := (mem_endpointShortBranches l p e q).mp hq
  let s := point (inward ((coordinates p).x e.port) e.inward 1)
    (onSide (coordinates p) e.side v)
  have hs : s ∈ endpointFixedSegments l (coordinates p) e := by
    dsimp only [endpointFixedSegments]
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc]
    right; right; right; left
    apply List.mem_flatMap.mpr
    refine ⟨v, hv, List.mem_append_right _ ?_⟩
    rw [ite_eq_left (show v < (coordinates p).depth e.level from hlt)]
    exact List.mem_cons_self
  apply (SegmentRecipe.mem_holes _ q).mpr
  refine ⟨s, List.mem_append_left _ (l.endpointFixedSegments_mem_fixed p hl hM e he hs), ?_⟩
  have hx' : q.1.val = inward ((coordinates p).x e.port) e.inward 1 := hx
  have hy' : q.2.val = onSide (coordinates p) e.side v := hy
  simp only [s, point, segment, min_self, max_self, Segment.Contains]
  exact Or.inl ⟨trivial, hx', by omega, by omega⟩

/-- The entire actual reader region is empty in every emitted physical signal configuration. -/
theorem endpointReaderWalk_subset_encoded (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) (e : Endpoint) (he : e ∈ l.endpoints) :
    l.endpointReaderWalk p e ⊆
      SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) := by
  intro q hq
  rcases Finset.mem_union.mp hq with hf | hr
  · exact l.encodedSegments_frame_subset p state hf
  · exact (Finset.mem_union.mp hr).elim
      (fun h => l.endpointRWalk_subset_encoded p hl hM ha state e he h)
      (fun h => l.endpointShortBranches_subset_encoded p hl hM state e he h)

/-- The three actual long public segments lie in the public f walk or the r reader region. -/
theorem endpointBaseSegments_subset_walks (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (e : Endpoint) (he : e ∈ l.endpoints) :
    SegmentRecipe.holes (p.W + 1) (p.H + 1) ((endpointFixedSegments l (coordinates p) e).take 3) ⊆
      endpointPublicWalk p e ∪ l.endpointReaderWalk p e := by
  intro q hq
  obtain ⟨s, hs, hcontains⟩ := (SegmentRecipe.mem_holes _ q).mp hq
  obtain ⟨hj, hm⟩ := l.endpoints_level_bounds p hl hM he
  have hlo := readDepth_ge p hj hm
  have hhi := readDepth_add_lt_H p e.level
  have hd : (coordinates p).depth e.level = readDepth p e.level := rfl
  have hH : (coordinates p).H = p.H := rfl
  simp only [endpointFixedSegments, List.cons_append, List.take_succ_cons, List.take_zero,
    List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · apply Finset.mem_union_left
    apply Finset.mem_union_left
    apply (mem_endpointFWalk_iff p e q).mpr
    have hc := vertical_coordinates hcontains
    refine ⟨hc.1, ?_⟩
    cases hside : e.side <;>
      simp only [onSide, hside, reduceCtorEq, ite_true, ite_false, hd, hH] at hc ⊢ <;> omega
  · apply Finset.mem_union_right
    apply Finset.mem_union_right
    apply Finset.mem_union_left
    apply (mem_endpointRWalk_iff p e q).mpr
    have hc := vertical_coordinates hcontains
    refine ⟨hc.1, ?_⟩
    cases hside : e.side <;>
      simp only [onSide, hside, reduceCtorEq, ite_true, ite_false, hd, hH] at hc ⊢ <;> omega
  · exact Finset.mem_union_left _ (Finset.mem_union_right _
      ((longBranch_contains_iff l p hl hM e he q).mp hcontains))

/-- All actual midpoint half rods through one endpoint's working depth. -/
@[expose] noncomputable def endpointFrontRods (l : PortLayout) (p : Scales.Parameters)
    (e : Endpoint) : Finset (Cell (p.W + 1) (p.H + 1)) :=
  ((l.workingDepthCoordinates p).toFinset.filter fun v => v ≤ readDepth p e.level).biUnion
    (endpointFrontRod p e)

/-- Every box in the actual finite half-rod family is initially present. -/
theorem endpointFrontRods_initial_full (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) (e : Endpoint) (he : e ∈ l.endpoints) :
    l.endpointFrontRods p e ⊆ (l.physicalInstance p hl hM ha initial target).initial.boxes := by
  intro q hq
  obtain ⟨v, hv, hrod⟩ := Finset.mem_biUnion.mp hq
  obtain ⟨hv, hle⟩ := Finset.mem_filter.mp hv
  have hv := List.mem_toFinset.mp hv
  exact l.endpointFrontRod_initial_full p hl hM ha initial target e he
    (workingDepth_positive l p hv).1 hle hrod

/-- The actual finite half-rod family shares the proved page and reader midpoint anchors. -/
theorem endpointFrontRods_anchored (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (ha : l.portCount ≤ p.axes) (e : Endpoint) (he : e ∈ l.endpoints)
    (G : Finset (Cell (p.W + 1) (p.H + 1))) (hpage : l.pageFrozenBlockers p hl ⊆ G)
    (hmid : l.readerMidpointRows p e.level ⊆ G) : Freeze.Anchored (l.endpointFrontRods p e) G := by
  apply Freeze.Anchored.biUnion
  intro v hv
  obtain ⟨hv, hle⟩ := Finset.mem_filter.mp hv
  have hv := List.mem_toFinset.mp hv
  apply l.endpointFrontRod_anchored p hl ha e he (workingDepth_positive l p hv).1 hle hv G hpage
  intro g hx hy
  apply hmid
  classical
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, he, rfl, hx, v, hv, hle, hy⟩

/-- Every selected short-branch back neighbour belongs to the computed half-rod family. -/
theorem endpointFrontRods_back_mem (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (e : Endpoint) (he : e ∈ l.endpoints)
    {v : ℕ} (hv : v ∈ l.workingDepthCoordinates p) (hle : v ≤ readDepth p e.level)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = if e.inward then p.x e.port - 1 else p.x e.port + 1)
    (hy : q.2.val = if e.side = .upper then v else p.H - v) : q ∈ l.endpointFrontRods p e := by
  classical
  exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hv, hle⟩,
    l.endpointFrontRod_back_mem p hl hM e he hx hy⟩

/-- The work-row back cap is part of the actual last-level r-wall closure. -/
theorem endpointRWall_cap_mem (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (e : Endpoint) (g : EndpointWideSeparator l p e) (heM : e.level = p.levels)
    {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val = EndpointStreet.r.column p e)
    (hy : q.2.val = if e.side = .upper then readDepth p e.level + 1
      else p.H - (readDepth p e.level + 1)) :
    q ∈ l.pageFrozenBlockers p hl ∪ l.endpointRWall p e g := by
  by_cases hc : q ∈ l.centralMarkers p
  · exact Finset.mem_union_left _ (marker_blocker l p hl (Or.inl hc))
  by_cases hw : q ∈ l.wideSeparatorHoles p
  · exact Finset.mem_union_left _ (marker_blocker l p hl (Or.inr hw))
  apply Finset.mem_union_right
  apply (mem_endpointRWall l p e g q).mpr
  have hd : readDepth p e.level = p.Y p.levels := by
    rw [heM, readDepth_eq p p.levels_pos le_rfl]
  exact ⟨hc, hw, Or.inl ⟨hx, by simpa only [hd] using hy⟩⟩

/-- Geometric blockers protecting the actual r corridor and short reader branches. -/
structure EndpointReaderGuards (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (e : Endpoint) (G : Finset (Cell (p.W + 1) (p.H + 1))) : Prop where
  /-- The established concrete page closure. -/
  page : l.pageFrozenBlockers p hl ⊆ G
  /-- The outside of each selected r-row meets its actual side wall. -/
  outer : ∀ q ∈ endpointRWalk p e, q ∉ Boundary.frame → q.2 ∈ l.workingRowSet p →
    ∀ r, Adjacent (if e.inward then .east else .west) q r → r ∈ G
  /-- The frozen cell behind the r-column work-row cap. -/
  cap : ∀ q : Cell (p.W + 1) (p.H + 1), q.1.val = EndpointStreet.r.column p e →
    q.2.val = (if e.side = .upper then readDepth p e.level + 1
      else p.H - (readDepth p e.level + 1)) → q ∈ G
  /-- The actual midpoint half rods give all short-branch back neighbours. -/
  front : ∀ v ∈ l.workingDepthCoordinates p, v < readDepth p e.level →
    ∀ q : Cell (p.W + 1) (p.H + 1),
      q.1.val = (if e.inward then p.x e.port - 1 else p.x e.port + 1) →
      q.2.val = (if e.side = .upper then v else p.H - v) → q ∈ G

private theorem reader_r_vertical_back (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (e : Endpoint) {G : Finset (Cell (p.W + 1) (p.H + 1))} (hg : EndpointReaderGuards l p hl e G)
    {q a b : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ endpointRWalk p e)
    (han : a ∉ l.endpointReaderWalk p e) {d : Direction} (hd : d = .north ∨ d = .south)
    (ha : Adjacent d a q) (hb : Adjacent d b a) : b ∈ G := by
  have hq' := (mem_endpointRWalk_iff p e q).mp hq
  have hax : a.1.val = EndpointStreet.r.column p e := by
    rcases hd with rfl | rfl <;> exact (congrArg Fin.val ha.1.symm).trans hq'.1
  have hnot : ¬(if e.side = .upper then a.2.val < readDepth p e.level
      else p.H - readDepth p e.level < a.2.val) := by
    intro hy
    exact han (Finset.mem_union_right _ (Finset.mem_union_left _ ((mem_endpointRWalk_iff p e a).mpr ⟨hax, hy⟩)))
  apply hg.cap b
  · rcases hd with rfl | rfl <;> exact (congrArg Fin.val hb.1.symm).trans hax
  · have hY := readDepth_add_lt_H p e.level
    have hqa := q.2.isLt
    have hab := a.2.isLt
    have hbb := b.2.isLt
    rcases hd with rfl | rfl <;> cases hs : e.side <;>
      simp only [hs, reduceCtorEq, ite_true, ite_false, Adjacent] at ha hb hq' hnot ⊢ <;> omega

private theorem reader_short_vertical (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (e : Endpoint) {G : Finset (Cell (p.W + 1) (p.H + 1))} (hg : EndpointReaderGuards l p hl e G)
    {q a : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.endpointShortBranches p e)
    {d : Direction} (hd : d = .north ∨ d = .south) (ha : Adjacent d a q) : a ∈ G := by
  obtain ⟨hx, v, hv, _, hy⟩ := (mem_endpointShortBranches l p e q).mp hq
  have hqx := x_even p e.port
  have hleft := readLength_add_lt_x p e.port 0
  have hrow := l.workingRowSet_even p (l.mem_workingRowSet_of_onSide p hv e.side q.2 hy)
  apply hg.page
  apply off_page_blocker l p hl
  intro hp
  have hs := pages_subset_streets l p hl hp
  rcases hs with hc | hr
  · have he := l.streetColumnSet_even p hc
    rcases hd with rfl | rfl <;> cases hi : e.inward <;>
      simp only [hi, Bool.false_eq_true, ite_true, ite_false, Adjacent] at ha hx <;>
      have := congrArg Fin.val ha.1 <;> omega
  · have he := l.workingRowSet_even p hr
    rcases hd with rfl | rfl <;> simp only [Adjacent] at ha <;> omega

private theorem reader_r_horizontal (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (e : Endpoint) (he : e ∈ l.endpoints) {G : Finset (Cell (p.W + 1) (p.H + 1))}
    (hg : EndpointReaderGuards l p hl e G)
    {q a : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ endpointRWalk p e) (hf : q ∉ Boundary.frame)
    (han : a ∉ l.endpointReaderWalk p e) {d : Direction} (hd : d = .east ∨ d = .west)
    (hadj : Adjacent d a q) : a ∈ G := by
  have hay : a.2 = q.2 := by rcases hd with rfl | rfl <;> exact hadj.2.symm
  by_cases hr : q.2 ∈ l.workingRowSet p
  · by_cases hout : Adjacent (if e.inward then .east else .west) q a
    · exact hg.outer q hq hf hr a hout
    · obtain ⟨hx, hvq⟩ := (mem_endpointRWalk_iff p e q).mp hq
      have hmax := readDepth_le_last p e.level
      have hY := last_depth_margin p
      have hH : p.H = 2 * p.D := rfl
      have hdepth : (if e.side = .upper then q.2.val else p.H - q.2.val) ≤ p.Y p.levels + 2 := by
        cases hs : e.side <;> simp only [hs, reduceCtorEq, ite_true, ite_false] at hvq ⊢ <;> omega
      obtain ⟨v, hv, hy⟩ := selected_depth l p e.side hr hf hdepth
      have hvmax := workingRows_le_last l p hv
      have hlt : v < readDepth p e.level := by
        cases hs : e.side <;> simp only [hs, reduceCtorEq, ite_true, ite_false] at hvq hy <;> omega
      have hleft := readLength_add_lt_x p e.port 0
      have hax : a.1.val = if e.inward then p.x e.port + 1 else p.x e.port - 1 := by
        rcases hd with rfl | rfl <;> cases hi : e.inward <;>
          simp only [EndpointStreet.column_r, hi, Bool.false_eq_true, ite_true, ite_false, Adjacent, hay,
            and_true] at hx hadj hout ⊢ <;> omega
      exact False.elim (han (Finset.mem_union_right _ (Finset.mem_union_right _
        ((mem_endpointShortBranches l p e a).mpr ⟨hax, v, hv, hlt, (congrArg Fin.val hay).trans hy⟩))))
  · apply hg.page
    apply off_page_blocker l p hl
    intro hp
    have hqcol : q.1 ∈ l.streetColumnSet p := by
      rw [l.streetColumnSet_iff, ((mem_endpointRWalk p e q).mp hq).1]
      exact (auxiliary_columns l p he).2
    have heven := l.streetColumnSet_even p hqcol
    rcases pages_subset_streets l p hl hp with hc | hrow
    · have he' := l.streetColumnSet_even p hc
      rcases hd with rfl | rfl <;> simp only [Adjacent] at hadj <;> omega
    · exact hr (hay ▸ hrow)

private theorem reader_short_horizontal_back (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (e : Endpoint) {G : Finset (Cell (p.W + 1) (p.H + 1))} (hg : EndpointReaderGuards l p hl e G)
    {q a b : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.endpointShortBranches p e)
    (han : a ∉ l.endpointReaderWalk p e) {d : Direction} (hd : d = .east ∨ d = .west)
    (ha : Adjacent d a q) (hb : Adjacent d b a) : b ∈ G := by
  obtain ⟨hx, v, hv, hlt, hy⟩ := (mem_endpointShortBranches l p e q).mp hq
  have hay : a.2 = q.2 := by rcases hd with rfl | rfl <;> exact ha.2.symm
  have hby : b.2 = q.2 := by rcases hd with rfl | rfl <;> exact hb.2.symm.trans hay
  have hne : a.1.val ≠ EndpointStreet.r.column p e := by
    intro hax
    exact han (Finset.mem_union_right _ (Finset.mem_union_left _
      ((mem_endpointRWalk p e a).mpr ⟨hax, v, hlt, (congrArg Fin.val hay).trans hy⟩)))
  have hleft := readLength_add_lt_x p e.port 0
  apply hg.front v hv hlt b ?_ ((congrArg Fin.val hby).trans hy)
  rcases hd with rfl | rfl <;> cases hi : e.inward <;>
    simp only [EndpointStreet.column_r, hi, Bool.false_eq_true, ite_true, ite_false, Adjacent] at hx hne ha hb ⊢ <;> omega

/-- Concrete guards on the outside r rows, the work-row cap, and f-side back neighbours
protect the whole actual reader region. -/
theorem endpointReaderWalk_emptyBoundary (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (e : Endpoint) (he : e ∈ l.endpoints) {G : Finset (Cell (p.W + 1) (p.H + 1))}
    (hg : EndpointReaderGuards l p hl e G) :
    Freeze.EmptyBoundary (l.endpointReaderWalk p e) Boundary.frame G := by
  constructor
  intro d q a b hq hf ha han hb
  rcases Finset.mem_union.mp hq with hframe | hreader
  · exact False.elim (hf hframe)
  rcases Finset.mem_union.mp hreader with hr | hs
  · cases d with
    | north => exact Or.inr (reader_r_vertical_back l p hl e hg hr han (Or.inl rfl) ha hb)
    | south => exact Or.inr (reader_r_vertical_back l p hl e hg hr han (Or.inr rfl) ha hb)
    | east => exact Or.inl (reader_r_horizontal l p hl e he hg hr hf han (Or.inl rfl) ha)
    | west => exact Or.inl (reader_r_horizontal l p hl e he hg hr hf han (Or.inr rfl) ha)
  · cases d with
    | north => exact Or.inl (reader_short_vertical l p hl e hg hs (Or.inl rfl) ha)
    | south => exact Or.inl (reader_short_vertical l p hl e hg hs (Or.inr rfl) ha)
    | east => exact Or.inr (reader_short_horizontal_back l p hl e hg hs han (Or.inl rfl) ha hb)
    | west => exact Or.inr (reader_short_horizontal_back l p hl e hg hs han (Or.inr rfl) ha hb)

/-- An actual guarded prefix with the computed reader boundary preserves every reader hole. -/
theorem physicalInstance_endpoint_reader_empty_of_avoiding (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) (e : Endpoint) (he : e ∈ l.endpoints)
    (G : Finset (Cell (p.W + 1) (p.H + 1))) (hg : EndpointReaderGuards l p hl e G)
    {u t : State (p.W + 1) (p.H + 1)}
    (hr : Relation.ReflTransGen (Freeze.AvoidingStep
      (l.physicalInstance p hl hM ha initial target).board none G)
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    l.endpointReaderWalk p e ⊆ holes u := by
  have htf : Disjoint t.boxes Boundary.frame := by
    apply Finset.disjoint_left.mpr
    intro q hq hf
    have hh := l.encodedSegments_frame_subset p target hf
    rw [← l.physicalInstance_goal_holes p hl hM ha initial target, ← ht] at hh
    exact (Finset.mem_compl.mp hh) hq
  apply (l.endpointReaderWalk_emptyBoundary p hl e he hg).reachable_holes
  · apply enrich_path hr
    intro a b _ hm hbu
    refine ⟨hm, ?_⟩
    have hbut : Reachable (l.physicalInstance p hl hM ha initial target).board none b u :=
      Relation.ReflTransGen.mono (fun _ _ h => h.1) _ _ hbu
    have hbt := hbut.trans hut
    intro q hq
    exact (mem_holes _).mpr (fun hb =>
      Finset.disjoint_left.mp (Boundary.reachable_frame_empty hbt htf) hb hq)
  · change l.endpointReaderWalk p e ⊆
      (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p initial))ᶜᶜ
    rw [compl_compl]
    exact l.endpointReaderWalk_subset_encoded p hl hM ha initial e he

/-- A concrete freezing closure with the reader guards certifies emptiness along the same
successful physical trajectory. -/
theorem physicalInstance_endpoint_reader_empty_of_closure (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) (e : Endpoint) (he : e ∈ l.endpoints)
    (G : Finset (Cell (p.W + 1) (p.H + 1)))
    (hc : Freeze.Closure (l.physicalInstance p hl hM ha initial target).initial
      (l.pageBlockers p hl ∪ l.readerMidpointRows p p.levels) G)
    (hg : EndpointReaderGuards l p hl e G)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    l.endpointReaderWalk p e ⊆ holes u := by
  have hbase : Relation.ReflTransGen (Freeze.AvoidingStep
      (l.physicalInstance p hl hM ha initial target).board none
      (l.pageBlockers p hl ∪ l.readerMidpointRows p p.levels))
      (l.physicalInstance p hl hM ha initial target).initial u := by
    apply enrich_path hsu
    intro a b hsa hm hbu
    have hbt := hbu.trans hut
    have hA := l.physicalInstance_reader_last_midpoints_excluded p hl hM ha initial target
      hsa ((Relation.ReflTransGen.single hm).trans hbt) ht
    have hB := l.physicalInstance_reader_last_midpoints_excluded p hl hM ha initial target
      (hsa.tail hm) hbt ht
    have hp := step_page_avoiding l p hl hM ha initial target hsa hm hbt ht
    exact hp.union_excluded hA hB
  exact l.physicalInstance_endpoint_reader_empty_of_avoiding p hl hM ha initial target e he G hg
    (hc.reachable hbase) hut ht

end PushPuzzle.PushS.PortLayout
