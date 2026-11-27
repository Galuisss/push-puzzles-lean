/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortBackground
import all PushS.PortStreetSeparation
import all PushS.PortSegments
import all PushS.PortHoleBudget
import all PushS.PortEndpointSeparation

/-!
# The actual full central strip between both working pages

All noncentral interior holes lie no deeper than the last working row plus two. Filling
the permanent central markers therefore leaves a full strip between the two pages.
-/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

private def LayerBand (p : Scales.Parameters) (y : ℕ) : Prop :=
  y ≤ p.Y p.levels + 2 ∨ p.H ≤ y + p.Y p.levels + 2 ∨
    (p.D ≤ y + 4 ∧ y ≤ p.D + 4)

private def BandSegment (p : Scales.Parameters) (s : Segment) : Prop :=
  ∀ q, s.Contains q → LayerBand p q.2

private def BandSegments (p : Scales.Parameters) (ss : List Segment) : Prop :=
  ∀ s ∈ ss, BandSegment p s

private theorem last_depth_margin (p : Scales.Parameters) : p.Y p.levels + 64 < p.D := by
  have h := readDepth_add_lt_D p p.levels
  rw [readDepth_eq p p.levels_pos le_rfl] at h
  exact h

private theorem side_segment_band (p : Scales.Parameters) (side : Side) {x u y v : ℕ}
    (hy : y ≤ p.Y p.levels + 2) (hv : v ≤ p.Y p.levels + 2) :
    BandSegment p (segment x (onSide (coordinates p) side y) u (onSide (coordinates p) side v)) := by
  intro q hq
  have hm := last_depth_margin p
  have hH : p.H = 2 * p.D := rfl
  cases side <;> simp only [segment, Segment.Contains, onSide, coordinates, ite_true,
    reduceCtorEq, ite_false] at hq
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))

private theorem point_band (p : Scales.Parameters) {x y : ℕ}
    (hy : p.D ≤ y + 4 ∧ y ≤ p.D + 4) : BandSegment p (point x y) := by
  intro q hq
  have he := (point_coordinates hq).2
  exact Or.inr (Or.inr (he ▸ hy))

private theorem band_append (p : Scales.Parameters) {ss tt : List Segment}
    (hs : BandSegments p ss) (ht : BandSegments p tt) : BandSegments p (ss ++ tt) := by
  intro s h
  exact (List.mem_append.mp h).elim (hs s) (ht s)

private theorem band_flatMap (p : Scales.Parameters) {α : Type} {xs : List α}
    {f : α → List Segment} (h : ∀ x ∈ xs, BandSegments p (f x)) :
    BandSegments p (xs.flatMap f) := by
  intro s hs
  obtain ⟨x, hx, hs⟩ := List.mem_flatMap.mp hs
  exact h x hx s hs

private theorem workingRows_le_last (l : PortLayout) (p : Scales.Parameters) {y : ℕ}
    (hy : y ∈ workingRows l (coordinates p)) : y ≤ p.Y p.levels + 2 := by
  obtain ⟨j, _, hy⟩ := List.mem_flatMap.mp hy
  have hb := readDepth_le_last p (j + 1)
  change (coordinates p).depth (j + 1) ≤ p.Y p.levels at hb
  dsimp only at hy
  split at hy <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hy <;> omega

private theorem endpointFixed_band (l : PortLayout) (p : Scales.Parameters) (e : Endpoint) :
    BandSegments p (endpointFixedSegments l (coordinates p) e) := by
  have hy := readDepth_le_last p e.level
  have hn := readDepth_le_last p (e.level + 1)
  have hY := p.Y_ge p.levels
  change (coordinates p).depth e.level ≤ p.Y p.levels at hy
  change (coordinates p).depth (e.level + 1) ≤ p.Y p.levels at hn
  dsimp only [endpointFixedSegments]
  simp only [List.append_assoc]
  apply band_append p
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl <;> apply side_segment_band p e.side <;> omega
  · apply band_append p
    · apply band_flatMap p
      intro y hrow
      have hb := workingRows_le_last l p hrow
      apply band_append p
      all_goals
        split
        · intro s hs
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
          subst s
          exact side_segment_band p e.side hb hb
        · exact fun _ h => False.elim (List.not_mem_nil h)
    · split
      · intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl <;> apply side_segment_band p e.side <;> omega
      · exact fun _ h => False.elim (List.not_mem_nil h)

private theorem gateFixed_band (p : Scales.Parameters) (i : ℕ) :
    BandSegments p (gateFixedSegments (coordinates p) i) := by
  have hy := readDepth_le_last p 1
  have hn := readDepth_le_last p 2
  have hY := p.Y_ge p.levels
  change (coordinates p).depth 1 ≤ p.Y p.levels at hy
  change (coordinates p).depth 2 ≤ p.Y p.levels at hn
  dsimp only [gateFixedSegments]
  simp only [List.append_assoc]
  apply band_append p
  · intro s hs
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hs
    apply side_segment_band p .lower <;> omega
  · apply band_append p
    · intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl <;> apply side_segment_band p .lower <;> omega
    · split
      · intro s hs
        obtain ⟨x, _, rfl⟩ := List.mem_map.mp hs
        apply side_segment_band p .lower <;> omega
      · exact fun _ h => False.elim (List.not_mem_nil h)

private theorem wideFixed_band (l : PortLayout) (p : Scales.Parameters) (side : Side) :
    BandSegments p (wideFixed l (coordinates p) side) := by
  apply band_flatMap p
  intro ab _
  dsimp only
  split
  · intro s hs
    obtain ⟨y, hy, hs⟩ := List.mem_filterMap.mp hs
    split at hs
    · cases hs
    · simp only [Option.some.injEq] at hs
      subst s
      have hb := workingRows_le_last l p hy
      exact side_segment_band p side hb hb
  · exact fun _ h => False.elim (List.not_mem_nil h)

private theorem interiorFixed_band (l : PortLayout) (p : Scales.Parameters) :
    BandSegments p (interiorFixed l (coordinates p)) := by
  unfold interiorFixed
  apply band_append p
  · apply band_append p
    · apply band_append p
      · exact band_append p (band_flatMap p fun e _ => endpointFixed_band l p e)
          (band_flatMap p fun i _ => gateFixed_band p i)
      · exact wideFixed_band l p .upper
    · exact wideFixed_band l p .lower
  · intro s hs
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hs
    exact point_band p (by dsimp only [coordinates]; omega)

private theorem shifted_band (p : Scales.Parameters) (guards rows : List ℕ) {s : Segment}
    (hs : BandSegment p s) : BandSegment p (shiftPoint guards rows s) := by
  unfold shiftPoint
  split
  · rename_i hcond
    have hself : s.Contains s.start := by
      right
      exact ⟨congrArg Prod.snd hcond.1, rfl, min_le_left _ _, le_max_left _ _⟩
    intro q hq
    rw [(point_coordinates hq).2]
    exact hs s.start hself
  · exact hs

private theorem markedInterior_band (l : PortLayout) (p : Scales.Parameters) :
    BandSegments p (markedInterior l (coordinates p)) := by
  dsimp only [markedInterior]
  apply band_append p
  · apply band_append p
    · apply band_append p
      · intro s hs
        split at hs
        · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hs
          exact shifted_band p _ _ (interiorFixed_band l p u hu)
        · exact interiorFixed_band l p s hs
      · apply band_flatMap p
        intro x _ s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl <;> exact point_band p (by dsimp only [coordinates]; omega)
    · intro s hs
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hs
      exact point_band p (by have := central_marker_bounds p; dsimp only [coordinates]; omega)
  · apply band_flatMap p
    intro i _ s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> exact point_band p (by dsimp only [coordinates]; omega)

private theorem endpoint_signal_band (p : Scales.Parameters) (state : SignalState) (e : Endpoint) :
    BandSegments p (endpointSegments (coordinates p) state e) := by
  have hy := readDepth_le_last p e.level
  have hb := Bool.toNat_le (if e.side = .upper then state.axes.getD e.port false
    else !(state.axes.getD e.port false))
  change (coordinates p).depth e.level ≤ p.Y p.levels at hy
  intro s hs
  simp only [endpointSegments, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl <;> apply side_segment_band p e.side <;> omega

private theorem triple_signal_band (p : Scales.Parameters) (state : SignalState) (g : Placement) :
    BandSegments p (tripleSignal (coordinates p) state g) := by
  have hy := readDepth_le_last p 1
  change (coordinates p).depth 1 ≤ p.Y p.levels at hy
  cases he : g.gate with
  | none => simp [tripleSignal, he, BandSegments]
  | some kind =>
    intro s hs
    simp only [tripleSignal, he, Option.elim_some, gateSegments,
      List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl <;> apply side_segment_band p .lower <;> omega

/-- Every actual selected working row lies on one of the two sides of the central strip. -/
theorem workingRowSet_central_gap (l : PortLayout) (p : Scales.Parameters)
    {y : Fin (p.H + 1)} (hy : y ∈ l.workingRowSet p) :
    y.val ≤ p.Y p.levels + 2 ∨ p.H ≤ y.val + p.Y p.levels + 2 := by
  rcases (l.workingRowSet_iff p y).mp hy with hy | hy | ⟨v, hv, hy | hy⟩
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)
  · exact Or.inl (by have := workingRows_le_last l p hv; omega)
  · have hb := workingRows_le_last l p hv
    have hm := last_depth_margin p
    have hH : p.H = 2 * p.D := rfl
    exact Or.inr (by omega)

/-- After removing the actual central markers, every remaining interior hole lies in one of
the two working-page bands, including all bounded raw coordinate lookups. -/
theorem encodedSegments_central_strip (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state))
    (hf : q ∉ Boundary.frame) (hc : q ∉ l.centralMarkers p) :
    q.2.val ≤ p.Y p.levels + 2 ∨ p.H ≤ q.2.val + p.Y p.levels + 2 := by
  obtain ⟨s, hs, hq'⟩ := (SegmentRecipe.mem_holes _ q).mp hq
  have hb : LayerBand p q.2.val := by
    rcases List.mem_append.mp hs with hfixed | hsignal
    · rcases List.mem_append.mp hfixed with hframe | hmarked
      · exact False.elim (hf (frame_contains (coordinates p) q ⟨s, hframe, hq'⟩))
      · exact markedInterior_band l p s hmarked _ hq'
    · rcases List.mem_append.mp hsignal with he | hg
      · obtain ⟨e, _, he⟩ := List.mem_flatMap.mp he
        exact endpoint_signal_band p state e s he _ hq'
      · obtain ⟨g, _, hg⟩ := List.mem_flatMap.mp hg
        exact triple_signal_band p state g s hg _ hq'
  rcases hb with hb | hb | hb
  · exact Or.inl hb
  · exact Or.inr hb
  · apply False.elim
    have hfixed : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.fixedSegments p) := by
      rcases List.mem_append.mp hs with hfixed | hsignal
      · exact (SegmentRecipe.mem_holes _ q).mpr ⟨s, hfixed, hq'⟩
      · have hgap := l.signalSegments_central_gap p state
          ((SegmentRecipe.mem_pointHoles _ _).mpr ⟨s, hsignal, hq'⟩)
        omega
    exact hc (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hfixed, hf⟩, hb⟩)

/-- The full encoded central strip consists of boxes away from its permanent marker holes. -/
theorem encodedSegments_central_full (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    (s : State (p.W + 1) (p.H + 1))
    (hs : PushS.holes s = SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state))
    {q : Cell (p.W + 1) (p.H + 1)} (hf : q ∉ Boundary.frame) (hc : q ∉ l.centralMarkers p)
    (hy : p.Y p.levels + 2 < q.2.val) (hy' : q.2.val + p.Y p.levels + 2 < p.H) :
    q ∈ s.boxes := by
  by_contra hq
  have hhole : q ∈ PushS.holes s := (mem_holes _).mpr hq
  rw [hs] at hhole
  have hb := l.encodedSegments_central_strip p state hhole hf hc
  omega

/-- The actual constructed instance starts with a full strip between its working pages. -/
theorem physicalInstance_central_strip_full (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) {q : Cell (p.W + 1) (p.H + 1)}
    (hf : q ∉ Boundary.frame) (hc : q ∉ l.centralMarkers p)
    (hy : p.Y p.levels + 2 < q.2.val) (hy' : q.2.val + p.Y p.levels + 2 < p.H) :
    q ∈ (l.physicalInstance p hl hM ha initial target).initial.boxes := by
  apply l.encodedSegments_central_full p initial _ _ hf hc hy hy'
  change (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p initial))ᶜᶜ = _
  simp

end PushPuzzle.PushS.PortLayout
