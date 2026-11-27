/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortCentralMarkers
public import PushS.Support
public import PushS.PortEndpointCounts
public import PushS.PortStreetSeparation
import all PushS.PortStreetSeparation
import all PushS.PortSegments
import all PushS.PortCoreCrossing
import all PushS.PortSignalLocality
import all PushS.PortEndpointSeparation

/-!
# Actual target support after filling the permanent central holes

Every remaining hole is on an original street column or an actual working row. Exact
storage therefore supplies the sparse support directly from the emitted target bitmap.
-/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

private def selectedRows (l : PortLayout) (p : Scales.Parameters) : List ℕ :=
  [0, p.H] ++ (workingRows l (coordinates p)).flatMap fun y => [y, p.H - y]

private def OnStreet (l : PortLayout) (p : Scales.Parameters) (q : ℕ × ℕ) : Prop :=
  q.1 ∈ streetColumns l (coordinates p) ∨ q.2 ∈ selectedRows l p

private def CentralBand (p : Scales.Parameters) (q : ℕ × ℕ) : Prop :=
  p.D ≤ q.2 + 4 ∧ q.2 ≤ p.D + 4

private def StreetSegment (l : PortLayout) (p : Scales.Parameters) (s : Segment) : Prop :=
  ∀ q, s.Contains q → OnStreet l p q ∨ CentralBand p q

private def StreetSegments (l : PortLayout) (p : Scales.Parameters) (ss : List Segment) : Prop :=
  ∀ s ∈ ss, StreetSegment l p s

private theorem workingRows_level (l : PortLayout) (p : Scales.Parameters) {j : ℕ}
    (hj : 1 ≤ j) (hm : j ≤ p.levels) :
    (coordinates p).depth j ∈ workingRows l (coordinates p) ∧
      (coordinates p).depth j + 2 ∈ workingRows l (coordinates p) := by
  have hi : j - 1 ∈ List.range p.levels := List.mem_range.mpr (by omega)
  have he : j - 1 + 1 = j := by omega
  constructor
  all_goals
    apply List.mem_flatMap.mpr
    refine ⟨j - 1, hi, ?_⟩
    simp only [he]
    split <;> simp

private theorem row_onSide (l : PortLayout) (p : Scales.Parameters) (side : Side) {y : ℕ}
    (hy : y ∈ workingRows l (coordinates p)) :
    onSide (coordinates p) side y ∈ selectedRows l p := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨y, hy, ?_⟩
  cases side <;> simp [onSide, coordinates]

private theorem axis_column (l : PortLayout) (p : Scales.Parameters) {i : ℕ}
    (hi : i < l.portCount) : (coordinates p).x i ∈ streetColumns l (coordinates p) := by
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩

private theorem auxiliary_columns (l : PortLayout) (p : Scales.Parameters) {e : Endpoint}
    (he : e ∈ endpoints l) :
    (auxiliary (coordinates p) e).1 ∈ streetColumns l (coordinates p) ∧
      (auxiliary (coordinates p) e).2 ∈ streetColumns l (coordinates p) := by
  constructor
  all_goals
    apply List.mem_append_right
    apply List.mem_append_left
    apply List.mem_flatMap.mpr
    refine ⟨e, he, ?_⟩
    simp

private theorem special_column (l : PortLayout) (p : Scales.Parameters) {i x : ℕ}
    (hi : i ∈ centers l) (hx : x ∈ specialColumns (coordinates p) i) :
    x ∈ streetColumns l (coordinates p) :=
  List.mem_append_right _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨i, hi, hx⟩))

private theorem vertical_street (l : PortLayout) (p : Scales.Parameters) {x y v : ℕ}
    (hx : x ∈ streetColumns l (coordinates p)) :
    StreetSegment l p (segment x y x v) := by
  intro q hq
  exact Or.inl (Or.inl ((vertical_coordinates hq).1 ▸ hx))

private theorem horizontal_street (l : PortLayout) (p : Scales.Parameters) {x u y : ℕ}
    (hy : y ∈ selectedRows l p) : StreetSegment l p (segment x y u y) := by
  intro q hq
  exact Or.inl (Or.inr ((horizontal_coordinates hq).1 ▸ hy))

private theorem central_point (l : PortLayout) (p : Scales.Parameters) {x y : ℕ}
    (hy : p.D ≤ y + 4 ∧ y ≤ p.D + 4) : StreetSegment l p (point x y) := by
  intro q hq
  right
  change p.D ≤ q.2 + 4 ∧ q.2 ≤ p.D + 4
  rw [(point_coordinates hq).2]
  exact hy

private theorem street_append (l : PortLayout) (p : Scales.Parameters) {ss tt : List Segment}
    (hs : StreetSegments l p ss) (ht : StreetSegments l p tt) : StreetSegments l p (ss ++ tt) := by
  intro s h
  exact (List.mem_append.mp h).elim (hs s) (ht s)

private theorem street_flatMap (l : PortLayout) (p : Scales.Parameters) {α : Type} {xs : List α}
    {f : α → List Segment} (h : ∀ x ∈ xs, StreetSegments l p (f x)) :
    StreetSegments l p (xs.flatMap f) := by
  intro s hs
  obtain ⟨x, hx, hs⟩ := List.mem_flatMap.mp hs
  exact h x hx s hs

private theorem endpointFixed_streets (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) {e : Endpoint}
    (he : e ∈ endpoints l) : StreetSegments l p (endpointFixedSegments l (coordinates p) e) := by
  obtain ⟨hj, hm⟩ := l.endpoints_level_bounds p hl hM he
  have hy := workingRows_level l p hj hm
  obtain ⟨hf, hr⟩ := auxiliary_columns l p he
  dsimp only [endpointFixedSegments]
  simp only [List.append_assoc]
  apply street_append l p
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact vertical_street l p hf
    · exact vertical_street l p hr
    · exact horizontal_street l p (row_onSide l p e.side hy.2)
  · apply street_append l p
    · apply street_flatMap l p
      intro y hy
      apply street_append l p
      all_goals
        split
        · intro s hs
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
          subst s
          exact horizontal_street l p (row_onSide l p e.side hy)
        · exact fun _ h => False.elim (List.not_mem_nil h)
    · split
      · intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        · exact vertical_street l p hf
        · exact vertical_street l p hr
      · exact fun _ h => False.elim (List.not_mem_nil h)

private theorem gateFixed_streets (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    {i : ℕ} (hi : i ∈ centers l) : StreetSegments l p (gateFixedSegments (coordinates p) i) := by
  have hcol : ∀ x ∈ specialColumns (coordinates p) i, x ∈ streetColumns l (coordinates p) :=
    fun _ hx => special_column l p hi hx
  obtain ⟨kind, first, hg, he⟩ := center_gate_mem l hi
  have hi' : i < l.portCount := by rw [he]; exact gate_middle_lt l hl hg
  have haxis := axis_column l p hi'
  have hy := workingRows_level l p (j := 1) le_rfl p.levels_pos
  have hprivate : (coordinates p).x i + 4 ∈ streetColumns l (coordinates p) :=
    hcol _ (by simp [specialColumns])
  dsimp only [gateFixedSegments]
  simp only [List.append_assoc]
  apply street_append l p
  · intro s hs
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hs
    apply vertical_street l p (hcol x ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp [specialColumns]
  · apply street_append l p
    · intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl
      · exact vertical_street l p hprivate
      · exact horizontal_street l p (row_onSide l p .lower hy.2)
      · exact vertical_street l p haxis
      · exact vertical_street l p hprivate
    · split
      · intro s hs
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hs
        exact vertical_street l p (hcol x hx)
      · exact fun _ h => False.elim (List.not_mem_nil h)

private theorem wideFixed_streets (l : PortLayout) (p : Scales.Parameters) (side : Side) :
    StreetSegments l p (wideFixed l (coordinates p) side) := by
  apply street_flatMap l p
  intro ab _
  dsimp only
  split
  · intro s hs
    obtain ⟨y, hy, hs⟩ := List.mem_filterMap.mp hs
    split at hs
    · cases hs
    · simp only [Option.some.injEq] at hs
      subst s
      exact horizontal_street l p (row_onSide l p side hy)
  · exact fun _ h => False.elim (List.not_mem_nil h)

private theorem interiorFixed_streets (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) :
    StreetSegments l p (interiorFixed l (coordinates p)) := by
  unfold interiorFixed
  apply street_append l p
  · apply street_append l p
    · apply street_append l p
      · apply street_append l p
        · exact street_flatMap l p fun _ he => endpointFixed_streets l p hl hM he
        · exact street_flatMap l p fun _ hi => gateFixed_streets l p hl hi
      · exact wideFixed_streets l p .upper
    · exact wideFixed_streets l p .lower
  · intro s hs
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hs
    exact central_point l p (by change p.D ≤ p.D + 4 ∧ p.D ≤ p.D + 4; omega)

private theorem streetRows_selected (l : PortLayout) (p : Scales.Parameters) {y : ℕ}
    (hy : y ∈ streetRows (coordinates p)) : y ∈ selectedRows l p := by
  rcases List.mem_append.mp hy with hy | hy
  · exact List.mem_append_left _ hy
  · obtain ⟨j, hj, hy⟩ := List.mem_flatMap.mp hy
    have hj' := List.mem_range.mp hj
    change j < p.levels at hj'
    have hr := workingRows_level l p (j := j + 1) (by omega) (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact row_onSide l p .upper hr.1
    · exact row_onSide l p .upper hr.2
    · exact row_onSide l p .lower hr.1
    · exact row_onSide l p .lower hr.2

private theorem shiftPoint_streets (l : PortLayout) (p : Scales.Parameters) (guards : List ℕ)
    {s : Segment} (hs : StreetSegment l p s) :
    StreetSegment l p (shiftPoint guards (streetRows (coordinates p)) s) := by
  unfold shiftPoint
  split
  · rename_i hcond
    exact horizontal_street l p (streetRows_selected l p (by simpa only [List.contains_iff_mem] using hcond.2.2))
  · exact hs

private theorem markedInterior_streets (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) :
    StreetSegments l p (markedInterior l (coordinates p)) := by
  dsimp only [markedInterior]
  apply street_append l p
  · apply street_append l p
    · apply street_append l p
      · intro s hs
        split at hs
        · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hs
          exact shiftPoint_streets l p _ (interiorFixed_streets l p hl hM u hu)
        · exact interiorFixed_streets l p hl hM s hs
      · apply street_flatMap l p
        intro x _ s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl <;> exact central_point l p (by dsimp only [coordinates]; omega)
    · intro s hs
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp hs
      exact central_point l p (by have := central_marker_bounds p; dsimp only [coordinates]; omega)
  · apply street_flatMap l p
    intro i _ s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> exact central_point l p (by dsimp only [coordinates]; omega)

private theorem frame_streets (l : PortLayout) (p : Scales.Parameters) :
    StreetSegments l p (frame (coordinates p)) := by
  intro s hs
  simp only [frame, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact horizontal_street l p (by simp [selectedRows, coordinates])
  · exact horizontal_street l p (by simp [selectedRows, coordinates])
  · exact vertical_street l p (by simp [streetColumns])
  · exact vertical_street l p (by simp [streetColumns])

private theorem endpoint_signal_streets (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (state : SignalState) {e : Endpoint}
    (he : e ∈ endpoints l) : StreetSegments l p (endpointSegments (coordinates p) state e) := by
  obtain ⟨hj, hm⟩ := l.endpoints_level_bounds p hl hM he
  have hy := workingRows_level l p hj hm
  intro s hs
  simp only [endpointSegments, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact vertical_street l p (axis_column l p (l.endpoints_port_lt hl he))
  · exact horizontal_street l p (row_onSide l p e.side hy.1)

private theorem triple_signal_streets (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (state : SignalState) {g : Placement} (hg : g ∈ placements l) :
    StreetSegments l p (tripleSignal (coordinates p) state g) := by
  cases he : g.gate with
  | none => simp [tripleSignal, he, StreetSegments]
  | some kind =>
    have hgate := placement_gate_mem l hg he
    have hi := gate_middle_lt l hl hgate
    have hy := workingRows_level l p (j := 1) le_rfl p.levels_pos
    intro s hs
    simp only [tripleSignal, he, Option.elim_some, gateSegments,
      List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact horizontal_street l p (row_onSide l p .lower hy.1)
    · exact horizontal_street l p (row_onSide l p .lower hy.1)
    · exact vertical_street l p (axis_column l p hi)

private theorem encodedSegments_streets (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (state : SignalState) :
    StreetSegments l p (l.encodedSegments p state) := by
  apply street_append l p
  · exact street_append l p (frame_streets l p) (markedInterior_streets l p hl hM)
  · exact street_append l p
      (street_flatMap l p fun _ he => endpoint_signal_streets l p hl hM state he)
      (street_flatMap l p fun _ hg => triple_signal_streets l p hl state hg)

private theorem frame_onStreet (l : PortLayout) (p : Scales.Parameters)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ Boundary.frame) : OnStreet l p (q.1.val, q.2.val) := by
  obtain ⟨d, hd⟩ := (Boundary.mem_frame q).mp hq
  cases d <;> simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and] at hd
  · right
    simp [selectedRows, hd]
  · left
    have he : q.1.val = p.W := by omega
    simp [streetColumns, coordinates, he]
  · right
    have he : q.2.val = p.H := by omega
    simp [selectedRows, he]
  · left
    simp [streetColumns, hd]

private theorem encoded_without_central_onStreet (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (state : SignalState)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state))
    (hc : q ∉ l.centralMarkers p) : OnStreet l p (q.1.val, q.2.val) := by
  obtain ⟨s, hs, hq'⟩ := (SegmentRecipe.mem_holes _ q).mp hq
  rcases encodedSegments_streets l p hl hM state s hs _ hq' with hstreet | hband
  · exact hstreet
  · by_contra hstreet
    have hf : q ∉ Boundary.frame := fun hf => hstreet (frame_onStreet l p hf)
    have hfixed : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.fixedSegments p) := by
      rcases List.mem_append.mp hs with hfix | hsignal
      · exact (SegmentRecipe.mem_holes _ q).mpr ⟨s, hfix, hq'⟩
      · have hsig := (SegmentRecipe.mem_pointHoles _ _).mpr ⟨s, hsignal, hq'⟩
        have hg := l.signalSegments_central_gap p state hsig
        dsimp only [CentralBand] at hband
        omega
    exact hc (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hfixed, hf⟩, hband⟩)

/-- Filling the actual central markers leaves every encoded hole on an original sparse street. -/
theorem encoded_without_central_supported (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (state : SignalState)
    (s : State (p.W + 1) (p.H + 1))
    (hs : PushS.holes s = SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state)) :
    Support.Supported (Support.streets (l.streetColumnSet p) (l.workingRowSet p))
      (Blocked.fill s (l.centralMarkers p)) := by
  intro q hq
  have hh : q ∉ s.boxes ∧ q ∉ l.centralMarkers p := by simpa [Blocked.fill] using hq
  change OnStreet l p (q.1.val, q.2.val)
  apply encoded_without_central_onStreet l p hl hM state
  · rw [← hs]
    exact (mem_holes _).mpr hh.1
  · exact hh.2

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)

/-- Every filled solution prefix has the actual sparse original-street support. -/
theorem physicalInstance_filled_supported_at {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    Support.Supported (Support.streets (l.streetColumnSet p) (l.workingRowSet p))
      (Blocked.fill u (l.centralMarkers p)) := by
  have hr : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (Blocked.fill u (l.centralMarkers p)) (Blocked.fill t (l.centralMarkers p)) := by
    apply Blocked.reachable_fill_of_invariant (fun {_ _} h => h) hut
      (fun _ huv hvt => l.physicalInstance_central_excluded p hl hM ha initial target
        (hsu.trans huv) hvt ht)
    rw [(l.physicalInstance p hl hM ha initial target).walls_empty]
    exact Finset.disjoint_empty_right _
  apply (Support.streets_axisClosed (l.streetColumnSet_separated p)
    (l.workingRowSet_separated p)).reachable_source hr
  apply l.encoded_without_central_supported p hl hM target t
  simp only [PushS.holes, ht]
  change (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p target))ᶜᶜ = _
  simp

/-- Every actual solution player lies on an original street. -/
theorem physicalInstance_player_on_streets {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    u.player ∈ Support.streets (l.streetColumnSet p) (l.workingRowSet p) := by
  have hv := hsu.valid (l.physicalInstance p hl hM ha initial target).initial_valid
  have hg := l.physicalInstance_central_excluded p hl hM ha initial target hsu hut ht
  apply l.physicalInstance_filled_supported_at p hl hM ha initial target hsu hut ht u.player
  change u.player ∉ u.boxes ∪ l.centralMarkers p
  exact fun h => (Finset.mem_union.mp h).elim hv.2.2 hg.player

/-- The complete ray of every actual solution push stays on a single original street. -/
theorem physicalInstance_push_run_on_streets {s u t : State (p.W + 1) (p.H + 1)}
    {d : Direction} {n : ℕ}
    (hss : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial s)
    (r : Run (l.physicalInstance p hl hM ha initial target).board d s n) (hn : 0 < n)
    (hp : u.player = r.cell 1)
    (hb : u.boxes = insert (r.cell ⟨n + 1, by omega⟩) (s.boxes.erase (r.cell 1)))
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals)
    (i : Fin (n + 2)) : r.cell i ∈ Support.streets (l.streetColumnSet p) (l.workingRowSet p) := by
  have hm : Move (l.physicalInstance p hl hM ha initial target).board none d s u :=
    .push (hss.valid (l.physicalInstance p hl hM ha initial target).initial_valid) hn trivial r hp hb
  have hsp := l.physicalInstance_player_on_streets p hl hM ha initial target hss
    ((Relation.ReflTransGen.single ⟨d, hm⟩).trans hut) ht
  have hup := l.physicalInstance_player_on_streets p hl hM ha initial target (hss.tail ⟨d, hm⟩) hut ht
  exact Support.streets_axisClosed (l.streetColumnSet_separated p) (l.workingRowSet_separated p)
    (players_adjacent hm) hsp hup _ (r.lane i)

end Solution
end PushPuzzle.PushS.PortLayout
