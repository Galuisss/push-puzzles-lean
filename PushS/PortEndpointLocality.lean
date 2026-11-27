/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.PortHoleLocality
public import PushS.PortEndpointIndexing
import all PushS.PortSegments
import all PushS.PortEndpointCrossing
import all PushS.PortCoreCrossing
import all PushS.PortFixedSeparation
import all PushS.PortStreetSeparation
import all PushS.PortWideGeometry
import all PushS.PortCentralMargins
import all PushS.PortEndpointSeparation
import all PushS.PortAxisClear

/-!
# Complete local hole identification at actual ordinary endpoints

Each endpoint window has depth one through its working depth plus three and horizontal
radius its allocated branch length plus sixteen. Within this window, the complete emitted
hole set is exactly this endpoint's original fixed and signal union. Its fixed pieces survive
the emitter's conditional point rounding.
-/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

/-- The exact physical neighbourhood of one endpoint, reflected on the lower page. -/
@[expose] def endpointWindow (p : Scales.Parameters) (e : Endpoint) : Set (Cell (p.W + 1) (p.H + 1)) :=
  {q | (if e.side = .upper then 1 ≤ q.2.val ∧ q.2.val ≤ readDepth p e.level + 3
      else p.H - (readDepth p e.level + 3) ≤ q.2.val ∧ q.2.val ≤ p.H - 1) ∧
    Nat.dist q.1.val (p.x e.port) ≤ readLength p e.level + 16}

private theorem x_mod_four (p : Scales.Parameters) (i : ℕ) : p.x i % 4 = 0 := by
  simp [Scales.Parameters.x, Scales.Parameters.D, Scales.Parameters.A, Scales.Parameters.Q, Nat.mul_mod]

private theorem L_mod_four (p : Scales.Parameters) (j : ℕ) : p.L j % 4 = 0 := by
  by_cases hj : j = 0 <;>
    simp [Scales.Parameters.L, hj, Scales.Parameters.A, Scales.Parameters.Q, Nat.mul_mod]

private theorem readLength_mod_four (p : Scales.Parameters) (j : ℕ) : readLength p j % 4 = 0 := by
  by_cases hj : j = 0
  · simp [hj, readLength, lengthTable]
  · by_cases hm : j ≤ p.levels
    · rw [readLength_eq p (by omega) hm]
      exact L_mod_four p j
    · rw [readLength_eq_zero p (by omega)]

private theorem midpoint_even (p : Scales.Parameters) (e : Endpoint) :
    (((auxiliary (coordinates p) e).1 + (coordinates p).x e.port) / 2) % 2 = 0 := by
  have hx := x_mod_four p e.port
  have hL := readLength_mod_four p e.level
  change ((if e.inward then p.x e.port - readLength p e.level
    else p.x e.port + readLength p e.level) + p.x e.port) / 2 % 2 = 0
  cases e.inward <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega

private theorem point_eq_of_degenerate (s : Segment) (h : s.start = s.finish) :
    point s.start.1 s.start.2 = s := by
  cases s with
  | mk a b =>
    change a = b at h
    subst b
    cases a
    simp [point, segment]

private theorem shiftPoint_even (guards rows : List ℕ) (s : Segment)
    (hx : s.start.1 % 2 = 0) : shiftPoint guards rows s = s := by
  unfold shiftPoint
  split
  · rename_i h
    rw [hx, Nat.sub_zero]
    exact point_eq_of_degenerate s h.1
  · rfl

private theorem shiftPoint_horizontal (guards rows : List ℕ) (x u y : ℕ) (hx : x ≠ u) :
    shiftPoint guards rows (segment x y u y) = segment x y u y := by
  have hne : (segment x y u y).start ≠ (segment x y u y).finish := by
    intro h
    have he := congrArg Prod.fst h
    simp only [segment] at he
    omega
  simp [shiftPoint, hne]

private theorem guard_not_street (l : PortLayout) (p : Scales.Parameters) (ss : List Segment)
    {x : ℕ} (hx : x ∈ streetColumns l (coordinates p)) :
    x ∉ guardColumns l (coordinates p) ss := by
  intro hguard
  obtain ⟨s, _, hguard⟩ := List.mem_filterMap.mp hguard
  split at hguard
  · rename_i hcond
    have hxs : s.start.1 = x := Option.some.inj hguard
    have ht : (streetColumns l (coordinates p)).contains s.start.1 = true :=
      List.contains_iff_mem.mpr (hxs.symm ▸ hx)
    simpa only [ht, Bool.not_true, Bool.false_eq_true] using hcond.2.1
  · cases hguard

private theorem shiftPoint_street (l : PortLayout) (p : Scales.Parameters)
    (ss : List Segment) (rows : List ℕ) (x y : ℕ)
    (hx : x ∈ streetColumns l (coordinates p)) :
    shiftPoint (guardColumns l (coordinates p) ss) rows (point x y) = point x y := by
  have hg := guard_not_street l p ss hx
  simp [shiftPoint, point, segment, hg]

private theorem shiftPoint_short (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (e : Endpoint) (he : e ∈ l.endpoints) (ss : List Segment) (rows : List ℕ) (y : ℕ) :
    shiftPoint (guardColumns l (coordinates p) ss) rows
      (point (inward ((coordinates p).x e.port) e.inward 1) y) =
      point (inward ((coordinates p).x e.port) e.inward 1) y := by
  have hnear : Nat.dist (inward ((coordinates p).x e.port) e.inward 1) (p.x e.port) ≤ 1 := by
    have hc : (coordinates p).x e.port = p.x e.port := rfl
    cases e.inward <;> simp only [inward, hc, Bool.false_eq_true, ite_false, ite_true]
    all_goals simp only [Nat.dist]; omega
  have hn : inward ((coordinates p).x e.port) e.inward 1 ∉ guardColumns l (coordinates p) ss := by
    intro hg
    have hf := guard_axis_far l p ss hg (l.endpoints_port_lt hl he)
    omega
  simp [shiftPoint, point, segment, hn]

private theorem endpoint_fixed_shift (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (e : Endpoint)
    (he : e ∈ l.endpoints) (ss : List Segment) (rows : List ℕ) {s : Segment}
    (hs : s ∈ endpointFixedSegments l (coordinates p) e) :
    shiftPoint (guardColumns l (coordinates p) ss) rows s = s := by
  have hc := auxiliary_even p e
  have hm := midpoint_even p e
  have hstreet (x : ℕ) (hx : x ∈ [(auxiliary (coordinates p) e).1, (auxiliary (coordinates p) e).2]) :
      x ∈ streetColumns l (coordinates p) :=
    List.mem_append_right _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨e, he, hx⟩))
  obtain ⟨hj, hlev⟩ := l.endpoints_level_bounds p hl hM he
  have hL := readLength_ge p hj hlev
  change 16384 ≤ (coordinates p).length e.level at hL
  dsimp only [endpointFixedSegments] at hs
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hs
  rcases hs with rfl | rfl | rfl | hs | hs
  · apply shiftPoint_even
    simpa only [segment, Nat.min_self] using hc.1
  · apply shiftPoint_even
    simpa only [segment, Nat.min_self] using hc.2
  · apply shiftPoint_horizontal
    have hx : (coordinates p).length e.level + 64 < (coordinates p).x e.port :=
      readLength_add_lt_x p e.port e.level
    intro heq
    cases hi : e.inward <;> simp only [auxiliary, inward, outward,
      hi, Bool.false_eq_true, ite_false, ite_true] at heq <;> omega
  · obtain ⟨v, _, hs⟩ := List.mem_flatMap.mp hs
    rcases List.mem_append.mp hs with hs | hs
    · split at hs
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        subst s
        apply shiftPoint_even
        simpa only [point, segment, Nat.min_self] using hm
      · cases hs
    · split at hs
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        subst s
        exact shiftPoint_short l p hl e he ss rows _
      · cases hs
  · split at hs
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl <;>
        exact shiftPoint_street l p ss rows _ _ (hstreet _ (by simp))
    · cases hs

/-- Every original fixed piece of an actual endpoint survives the complete marked emitter. -/
theorem endpointFixedSegments_mem_fixed (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (e : Endpoint)
    (he : e ∈ l.endpoints) {s : Segment} (hs : s ∈ endpointFixedSegments l (coordinates p) e) :
    s ∈ l.fixedSegments p := by
  have hb : s ∈ interiorFixed l (coordinates p) := by
    unfold interiorFixed
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_flatMap.mpr ⟨e, he, hs⟩
  unfold fixedSegments
  apply List.mem_append_right
  unfold markedInterior
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_left
  split
  · exact List.mem_map.mpr ⟨s, hb, endpoint_fixed_shift l p hl hM e he _ _ hs⟩
  · exact hb

private theorem gate_fixed_shift (l : PortLayout) (p : Scales.Parameters) (i : ℕ)
    (ss : List Segment) (rows : List ℕ) {s : Segment}
    (hs : s ∈ gateFixedSegments (coordinates p) i) :
    shiftPoint (guardColumns l (coordinates p) ss) rows s = s := by
  have hx : (coordinates p).x i % 2 = 0 := x_even p i
  have hc (x : ℕ) (h : x ∈ specialColumns (coordinates p) i) : x % 2 = 0 :=
    specialColumns_even p i h
  dsimp only [gateFixedSegments] at hs
  simp only [List.mem_append, or_assoc] at hs
  rcases hs with hs | hs | hs
  · obtain ⟨x, hx', rfl⟩ := List.mem_map.mp hs
    apply shiftPoint_even
    have he : x % 2 = 0 := hc x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx'
      rcases hx' with rfl | rfl | rfl | rfl <;> simp [specialColumns])
    simpa only [segment, Nat.min_self] using he
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · apply shiftPoint_even
      simp only [point, segment, Nat.min_self]
      omega
    · exact shiftPoint_horizontal _ _ _ _ _ (by omega)
    · apply shiftPoint_even
      simpa only [point, segment, Nat.min_self] using hx
    · apply shiftPoint_even
      simp only [point, segment, Nat.min_self]
      omega
  · split at hs
    · obtain ⟨x, hx', rfl⟩ := List.mem_map.mp hs
      apply shiftPoint_even
      simpa only [point, segment, Nat.min_self] using hc x hx'
    · cases hs

private def roundedPiece (l : PortLayout) (p : Scales.Parameters) (s : Segment) : Segment :=
  let c := coordinates p
  let guards := guardColumns l c (frame c ++ interiorFixed l c)
  if guards.any (fun x => guards.contains (x + 1)) then shiftPoint guards (streetRows c) s else s

private theorem rounded_endpoint (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (e : Endpoint)
    (he : e ∈ l.endpoints) {s : Segment} (hs : s ∈ endpointFixedSegments l (coordinates p) e) :
    roundedPiece l p s = s := by
  dsimp only [roundedPiece]
  split
  · exact endpoint_fixed_shift l p hl hM e he _ _ hs
  · rfl

private theorem rounded_gate (l : PortLayout) (p : Scales.Parameters) (i : ℕ) {s : Segment}
    (hs : s ∈ gateFixedSegments (coordinates p) i) : roundedPiece l p s = s := by
  dsimp only [roundedPiece]
  split
  · exact gate_fixed_shift l p i _ _ hs
  · rfl

private theorem rounded_auxiliary (l : PortLayout) (p : Scales.Parameters) {x : ℕ}
    (hx : x ∈ originalAuxiliary l (coordinates p)) :
    roundedPiece l p (point x p.D) = point x p.D := by
  have he : x % 2 = 0 := streetColumnCoordinates_even l p (List.mem_append_right _ hx)
  dsimp only [roundedPiece]
  split
  · apply shiftPoint_even
    simpa only [point, segment, Nat.min_self] using he
  · rfl

private theorem rounded_wide_mem (l : PortLayout) (p : Scales.Parameters) (side : Side)
    {s : Segment} (hs : s ∈ wideFixed l (coordinates p) side) :
    roundedPiece l p s ∈ physicalWideSegments l p side := by
  dsimp only [physicalWideSegments, roundedPiece]
  split
  · exact List.mem_map.mpr ⟨s, hs, rfl⟩
  · exact hs

private theorem roundedInterior_eq (l : PortLayout) (p : Scales.Parameters) :
    (let c := coordinates p
     let guards := guardColumns l c (frame c ++ interiorFixed l c)
     if guards.any (fun x => guards.contains (x + 1)) then
       (interiorFixed l c).map (shiftPoint guards (streetRows c)) else interiorFixed l c) =
      (interiorFixed l (coordinates p)).map (roundedPiece l p) := by
  dsimp only [roundedPiece]
  split <;> rename_i h
  · apply List.map_congr_left
    intro s _
    dsimp only [roundedPiece]
    rw [ite_eq_left h]
  · symm
    apply List.map_id''
    intro s
    dsimp only [roundedPiece]
    rw [ite_eq_right h]

private def EndpointSources (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    (q : ℕ × ℕ) : Prop :=
  (∃ e ∈ l.endpoints, q ∈ pointHoles (endpointFixedSegments l (coordinates p) e) ∨
    q ∈ pointHoles (endpointSegments (coordinates p) state e)) ∨
  ∃ kind first, .gate kind first ∈ l.lowerGroups ∧
    (q ∈ pointHoles (gateFixedSegments (coordinates p) (first + 1)) ∨
      ∃ internal, q ∈ pointHoles (gateSegments (coordinates p) state kind first internal))

private theorem roundedInterior_sources (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (state : SignalState)
    {s : Segment} (hs : s ∈ interiorFixed l (coordinates p))
    {q : Cell (p.W + 1) (p.H + 1)} (hq : (roundedPiece l p s).Contains (q.1.val, q.2.val)) :
    q ∈ l.wideSeparatorHoles p ∨ EndpointSources l p state (q.1.val, q.2.val) ∨ q.2.val = p.D := by
  simp only [interiorFixed, List.mem_append, or_assoc] at hs
  rcases hs with hs | hs | hs | hs | hs
  · obtain ⟨e, he, hs⟩ := List.mem_flatMap.mp hs
    rw [rounded_endpoint l p hl hM e he hs] at hq
    exact Or.inr (Or.inl (Or.inl ⟨e, he, Or.inl ((mem_pointHoles _ _).mpr ⟨s, hs, hq⟩)⟩))
  · obtain ⟨i, hi, hs⟩ := List.mem_flatMap.mp hs
    obtain ⟨kind, first, hg, rfl⟩ := center_gate_mem l hi
    rw [rounded_gate l p (first + 1) hs] at hq
    exact Or.inr (Or.inl (Or.inr ⟨kind, first, hg,
      Or.inl ((mem_pointHoles _ _).mpr ⟨s, hs, hq⟩)⟩))
  · left
    apply (SegmentRecipe.mem_holes _ q).mpr
    exact ⟨_, List.mem_append_left _ (rounded_wide_mem l p .upper hs), hq⟩
  · left
    apply (SegmentRecipe.mem_holes _ q).mpr
    exact ⟨_, List.mem_append_right _ (rounded_wide_mem l p .lower hs), hq⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hs
    change (roundedPiece l p (point x p.D)).Contains (q.1.val, q.2.val) at hq
    rw [rounded_auxiliary l p hx] at hq
    exact Or.inr (Or.inr (point_coordinates hq).2)

private theorem marked_sources (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (state : SignalState)
    {s : Segment} (hs : s ∈ markedInterior l (coordinates p))
    {q : Cell (p.W + 1) (p.H + 1)} (hq : s.Contains (q.1.val, q.2.val)) (hf : q ∉ Boundary.frame) :
    q ∈ l.centralMarkers p ∨ q ∈ l.wideSeparatorHoles p ∨ EndpointSources l p state (q.1.val, q.2.val) := by
  have hfixed : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.fixedSegments p) :=
    (SegmentRecipe.mem_holes _ q).mpr ⟨s, List.mem_append_right _ hs, hq⟩
  have hcentral (hy : p.D ≤ q.2.val + 4 ∧ q.2.val ≤ p.D + 4) : q ∈ l.centralMarkers p :=
    Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hfixed, hf⟩, hy⟩
  dsimp only [markedInterior] at hs
  simp only [List.mem_append, or_assoc] at hs
  rcases hs with hs | hs | hs | hs
  · rw [roundedInterior_eq l p] at hs
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hs
    rcases roundedInterior_sources l p hl hM state hu hq with hw | hs | hy
    · exact Or.inr (Or.inl hw)
    · exact Or.inr (Or.inr hs)
    · exact Or.inl (hcentral (by rw [hy]; omega))
  · obtain ⟨x, _, hs⟩ := List.mem_flatMap.mp hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    all_goals
      have hp := (point_coordinates hq).2
      apply Or.inl (hcentral ?_)
      dsimp only [coordinates] at hp
      omega
  · obtain ⟨x, _, rfl⟩ := List.mem_map.mp hs
    have hp := (point_coordinates hq).2
    apply Or.inl (hcentral ?_)
    dsimp only [coordinates] at hp
    omega
  · obtain ⟨i, _, hs⟩ := List.mem_flatMap.mp hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    all_goals
      have hp := (point_coordinates hq).2
      apply Or.inl (hcentral ?_)
      dsimp only [coordinates] at hp
      omega

private theorem signal_sources (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    {q : ℕ × ℕ} (hq : q ∈ pointHoles (l.signalSegments p state)) : EndpointSources l p state q := by
  obtain ⟨s, hs, hq⟩ := (mem_pointHoles _ q).mp hq
  rcases List.mem_append.mp hs with hs | hs
  · obtain ⟨e, he, hs⟩ := List.mem_flatMap.mp hs
    exact Or.inl ⟨e, he, Or.inr ((mem_pointHoles _ q).mpr ⟨s, hs, hq⟩)⟩
  · obtain ⟨g, hg, hs⟩ := List.mem_flatMap.mp hs
    cases hk : g.gate with
    | none => simp [tripleSignal, hk] at hs
    | some kind =>
      have hgate := placement_gate_mem l hg hk
      exact Or.inr ⟨kind, g.left, hgate,
        Or.inr ⟨g.internal, (mem_pointHoles _ q).mpr ⟨s,
          by simpa only [tripleSignal, hk, Option.elim_some] using hs, hq⟩⟩⟩

private theorem encoded_sources (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (state : SignalState)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state))
    (hf : q ∉ Boundary.frame) :
    q ∈ l.centralMarkers p ∨ q ∈ l.wideSeparatorHoles p ∨ EndpointSources l p state (q.1.val, q.2.val) := by
  obtain ⟨s, hs, hq⟩ := (SegmentRecipe.mem_holes _ q).mp hq
  rcases List.mem_append.mp hs with hs | hs
  · rcases List.mem_append.mp hs with hs | hs
    · have hframe : q ∈ Boundary.frame := by
        simp only [frame, List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl | rfl | rfl
        · apply (Boundary.mem_frame q).mpr
          refine ⟨.north, ?_⟩
          simpa only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and] using
            (horizontal_coordinates hq).1
        · apply (Boundary.mem_frame q).mpr
          refine ⟨.south, ?_⟩
          have he : q.2.val = p.H := (horizontal_coordinates hq).1
          simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and, he]
        · apply (Boundary.mem_frame q).mpr
          refine ⟨.west, ?_⟩
          simpa only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and] using
            (vertical_coordinates hq).1
        · apply (Boundary.mem_frame q).mpr
          refine ⟨.east, ?_⟩
          have he : q.1.val = p.W := (vertical_coordinates hq).1
          simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and, he]
      exact False.elim (hf hframe)
    · exact marked_sources l p hl hM state hs hq hf
  · exact Or.inr (Or.inr (signal_sources l p state ((mem_pointHoles _ _).mpr ⟨s, hs, hq⟩)))

private theorem window_page (p : Scales.Parameters) (e : Endpoint)
    {q : Cell (p.W + 1) (p.H + 1)} (hw : q ∈ endpointWindow p e) :
    if e.side = .upper then q.2.val + 32 < p.D else p.D + 32 < q.2.val := by
  have hr := hw.1
  have hd := readDepth_add_lt_D p e.level
  have hH : p.H = 2 * p.D := rfl
  by_cases hs : e.side = .upper <;> simp only [hs, ite_true, ite_false] at hr ⊢ <;> omega

/-- The complete local endpoint rectangle avoids every central marker. -/
theorem endpointWindow_not_central (l : PortLayout) (p : Scales.Parameters) (e : Endpoint)
    {q : Cell (p.W + 1) (p.H + 1)} (hw : q ∈ endpointWindow p e) : q ∉ l.centralMarkers p := by
  intro hc
  have hy := (Finset.mem_filter.mp hc).2
  have hp := window_page p e hw
  split at hp <;> omega

/-- The local endpoint rectangle lies strictly inside the physical frame. -/
theorem endpointWindow_not_frame (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (ha : l.portCount ≤ p.axes) (e : Endpoint) (he : e ∈ l.endpoints)
    {q : Cell (p.W + 1) (p.H + 1)} (hw : q ∈ endpointWindow p e) : q ∉ Boundary.frame := by
  have hx0 := readLength_add_lt_x p e.port e.level
  have hxW := x_add_readLength_lt_W p (show e.port < p.axes by
    have := l.endpoints_port_lt hl he; omega) e.level
  have hdist := hw.2
  simp only [Nat.dist] at hdist
  have hy := hw.1
  have hp := window_page p e hw
  have hH : p.H = 2 * p.D := rfl
  have hD := readDepth_add_lt_D p e.level
  intro hf
  obtain ⟨d, hd⟩ := (Boundary.mem_frame q).mp hf
  cases d <;> simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and] at hd
  · split at hy <;> omega
  · omega
  · split at hy <;> omega
  · omega

private theorem window_axis_eq (p : Scales.Parameters) (e : Endpoint)
    {q : Cell (p.W + 1) (p.H + 1)} (hw : q ∈ endpointWindow p e) (i : ℕ)
    (hi : Nat.dist q.1.val (p.x i) ≤ p.L p.levels + 12) : i = e.port := by
  have he := hw.2
  have hL := readLength_le_last p e.level
  have hD := p.outer_distance
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hgap := axis_spacing p h
    simp only [Nat.dist] at he hi
    omega
  · have hgap := axis_spacing p h
    simp only [Nat.dist] at he hi
    omega

private theorem local_radius_budget (p : Scales.Parameters) (j : ℕ) :
    readLength p j + 16 < 2 * p.b p.levels + 2 := by
  have hL := readLength_le_last p j
  have hY := p.Y_ge p.levels
  have hm := Nat.mul_le_mul_right (p.Y p.levels + p.L p.levels + 10)
    (show 1 ≤ 8 * (p.axes + 1) by omega)
  simp only [Nat.one_mul] at hm
  unfold Scales.Parameters.b
  omega

/-- No actual wide separator lies in a local endpoint rectangle. -/
theorem endpointWindow_not_wide (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (ha : l.portCount ≤ p.axes) (e : Endpoint) (he : e ∈ l.endpoints)
    {q : Cell (p.W + 1) (p.H + 1)} (hw : q ∈ endpointWindow p e) : q ∉ l.wideSeparatorHoles p := by
  have hi := l.endpoints_port_lt hl he
  have hm := x_add_readLength_lt_W p (show e.port < p.axes by omega) 0
  let x : Fin (p.W + 1) := ⟨p.x e.port, by omega⟩
  have hx : x ∈ l.streetColumnSet p := axis_in_streetColumns l p hi
  intro hwide
  have hfar := l.wideSeparatorHoles_street_gap p hl hwide x hx
  have hb := local_radius_budget p e.level
  have hnear := hw.2
  change 2 * p.b p.levels + 2 < Nat.dist q.1.val (p.x e.port) at hfar
  omega

private theorem endpoint_source_near (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    (f : Endpoint) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles (endpointFixedSegments l (coordinates p) f) ∨
      q ∈ pointHoles (endpointSegments (coordinates p) state f)) :
    Nat.dist q.1 (p.x f.port) ≤ p.L p.levels + 12 := by
  have hL := readLength_le_last p f.level
  rcases hq with hq | hq
  · have hs := fixed_endpoint_span l p f hq
    simp only [Nat.dist]
    omega
  · have hs := (endpoint_near p state f hq).1
    have hc : (coordinates p).x f.port = p.x f.port := rfl
    cases hi : f.inward <;> simp only [hi, Bool.false_eq_true, ite_false, ite_true, hc] at hs <;>
      simp only [Nat.dist] <;> omega

private theorem window_endpoint_owner (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (state : SignalState) (e f : Endpoint) (he : e ∈ l.endpoints) (hf : f ∈ l.endpoints)
    {q : Cell (p.W + 1) (p.H + 1)} (hw : q ∈ endpointWindow p e)
    (hq : (q.1.val, q.2.val) ∈ pointHoles (endpointFixedSegments l (coordinates p) f) ∨
      (q.1.val, q.2.val) ∈ pointHoles (endpointSegments (coordinates p) state f)) : f = e := by
  have hport := window_axis_eq p e hw f.port (endpoint_source_near l p state f hq)
  have hside : f.side = e.side := by
    by_contra hne
    have hp := window_page p e hw
    have hfpage : if f.side = .upper then q.2.val + 32 < p.D else p.D + 32 < q.2.val :=
      hq.elim (fixed_endpoint_page l p f) (signal_endpoint_page p state f)
    cases hes : e.side <;> cases hfs : f.side <;>
      simp_all only [reduceCtorEq, ite_true, ite_false] <;> omega
  exact l.endpoints_key_injective hl hf he hside hport

private theorem window_not_gate (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (state : SignalState) (e : Endpoint) (he : e ∈ l.endpoints)
    {kind : Shuttle.Kind} {first : ℕ} (hg : .gate kind first ∈ l.lowerGroups)
    {q : Cell (p.W + 1) (p.H + 1)} (hw : q ∈ endpointWindow p e)
    (hq : (q.1.val, q.2.val) ∈ pointHoles (gateFixedSegments (coordinates p) (first + 1)) ∨
      ∃ internal, (q.1.val, q.2.val) ∈ pointHoles (gateSegments (coordinates p) state kind first internal)) : False := by
  have hs : p.x (first + 1) - 2 ≤ q.1.val ∧ q.1.val ≤ p.x (first + 1) + 12 := by
    rcases hq with h | ⟨internal, h⟩
    · exact gate_fixed_span p _ h
    · exact gate_signal_span p state kind first internal h
  have hp : p.D + 32 < q.2.val := by
    rcases hq with h | ⟨internal, h⟩
    · exact gate_fixed_page p _ h
    · exact gate_signal_page p state kind first internal h
  have hport : first + 1 = e.port := window_axis_eq p e hw (first + 1) (by
    simp only [Nat.dist]
    omega)
  cases hes : e.side with
  | upper =>
    have hepage := window_page p e hw
    simp only [hes, ite_true] at hepage
    omega
  | lower => exact l.endpoints_lower_ne_gate_middle hl hg he hes hport.symm

private theorem endpoint_holes_subset_encoded (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (state : SignalState)
    (e : Endpoint) (he : e ∈ l.endpoints) :
    SegmentRecipe.holes (p.W + 1) (p.H + 1)
        (endpointFixedSegments l (coordinates p) e ++ endpointSegments (coordinates p) state e) ⊆
      SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) := by
  intro q hq
  obtain ⟨s, hs, hq⟩ := (SegmentRecipe.mem_holes _ q).mp hq
  apply (SegmentRecipe.mem_holes _ q).mpr
  rcases List.mem_append.mp hs with hfixed | hsignal
  · exact ⟨s, List.mem_append_left _ (l.endpointFixedSegments_mem_fixed p hl hM e he hfixed), hq⟩
  · have hs : s ∈ l.signalSegments p state :=
      List.mem_append_left _ (List.mem_flatMap.mpr ⟨e, he, hsignal⟩)
    exact ⟨s, List.mem_append_right _ hs, hq⟩

/-- Inside an actual endpoint window, the complete marked encoding has precisely this
endpoint's original fixed and signal holes. -/
theorem encodedSegments_endpointWindow (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) (e : Endpoint) (he : e ∈ l.endpoints)
    (q : Cell (p.W + 1) (p.H + 1)) (hw : q ∈ endpointWindow p e) :
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) ↔
      q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1)
        (endpointFixedSegments l (coordinates p) e ++ endpointSegments (coordinates p) state e) := by
  constructor
  · intro hq
    rcases encoded_sources l p hl hM state hq (l.endpointWindow_not_frame p hl ha e he hw) with
      hcentral | hwide | hsource
    · exact False.elim (l.endpointWindow_not_central p e hw hcentral)
    · exact False.elim (l.endpointWindow_not_wide p hl ha e he hw hwide)
    · rcases hsource with ⟨f, hf, hsource⟩ | ⟨kind, first, hg, hsource⟩
      · have hfe := window_endpoint_owner l p hl state e f he hf hw hsource
        subst f
        apply (SegmentRecipe.mem_holes _ q).mpr
        rcases hsource with hfixed | hsignal
        · obtain ⟨s, hs, hq⟩ := (mem_pointHoles _ _).mp hfixed
          exact ⟨s, List.mem_append_left _ hs, hq⟩
        · obtain ⟨s, hs, hq⟩ := (mem_pointHoles _ _).mp hsignal
          exact ⟨s, List.mem_append_right _ hs, hq⟩
      · exact False.elim (window_not_gate l p hl state e he hg hw hsource)
  · intro hq
    exact endpoint_holes_subset_encoded l p hl hM state e he hq

/-- The frame-side cell immediately before the common pocket is occupied in every
actual encoding. -/
theorem endpoint_sealed_not_hole (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) (e : Endpoint) (he : e ∈ l.endpoints)
    (q : Cell (p.W + 1) (p.H + 1)) (hx : q.1.val = p.x e.port)
    (hy : q.2.val = if e.side = .upper then readDepth p e.level - 1
      else p.H - (readDepth p e.level - 1)) :
    q ∉ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) := by
  obtain ⟨hj, hm⟩ := l.endpoints_level_bounds p hl hM he
  have hlo := readDepth_ge p hj hm
  have hhi := readDepth_add_lt_H p e.level
  have hw : q ∈ endpointWindow p e := by
    simp only [endpointWindow, Set.mem_ofPred_eq, hx, Nat.dist_self]
    cases hs : e.side <;> simp only [hs, reduceCtorEq, ite_true, ite_false] at hy ⊢ <;> omega
  rw [l.encodedSegments_endpointWindow p hl hM ha state e he q hw]
  intro hq
  obtain ⟨s, hs, hq⟩ := (SegmentRecipe.mem_holes _ q).mp hq
  rcases List.mem_append.mp hs with hs | hs
  · exact own_fixed_off_axis l p hl hM he ((mem_pointHoles _ _).mpr ⟨s, hs, hq⟩) hx
  · have hbit := Bool.toNat_le (if e.side = .upper then state.axes.getD e.port false
      else !(state.axes.getD e.port false))
    have hd : (coordinates p).depth e.level = readDepth p e.level := rfl
    have hH : (coordinates p).H = p.H := rfl
    dsimp only [endpointSegments] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · have hv := vertical_coordinates hq
      cases hside : e.side <;>
        simp only [onSide, hside, reduceCtorEq, ite_true, ite_false, hd, hH] at hv hy hbit <;>
        omega
    · have hh := (horizontal_coordinates hq).1
      cases hside : e.side <;>
        simp only [onSide, hside, reduceCtorEq, ite_true, ite_false, hd, hH] at hh hy <;> omega

/-- The two axis holes and the first inward hole form the common L-shaped pocket,
independently of both signal bits. -/
theorem endpointPocket_mem_holes (l : PortLayout) (p : Scales.Parameters)
    (state : SignalState) (e : Endpoint) (he : e ∈ l.endpoints)
    (q : Cell (p.W + 1) (p.H + 1))
    (hpos : (q.1.val = p.x e.port ∧
        (q.2.val = (if e.side = .upper then readDepth p e.level else p.H - readDepth p e.level) ∨
        q.2.val = (if e.side = .upper then readDepth p e.level + 1
          else p.H - (readDepth p e.level + 1)))) ∨
      (q.1.val = (if e.inward then p.x e.port + 1 else p.x e.port - 1) ∧
        q.2.val = (if e.side = .upper then readDepth p e.level else p.H - readDepth p e.level))) :
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) := by
  have hown : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1)
      (endpointSegments (coordinates p) state e) := by
    have hd : (coordinates p).depth e.level = readDepth p e.level := rfl
    have hH : (coordinates p).H = p.H := rfl
    have hx' : (coordinates p).x e.port = p.x e.port := rfl
    apply (SegmentRecipe.mem_holes _ q).mpr
    rcases hpos with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · refine ⟨_, List.mem_cons_self, ?_⟩
      apply Or.inl
      simp only [segment, onSide, hd, hH, hx']
      cases hs : e.side <;> simp only [hs, reduceCtorEq, ite_true, ite_false] at hy ⊢ <;> omega
    · refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
      apply Or.inr
      simp only [segment, onSide, inward, hd, hH, hx']
      cases hd : e.inward <;> cases hs : e.side <;>
        simp only [hd, hs, Bool.false_eq_true, ite_true, ite_false, reduceCtorEq] at hx hy ⊢ <;> omega
  obtain ⟨s, hs, hq⟩ := (SegmentRecipe.mem_holes _ q).mp hown
  apply (SegmentRecipe.mem_holes _ q).mpr
  have hs : s ∈ l.signalSegments p state :=
    List.mem_append_left _ (List.mem_flatMap.mpr ⟨e, he, hs⟩)
  exact ⟨s, List.mem_append_right _ hs, hq⟩

end PushPuzzle.PushS.PortLayout
