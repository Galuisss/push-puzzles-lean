/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessCentralFlanks
public import PushS.PortGatePageWindow
import all PushS.PortCentralStrip
import all PushS.PortEndpointLocality
import all PushS.PortSegments
import all PushS.PortFixedSeparation
import all Push.AcceptanceProgramLayout

/-! Literal emitter origins of the far guard and short-train sample markers. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushFS.Reduction PushS PushS.PortLayout SegmentRecipe AcceptanceProgram

private def NearSegments (p : Scales.Parameters) (ss : List Segment) : Prop :=
  ∀ s ∈ ss, ∀ q, s.Contains q → q.2 ≤ p.Y p.levels + 2 ∨ p.H ≤ q.2 + p.Y p.levels + 2

private theorem near_side (p : Scales.Parameters) (side : Side) {x u y v : ℕ}
    (hy : y ≤ p.Y p.levels + 2) (hv : v ≤ p.Y p.levels + 2) :
    ∀ q, (segment x (onSide (coordinates p) side y) u (onSide (coordinates p) side v)).Contains q →
      q.2 ≤ p.Y p.levels + 2 ∨ p.H ≤ q.2 + p.Y p.levels + 2 := by
  intro q hq
  have hH : p.H = 2 * p.D := rfl
  cases side <;> simp only [PortLayout.segment, Segment.Contains, onSide, coordinates, ite_true,
    reduceCtorEq, ite_false] at hq
  all_goals omega

private theorem near_append (p : Scales.Parameters) {ss tt : List Segment}
    (hs : NearSegments p ss) (ht : NearSegments p tt) : NearSegments p (ss ++ tt) := by
  intro s h
  exact (List.mem_append.mp h).elim (hs s) (ht s)

private theorem near_flatMap (p : Scales.Parameters) {α : Type} {xs : List α}
    {f : α → List Segment} (h : ∀ x ∈ xs, NearSegments p (f x)) : NearSegments p (xs.flatMap f) := by
  intro s hs
  obtain ⟨x, hx, hs⟩ := List.mem_flatMap.mp hs
  exact h x hx s hs

private theorem endpoint_near (l : PortLayout) (p : Scales.Parameters) (e : Endpoint) :
    NearSegments p (endpointFixedSegments l (coordinates p) e) := by
  have hy := readDepth_le_last p e.level
  have hn := readDepth_le_last p (e.level + 1)
  have hY := p.Y_ge p.levels
  change (coordinates p).depth e.level ≤ p.Y p.levels at hy
  change (coordinates p).depth (e.level + 1) ≤ p.Y p.levels at hn
  dsimp only [endpointFixedSegments]
  simp only [List.append_assoc]
  apply near_append p
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl <;> apply near_side p e.side <;> omega
  · apply near_append p
    · apply near_flatMap p
      intro y hrow
      have hb := workingRows_le_last l p hrow
      apply near_append p
      all_goals
        split
        · intro s hs
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
          subst s
          exact near_side p e.side hb hb
        · exact fun _ h => False.elim (List.not_mem_nil h)
    · split
      · intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl <;> apply near_side p e.side <;> omega
      · exact fun _ h => False.elim (List.not_mem_nil h)

private theorem gate_near (p : Scales.Parameters) (i : ℕ) :
    NearSegments p (gateFixedSegments (coordinates p) i) := by
  have hy := readDepth_le_last p 1
  have hn := readDepth_le_last p 2
  have hY := p.Y_ge p.levels
  change (coordinates p).depth 1 ≤ p.Y p.levels at hy
  change (coordinates p).depth 2 ≤ p.Y p.levels at hn
  dsimp only [gateFixedSegments]
  simp only [List.append_assoc]
  apply near_append p
  · intro s hs
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hs
    apply near_side p .lower <;> omega
  · apply near_append p
    · intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl <;> apply near_side p .lower <;> omega
    · split
      · intro s hs
        obtain ⟨x, _, rfl⟩ := List.mem_map.mp hs
        apply near_side p .lower <;> omega
      · exact fun _ h => False.elim (List.not_mem_nil h)

private theorem wide_near (l : PortLayout) (p : Scales.Parameters) (side : Side) :
    NearSegments p (wideFixed l (coordinates p) side) := by
  apply near_flatMap p
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
      exact near_side p side hb hb
  · exact fun _ h => False.elim (List.not_mem_nil h)


private theorem base_central_cut (l : PortLayout) (p : Scales.Parameters) {s : Segment}
    (hs : s ∈ interiorFixed l (coordinates p)) {q : ℕ × ℕ} (hq : s.Contains q)
    (hy : p.D ≤ q.2 + 4) (hy' : q.2 ≤ p.D + 4) : q.2 = p.D := by
  have hD := last_depth_margin p
  have hH : p.H = 2 * p.D := rfl
  simp only [interiorFixed, List.mem_append, or_assoc] at hs
  rcases hs with hs | hs | hs | hs | hs
  · obtain ⟨e, _, he⟩ := List.mem_flatMap.mp hs
    have h := endpoint_near l p e s he q hq
    omega
  · obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp hs
    have h := gate_near p i s hi q hq
    omega
  · have h := wide_near l p .upper s hs q hq
    omega
  · have h := wide_near l p .lower s hs q hq
    omega
  · obtain ⟨x, _, rfl⟩ := List.mem_map.mp hs
    exact (point_coordinates hq).2

private theorem shifted_central_cut (l : PortLayout) (p : Scales.Parameters) (guards rows : List ℕ)
    {s : Segment} (hs : s ∈ interiorFixed l (coordinates p)) {q : ℕ × ℕ}
    (hq : (shiftPoint guards rows s).Contains q) (hy : p.D ≤ q.2 + 4) (hy' : q.2 ≤ p.D + 4) : q.2 = p.D := by
  unfold shiftPoint at hq
  split at hq
  · rename_i hcond
    have hrow := (point_coordinates hq).2
    have hself : s.Contains s.start := by
      right
      exact ⟨congrArg Prod.snd hcond.1, rfl, min_le_left _ _, le_max_left _ _⟩
    have h := base_central_cut l p hs hself (by omega) (by omega)
    omega
  · exact base_central_cut l p hs hq hy hy'

private theorem central_sources (l : PortLayout) (p : Scales.Parameters)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.centralMarkers p) :
    q.2.val = p.D ∨ q.2.val = p.D - 2 ∨ q.2.val = p.D + 2 ∨
      (q.2.val = p.D - 4 ∧ ∃ ss, q.1.val ∈ guardColumns l (coordinates p) ss) ∨
      (q.2.val = p.D + 4 ∧ ∃ i ∈ centers l, q.1.val = p.x i + 2 ∨ q.1.val = p.x i + 10) := by
  obtain ⟨hq, hy, hy'⟩ := Finset.mem_filter.mp hq
  obtain ⟨hq, hf⟩ := Finset.mem_sdiff.mp hq
  obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hq
  rcases List.mem_append.mp hs with hframe | hs
  · exact (hf (frame_contains (coordinates p) q ⟨s, hframe, hc⟩)).elim
  dsimp only [markedInterior] at hs
  simp only [List.mem_append, or_assoc] at hs
  rcases hs with hs | hs | hs | hs
  · left
    split at hs
    · obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hs
      exact shifted_central_cut l p _ _ hold hc hy hy'
    · exact base_central_cut l p hs hc hy hy'
  · obtain ⟨x, _, hs⟩ := List.mem_flatMap.mp hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact Or.inr (Or.inl (point_coordinates hc).2)
    · exact Or.inr (Or.inr (Or.inl (point_coordinates hc).2))
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hs
    obtain ⟨hx', hy'⟩ := point_coordinates hc
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hy', _, hx' ▸ hx⟩)))
  · obtain ⟨i, hi, hs⟩ := List.mem_flatMap.mp hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · obtain ⟨hx, hy⟩ := point_coordinates hc
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hy, i, hi, Or.inl hx⟩)))
    · obtain ⟨hx, hy⟩ := point_coordinates hc
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hy, i, hi, Or.inr hx⟩)))

private theorem guard_marker_off_street (l : PortLayout) (p : Scales.Parameters)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.centralMarkers p) (hy : q.2.val = p.D - 4) :
    q.1.val ∉ streetColumns l (coordinates p) := by
  have hD := p.outer_distance
  rcases central_sources l p hq with h | h | h | ⟨_, ss, hx⟩ | ⟨h, _⟩
  · omega
  · omega
  · omega
  · intro hstreet
    exact guard_not_street l p ss hstreet hx
  · omega

private theorem sample_marker_source (l : PortLayout) (p : Scales.Parameters)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.centralMarkers p) (hy : q.2.val = p.D + 4) :
    ∃ i ∈ centers l, q.1.val = p.x i + 2 ∨ q.1.val = p.x i + 10 := by
  have hD := p.outer_distance
  rcases central_sources l p hq with h | h | h | ⟨h, _⟩ | ⟨_, i, hi, hx⟩
  · omega
  · omega
  · omega
  · omega
  · exact ⟨i, hi, hx⟩

end PushPuzzle.Push.AcceptanceSoundness
