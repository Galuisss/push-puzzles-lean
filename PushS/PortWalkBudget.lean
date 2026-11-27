/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortHoleBudget
public import PushS.PortEndpointEnumeration
public import PushS.PortInventorySum
public import PushS.EndpointWalking
public import PushS.PortCentralMarkers
import all PushS.EndpointWalking
import all PushS.PortLayoutCoordinates
import all PushS.PortHoleBudget
import all PushS.PortInventorySum
import all PushS.PortSegments

/-! Actual endpoint and long-walk counts for the reader budgets. -/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS.Reduction

/-- The actual middle-port list of the emitted lower-page gates. -/
def gateCenterCoordinates (l : PortLayout) : List ℕ := centers l

/-- Every original port contributes at most one ordinary endpoint on each of its two pages. -/
theorem endpoints_length_le_twice (l : PortLayout) (hl : l.pages.Valid) :
    l.endpoints.length ≤ 2 * l.portCount := by
  let keys := l.endpoints.map fun e => (e.side, e.port)
  have hsub : keys.toFinset ⊆ (Finset.univ : Finset Side) ×ˢ Finset.range l.portCount := by
    intro key hk
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hk)
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_range.mpr (l.endpoints_port_lt hl he)⟩
  have hc := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup (l.endpoints_keys_nodup hl)] at hc
  have hside : Fintype.card Side = 2 := by decide
  simpa only [keys, List.length_map, Finset.card_product, Finset.card_univ,
    Finset.card_range, hside] using hc

/-- Actual f walks and long branches at this or deeper levels, and r walks at deeper levels. -/
def readerWalkSegments (l : PortLayout) (p : Scales.Parameters) (j : ℕ) : List Segment :=
  l.endpoints.flatMap fun e =>
    (((endpointFixedSegments l (coordinates p) e).take 3).zipIdx).filterMap fun (s, k) =>
      if (if k = 1 then j < e.level else j ≤ e.level) then some s else none

/-- The frame and the actual public walks removed from the reader's outside-hole budget. -/
@[expose] def readerWalkHoles (l : PortLayout) (p : Scales.Parameters) (j : ℕ) :
    Finset (PushFS.Cell (p.W + 1) (p.H + 1)) :=
  Boundary.frame ∪ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.readerWalkSegments p j)

private theorem endpoint_base_nonpoint (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) {e : Endpoint} (he : e ∈ l.endpoints) {s : Segment}
    (hs : s ∈ (endpointFixedSegments l (coordinates p) e).take 3) : s.start ≠ s.finish := by
  dsimp only [endpointFixedSegments] at hs
  simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
    List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact streetSegment_ne l p hl hM e he .f
  · exact streetSegment_ne l p hl hM e he .r
  · obtain ⟨hj, hm⟩ := l.endpoints_level_bounds p hl hM he
    have hL := readLength_ge p hj hm
    have hmargin := readLength_add_lt_x p e.port e.level
    change 16384 ≤ (coordinates p).length e.level at hL
    change (coordinates p).length e.level + 64 < (coordinates p).x e.port at hmargin
    intro h
    have hx := congrArg (fun q : ℕ × ℕ => q.1) h
    cases hd : e.inward <;> simp only [segment, auxiliary, inward, outward, hd,
      Bool.false_eq_true, ite_false, ite_true] at hx <;> omega

/-- Every selected public-walk segment is retained literally in the complete marked emitter. -/
theorem readerWalkSegments_subset_fixed (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (j : ℕ) :
    ∀ s ∈ l.readerWalkSegments p j, s ∈ l.fixedSegments p := by
  intro s hs
  obtain ⟨e, he, hs⟩ := List.mem_flatMap.mp hs
  obtain ⟨sk, hsk, hs⟩ := List.mem_filterMap.mp hs
  rcases sk with ⟨u, k⟩
  dsimp only at hs
  have heq : u = s := by
    split_ifs at hs <;> exact Option.some.inj hs
  subst s
  have hbase := List.fst_mem_of_mem_zipIdx hsk
  apply long_segment_mem_fixed l p _ (endpoint_base_nonpoint l p hl hM he hbase)
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_left
  exact List.mem_flatMap.mpr ⟨e, he, List.mem_of_mem_take hbase⟩

/-- The reader region is an actual hole subset of every complete physical encoding. -/
theorem readerWalkHoles_subset_encoded (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (j : ℕ) (state : SignalState) :
    l.readerWalkHoles p j ⊆
      SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) := by
  intro q hq
  rcases Finset.mem_union.mp hq with hf | hw
  · exact l.encodedSegments_frame_subset p state hf
  · obtain ⟨s, hs, hq⟩ := (SegmentRecipe.mem_holes _ q).mp hw
    exact (SegmentRecipe.mem_holes _ q).mpr
      ⟨s, List.mem_append_left _ (l.readerWalkSegments_subset_fixed p hl hM j s hs), hq⟩

/-- Lowering the reader level adds actual public-walk segments. -/
theorem readerWalkSegments_antitone (l : PortLayout) (p : Scales.Parameters) {i j : ℕ}
    (hij : i ≤ j) : ∀ s ∈ l.readerWalkSegments p j, s ∈ l.readerWalkSegments p i := by
  intro s hs
  obtain ⟨e, he, hs⟩ := List.mem_flatMap.mp hs
  obtain ⟨⟨u, k⟩, hsk, hs⟩ := List.mem_filterMap.mp hs
  dsimp only at hs
  have ht : if k = 1 then j < e.level else j ≤ e.level := by
    by_contra h
    rw [ite_eq_right h] at hs
    cases hs
  have hu : u = s := by rw [ite_eq_left ht] at hs; exact Option.some.inj hs
  have ht' : if k = 1 then i < e.level else i ≤ e.level := by
    by_cases hk : k = 1 <;> simp only [hk, ite_true, ite_false] at ht ⊢ <;> omega
  apply List.mem_flatMap.mpr
  refine ⟨e, he, List.mem_filterMap.mpr ⟨(u, k), hsk, ?_⟩⟩
  dsimp only
  rw [ite_eq_left ht', hu]

/-- The actual finite reader regions grow while the allocated levels are processed downwards. -/
theorem readerWalkHoles_antitone (l : PortLayout) (p : Scales.Parameters) {i j : ℕ} (hij : i ≤ j) :
    l.readerWalkHoles p j ⊆ l.readerWalkHoles p i := by
  intro q hq
  rcases Finset.mem_union.mp hq with hf | hw
  · exact Finset.mem_union_left _ hf
  · apply Finset.mem_union_right
    obtain ⟨s, hs, hq⟩ := (SegmentRecipe.mem_holes _ q).mp hw
    exact (SegmentRecipe.mem_holes _ q).mpr ⟨s, l.readerWalkSegments_antitone p hij s hs, hq⟩

/-- Every bounded raw depth lookup below a reader level stays below its geometric depth. -/
theorem readDepth_le_level (p : Scales.Parameters) {i j : ℕ} (hij : i ≤ j) : readDepth p i ≤ p.Y j := by
  by_cases hi : i = 0
  · simp [readDepth, depthTable, hi]
  · by_cases hm : i ≤ p.levels
    · rw [readDepth_eq p (by omega) hm]
      exact Y_le p hij
    · rw [readDepth_eq_zero p (by omega)]
      exact Nat.zero_le _

/-- Every bounded raw branch lookup below a reader level stays below its geometric length. -/
theorem readLength_le_level (p : Scales.Parameters) {i j : ℕ} (hij : i ≤ j) : readLength p i ≤ p.L j := by
  by_cases hi : i = 0
  · simp [readLength, lengthTable, hi]
  · by_cases hm : i ≤ p.levels
    · rw [readLength_eq p (by omega) hm]
      exact L_le p hij
    · rw [readLength_eq_zero p (by omega)]
      exact Nat.zero_le _

private theorem portList_length_bound (gs : List PageLevels.Group) :
    2 * gs.length ≤ (gs.flatMap portList).length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hg : 2 ≤ (portList g).length := by cases g <;> simp [portList]
    simp only [List.flatMap_cons, List.length_cons, List.length_append]
    omega

private theorem page_twice_length_le (page : PageLevels.Page) (hp : page.Valid) :
    2 * page.groups.length ≤ page.portCount := by
  have h := portList_length_bound page.groups
  have he := (page_ports_perm page hp).length_eq
  simp only [List.length_range] at he
  omega

/-- Actual lower gate centers consume at least two distinct ports each. -/
theorem gateCenters_length_twice_le (l : PortLayout) (hl : l.pages.Valid) :
    2 * (l.gateCenterCoordinates).length ≤ l.portCount := by
  change 2 * (centers l).length ≤ l.portCount
  have hc := List.length_filterMap_le (fun g => encLowerGroup_elim g
    (fun _ => none) (fun ka => some (ka.2 + 1))) l.lowerGroups
  have hp := page_twice_length_le l.pages.lowerPage hl.lower
  simp only [pages, PageLevels.Pages.lowerPage, List.length_map] at hp
  change (centers l).length ≤ l.lowerGroups.length at hc
  omega

private theorem endpoint_base_trace (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) {e : Endpoint} (he : e ∈ l.endpoints) :
    let ss := endpointFixedSegments l (coordinates p) e
    traceLength (ss.take 1) ≤ readDepth p e.level + 2 ∧
      traceLength ((ss.drop 1).take 1) ≤ readDepth p e.level + 2 ∧
      traceLength ((ss.drop 2).take 1) ≤ readLength p e.level := by
  let c := coordinates p
  obtain ⟨hj, hm⟩ := l.endpoints_level_bounds p hl hM he
  have hY : 16384 ≤ c.depth e.level := readDepth_ge p hj hm
  have hL : 16384 ≤ c.length e.level := readLength_ge p hj hm
  have hx : c.length e.level + 64 < c.x e.port := readLength_add_lt_x p e.port e.level
  have hy : c.depth e.level + 64 < c.H := readDepth_add_lt_H p e.level
  have h1 := segment_length_le (auxiliary c e).1 (onSide c e.side 1)
    (auxiliary c e).1 (onSide c e.side (c.depth e.level + 2))
  have h2 := segment_length_le (auxiliary c e).2 (onSide c e.side 1)
    (auxiliary c e).2 (onSide c e.side (c.depth e.level - 1))
  have h3 := segment_length_le (inward (auxiliary c e).1 e.inward 1)
    (onSide c e.side (c.depth e.level + 2)) (outward (c.x e.port) e.inward 1)
    (onSide c e.side (c.depth e.level + 2))
  dsimp only [endpointFixedSegments]
  simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
    List.drop_succ_cons, List.drop_zero, trace_cons, trace_nil, Nat.add_zero]
  change _ ≤ c.depth e.level + 2 ∧ _ ≤ c.depth e.level + 2 ∧ _ ≤ c.length e.level
  dsimp only [c] at *
  cases hs : e.side <;> cases hd : e.inward <;>
    simp only [auxiliary, outward, inward, onSide, hs, hd, reduceCtorEq,
      Bool.false_eq_true, ite_false, ite_true, Nat.dist] at h1 h2 h3 ⊢ <;> omega

/-- The actual unremoved f/r streets, shorter long branches, and four gate public streets. -/
def readerResidualSegments (l : PortLayout) (p : Scales.Parameters) (j : ℕ) : List Segment :=
  ((l.endpoints.filter fun e => decide (e.level < j)).flatMap fun e =>
    (endpointFixedSegments l (coordinates p) e).take 1) ++
  ((l.endpoints.filter fun e => decide (e.level ≤ j)).flatMap fun e =>
    ((endpointFixedSegments l (coordinates p) e).drop 1).take 1) ++
  ((l.endpoints.filter fun e => decide (e.level < j)).flatMap fun e =>
    ((endpointFixedSegments l (coordinates p) e).drop 2).take 1) ++
  (centers l).flatMap fun i => (gateFixedSegments (coordinates p) i).take 4

private theorem gate_public_trace (p : Scales.Parameters) (i : ℕ) :
    traceLength ((gateFixedSegments (coordinates p) i).take 4) ≤ 4 * (p.Y 1 + 2) := by
  let c := coordinates p
  have hY : c.depth 1 = p.Y 1 := readDepth_eq p le_rfl p.levels_pos
  have hH : c.depth 1 + 64 < c.H := readDepth_add_lt_H p 1
  have he (x : ℕ) :
      (segment x (onSide c .lower 1) x (onSide c .lower (c.depth 1 - 1))).cells.length ≤ p.Y 1 + 2 := by
    have h := segment_length_le x (onSide c .lower 1) x (onSide c .lower (c.depth 1 - 1))
    simp only [onSide, reduceCtorEq, ite_false, Nat.dist] at h ⊢
    omega
  dsimp only [gateFixedSegments]
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.take_succ_cons,
    List.take_zero, trace_cons, trace_nil]
  have h0 := he (c.x i - 2)
  have h1 := he (c.x i + 6)
  have h2 := he (c.x i + 8)
  have h3 := he (c.x i + 12)
  dsimp only [c] at *
  omega

private theorem endpoint_filtered_trace (l : PortLayout) (hl : l.pages.Valid)
    (pred : Endpoint → Bool) (f : Endpoint → List Segment) (k : ℕ)
    (h : ∀ e ∈ l.endpoints, pred e = true → traceLength (f e) ≤ k) :
    traceLength ((l.endpoints.filter pred).flatMap f) ≤ 2 * l.portCount * k := by
  have hb := trace_flatMap_le (l.endpoints.filter pred) f k (fun e he =>
    h e (List.mem_filter.mp he).1 (List.mem_filter.mp he).2)
  have hn := (List.length_filter_le pred l.endpoints).trans (l.endpoints_length_le_twice hl)
  exact hb.trans (Nat.mul_le_mul_right k hn)

private theorem reader_residual_trace_port_count (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) {j : ℕ} (hj : 1 ≤ j) :
    traceLength (l.readerResidualSegments p j) ≤
      4 * l.portCount * (p.Y j + 2) + 2 * l.portCount * p.L (j - 1) := by
  let f := (l.endpoints.filter fun e => decide (e.level < j)).flatMap fun e =>
    (endpointFixedSegments l (coordinates p) e).take 1
  let r := (l.endpoints.filter fun e => decide (e.level ≤ j)).flatMap fun e =>
    ((endpointFixedSegments l (coordinates p) e).drop 1).take 1
  let b := (l.endpoints.filter fun e => decide (e.level < j)).flatMap fun e =>
    ((endpointFixedSegments l (coordinates p) e).drop 2).take 1
  let g := (centers l).flatMap fun i => (gateFixedSegments (coordinates p) i).take 4
  have hf : traceLength f ≤ 2 * l.portCount * (p.Y (j - 1) + 2) := by
    apply endpoint_filtered_trace l hl
    intro e he hlev
    have he' : e.level ≤ j - 1 := by have := of_decide_eq_true hlev; omega
    have hb := (endpoint_base_trace l p hl hM he).1
    have hd := readDepth_le_level p he'
    omega
  have hr : traceLength r ≤ 2 * l.portCount * (p.Y j + 2) := by
    apply endpoint_filtered_trace l hl
    intro e he hlev
    have hb := (endpoint_base_trace l p hl hM he).2.1
    have hd := readDepth_le_level p (of_decide_eq_true hlev)
    omega
  have hb : traceLength b ≤ 2 * l.portCount * p.L (j - 1) := by
    apply endpoint_filtered_trace l hl
    intro e he hlev
    have he' : e.level ≤ j - 1 := by have := of_decide_eq_true hlev; omega
    have hb := (endpoint_base_trace l p hl hM he).2.2
    have hd := readLength_le_level p he'
    omega
  have hg : traceLength g ≤ 2 * l.portCount * (p.Y 1 + 2) := by
    have ht := trace_flatMap_le (centers l) (fun i => (gateFixedSegments (coordinates p) i).take 4)
      (4 * (p.Y 1 + 2)) (fun i _ => gate_public_trace p i)
    have hn := l.gateCenters_length_twice_le hl
    change 2 * (centers l).length ≤ l.portCount at hn
    have hm := Nat.mul_le_mul_right (2 * (p.Y 1 + 2)) hn
    dsimp only [g]
    nlinarith
  have heq : traceLength (l.readerResidualSegments p j) =
      traceLength f + traceLength r + traceLength b + traceLength g := by
    simp only [readerResidualSegments, trace_append, f, r, b, g]
  by_cases hj1 : j = 1
  · have he : (l.endpoints.filter fun e => decide (e.level < j)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro e he
      have hp := (l.endpoints_level_bounds p hl hM he).1
      simp only [decide_eq_true_eq]
      omega
    have hf0 : traceLength f = 0 := by simp only [f, he, List.flatMap_nil, trace_nil]
    rw [hj1] at hr hb heq ⊢
    simp only [Nat.sub_self, Scales.Parameters.L, ite_true] at hb ⊢
    nlinarith
  · have hy1 := Y_le p (show 1 ≤ j - 1 by omega)
    have hstep := p.Y_succ (j - 1) (by omega)
    rw [show j - 1 + 1 = j by omega] at hstep
    have hs : 2 ≤ p.S := by unfold Scales.Parameters.S; omega
    have hs2 : 4 ≤ p.S ^ 2 := by nlinarith
    have hmul := Nat.mul_le_mul_left (p.Y (j - 1)) hs2
    rw [← hstep] at hmul
    have hy0 := p.Y_ge (j - 1)
    have hwalk : (p.Y (j - 1) + 2) + (p.Y 1 + 2) ≤ p.Y j + 2 := by omega
    have hsum := Nat.mul_le_mul_left (2 * l.portCount) hwalk
    rw [heq]
    nlinarith

/-- The actual unremoved long segments fit the nonconstant part of the reader budget. -/
theorem readerResidualSegments_trace_length_le (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    {j : ℕ} (hj : 1 ≤ j) :
    ((l.readerResidualSegments p j).flatMap Segment.cells).length ≤
      4 * p.axes * (p.Y j + 2) + 2 * p.axes * p.L (j - 1) := by
  have hb := reader_residual_trace_port_count l p hl hM hj
  have hwalk := Nat.mul_le_mul_right (p.Y j + 2) (Nat.mul_le_mul_left 4 ha)
  have hbranch := Nat.mul_le_mul_right (p.L (j - 1)) (Nat.mul_le_mul_left 2 ha)
  change traceLength _ ≤ _
  omega

end PushPuzzle.PushS.PortLayout
