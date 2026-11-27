/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortWalkBudget
public import PushS.PortPageColumnCounts
import all PushS.PortWalkBudget
import all PushS.PortHoleBudget
import all PushS.PortPageColumnCounts
import all PushS.PortTwoPageStreets
import all PushS.PortSegments

/-! Actual small fixed-hole stock between the reader's public walks. -/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS.Reduction SegmentRecipe

private def baseSmallSegments (l : PortLayout) (p : Scales.Parameters) : List Segment :=
  l.endpoints.flatMap (fun e => (endpointFixedSegments l (coordinates p) e).drop 3) ++
  (centers l).flatMap (fun i => (gateFixedSegments (coordinates p) i).drop 4) ++
  wideFixed l (coordinates p) .upper ++ wideFixed l (coordinates p) .lower ++
  (originalAuxiliary l (coordinates p)).map (fun x => point x p.D)

private theorem endpoint_tail_points (l : PortLayout) (p : Scales.Parameters) (e : Endpoint)
    {s : Segment} (hs : s ∈ (endpointFixedSegments l (coordinates p) e).drop 3) :
    s.start = s.finish := by
  dsimp only [endpointFixedSegments] at hs
  simp only [List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero,
    List.mem_append] at hs
  rcases hs with hs | hs
  · obtain ⟨v, _, hs⟩ := List.mem_flatMap.mp hs
    rcases List.mem_append.mp hs with hs | hs
    all_goals split at hs
    all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    all_goals subst s; rfl
  · split at hs
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl <;> rfl
    · cases hs

private theorem endpoint_tail_trace (l : PortLayout) (p : Scales.Parameters) (e : Endpoint) :
    traceLength ((endpointFixedSegments l (coordinates p) e).drop 3) ≤ 6 * p.levels + 2 := by
  dsimp only [endpointFixedSegments]
  simp only [List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero, trace_append]
  calc
    _ ≤ (workingRows l (coordinates p)).length * 2 + 2 := by
      apply Nat.add_le_add
      · apply trace_flatMap_le
        intro v _
        split_ifs <;> simp
      · split <;> simp
    _ ≤ 6 * p.levels + 2 := by
      have hw := workingRows_length_le l (coordinates p)
      change (workingRows l (coordinates p)).length ≤ 3 * p.levels at hw
      omega

private theorem gate_tail_trace (p : Scales.Parameters) (i : ℕ) :
    traceLength ((gateFixedSegments (coordinates p) i).drop 4) ≤ 12 := by
  let c := coordinates p
  have hb := segment_length_le (c.x i + 1) (onSide c .lower (c.depth 1 + 2))
    (c.x i + 4) (onSide c .lower (c.depth 1 + 2))
  simp only [Nat.dist] at hb
  have hb' := hb.trans (show _ ≤ 4 by omega)
  have hm : traceLength (if 1 < c.levels then (specialColumns c i).map fun x =>
      point x (onSide c .lower ((c.depth 1 + c.depth 2) / 2)) else []) ≤ 5 := by
    split <;> simp [specialColumns]
  dsimp only [gateFixedSegments]
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.drop_succ_cons, List.drop_zero, trace_cons, point_length]
  change 1 + (_ + (1 + (1 + _))) ≤ 12
  dsimp only [c] at hb' hm
  omega

private theorem page_columns_total (l : PortLayout) (p : Scales.Parameters) :
    (l.pageColumnCoordinates p .upper).length + (l.pageColumnCoordinates p .lower).length =
      4 + 3 * l.endpoints.length + 6 * (centers l).length := by
  have he (side : Side) : ((l.endpoints.filter fun e => decide (e.side = side)).flatMap fun e =>
      let (f, r) := auxiliary (coordinates p) e
      [f, (coordinates p).x e.port, r]).length =
      (l.endpoints.filter fun e => decide (e.side = side)).length * 3 :=
    List.length_flatMap_of_forall_length_eq (fun _ _ => rfl)
  have hc : ((centers l).flatMap fun i => (coordinates p).x i :: specialColumns (coordinates p) i).length =
      (centers l).length * 6 := List.length_flatMap_of_forall_length_eq (fun _ _ => rfl)
  have hsplit (xs : List Endpoint) :
      (xs.filter fun e => decide (e.side = .upper)).length +
        (xs.filter fun e => decide (e.side = .lower)).length = xs.length := by
    induction xs with
    | nil => rfl
    | cons e xs ih => cases hs : e.side <;> simp [hs] <;> omega
  simp only [pageColumnCoordinates, pageColumns, List.length_append, he, hc,
    reduceCtorEq, ite_false, ite_true, List.length_nil, List.length_cons]
  have h := hsplit l.endpoints
  omega

private theorem wide_trace_linear (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (side : Side) :
    traceLength (wideFixed l (coordinates p) side) ≤
      3 * p.levels * (l.pageColumnCoordinates p side).length := by
  have hw := workingRows_length_le l (coordinates p)
  change (workingRows l (coordinates p)).length ≤ 3 * p.levels at hw
  have hp := l.pageAdjacentColumnPairs_length_le p hl hM ha side
  change (adjacentPairs (pageColumns l (coordinates p) side)).length ≤ _ at hp
  have ht : traceLength (wideFixed l (coordinates p) side) ≤
      (adjacentPairs (pageColumns l (coordinates p) side)).length * (3 * p.levels) := by
    apply trace_flatMap_le
    intro ab _
    dsimp only
    split
    · refine (trace_filterMap_le (workingRows l (coordinates p)) _ 1 ?_).trans ?_
      · intro v _ s hs
        split at hs
        · cases hs
        · cases hs; simp
      · simpa only [Nat.mul_one] using hw
    · simp
  have hm := Nat.mul_le_mul_right (3 * p.levels) hp
  exact (ht.trans hm).trans_eq (Nat.mul_comm _ _)

private theorem base_small_trace (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) :
    traceLength (baseSmallSegments l p) ≤
      39 * p.axes * p.levels + 17 * p.axes + 12 * p.levels := by
  have he := trace_flatMap_le l.endpoints
    (fun e => (endpointFixedSegments l (coordinates p) e).drop 3) (6 * p.levels + 2)
    (fun e _ => endpoint_tail_trace l p e)
  have hg := trace_flatMap_le (centers l)
    (fun i => (gateFixedSegments (coordinates p) i).drop 4) 12 (fun i _ => gate_tail_trace p i)
  have hu := wide_trace_linear l p hl hM ha .upper
  have hd := wide_trace_linear l p hl hM ha .lower
  have haux : traceLength ((originalAuxiliary l (coordinates p)).map fun x => point x p.D) =
      2 * l.endpoints.length + 5 * (centers l).length :=
    (trace_points _ (fun x => (x, p.D))).trans (auxiliary_length l (coordinates p))
  have hE : l.endpoints.length ≤ 2 * p.axes := (l.endpoints_length_le_twice hl).trans (by omega)
  have hC : 2 * (centers l).length ≤ p.axes := (l.gateCenters_length_twice_le hl).trans ha
  have hcols := page_columns_total l p
  have hslots := Nat.mul_le_mul_right (6 * p.levels + 2) hE
  have hcolslots := Nat.mul_le_mul_left (3 * p.levels) (show
      (l.pageColumnCoordinates p .upper).length + (l.pageColumnCoordinates p .lower).length ≤
        4 + 9 * p.axes by omega)
  simp only [baseSmallSegments, trace_append]
  nlinarith

private def pointTrace (ss : List Segment) : ℕ :=
  traceLength (ss.filter fun s => decide (s.start = s.finish))

private theorem pointTrace_append (ss tt : List Segment) :
    pointTrace (ss ++ tt) = pointTrace ss + pointTrace tt := by
  simp only [pointTrace, List.filter_append, trace_append]

private theorem pointTrace_le (ss : List Segment) : pointTrace ss ≤ traceLength ss := by
  induction ss with
  | nil => exact Nat.le_refl 0
  | cons s ss ih =>
    by_cases hs : s.start = s.finish <;>
      simp only [pointTrace, List.filter_cons, hs, decide_true, decide_false, Bool.false_eq_true, ite_true,
        ite_false, trace_cons] at ih ⊢ <;> omega

private theorem pointTrace_zero (ss : List Segment) (hn : ∀ s ∈ ss, s.start ≠ s.finish) :
    pointTrace ss = 0 := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    have hs := hn s List.mem_cons_self
    have ht := ih (fun t ht => hn t (List.mem_cons_of_mem _ ht))
    simpa only [pointTrace, List.filter_cons, hs, decide_false, Bool.false_eq_true, ite_false] using ht

private theorem pointTrace_drop_le (ss : List Segment) (k : ℕ)
    (hn : ∀ s ∈ ss.take k, s.start ≠ s.finish) : pointTrace ss ≤ traceLength (ss.drop k) := by
  have hz := pointTrace_zero (ss.take k) hn
  calc
    pointTrace ss = pointTrace (ss.take k ++ ss.drop k) := congrArg pointTrace (List.take_append_drop k ss).symm
    _ = pointTrace (ss.drop k) := by rw [pointTrace_append, hz, Nat.zero_add]
    _ ≤ traceLength (ss.drop k) := pointTrace_le _

private theorem pointTrace_flatMap_le {α : Type*} (xs : List α) (f g : α → List Segment)
    (h : ∀ a ∈ xs, pointTrace (f a) ≤ traceLength (g a)) :
    pointTrace (xs.flatMap f) ≤ traceLength (xs.flatMap g) := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons a xs ih =>
    have ha := h a List.mem_cons_self
    have ht := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
    simpa only [List.flatMap_cons, pointTrace_append, trace_append] using Nat.add_le_add ha ht

private theorem gate_base_nonpoint (p : Scales.Parameters) (i : ℕ) {s : Segment}
    (hs : s ∈ (gateFixedSegments (coordinates p) i).take 4) : s.start ≠ s.finish := by
  let c := coordinates p
  have hY : 16384 ≤ c.depth 1 := readDepth_ge p (by omega) p.levels_pos
  have hH : c.depth 1 + 64 < c.H := readDepth_add_lt_H p 1
  have hrow : onSide c .lower 1 ≠ onSide c .lower (c.depth 1 - 1) := by
    simp only [onSide, reduceCtorEq, ite_false]
    omega
  have hs' : s ∈ ([c.x i - 2, c.x i + 6, c.x i + 8, c.x i + 12].map fun col =>
      segment col (onSide c .lower 1) col (onSide c .lower (c.depth 1 - 1))) := by
    simpa only [gateFixedSegments, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, List.take_succ_cons, List.take_zero] using hs
  obtain ⟨col, _, rfl⟩ := List.mem_map.mp hs'
  intro heq
  have hy := congrArg Prod.snd heq
  dsimp only [segment] at hy
  omega

private theorem base_point_trace (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) :
    pointTrace (interiorFixed l (coordinates p)) ≤ traceLength (baseSmallSegments l p) := by
  have he := pointTrace_flatMap_le l.endpoints (endpointFixedSegments l (coordinates p))
    (fun e => (endpointFixedSegments l (coordinates p) e).drop 3)
    (fun e he => pointTrace_drop_le _ 3 (fun s hs => endpoint_base_nonpoint l p hl hM he hs))
  have hg := pointTrace_flatMap_le (centers l) (gateFixedSegments (coordinates p))
    (fun i => (gateFixedSegments (coordinates p) i).drop 4)
    (fun i _ => pointTrace_drop_le _ 4 (fun s hs => gate_base_nonpoint p i hs))
  have hu := pointTrace_le (wideFixed l (coordinates p) .upper)
  have hd := pointTrace_le (wideFixed l (coordinates p) .lower)
  have ha : pointTrace ((originalAuxiliary l (coordinates p)).map fun x => point x (coordinates p).D) ≤
      traceLength ((originalAuxiliary l (coordinates p)).map fun x => point x p.D) := pointTrace_le _
  simp only [interiorFixed, baseSmallSegments, pointTrace_append, trace_append]
  omega

private theorem shiftPoint_point_iff (guards rows : List ℕ) (s : Segment) :
    (shiftPoint guards rows s).start = (shiftPoint guards rows s).finish ↔ s.start = s.finish := by
  unfold shiftPoint
  split
  · rename_i h
    simp [point, segment, h.1]
  · rfl

private theorem pointTrace_shift (guards rows : List ℕ) (ss : List Segment) :
    pointTrace (ss.map (shiftPoint guards rows)) = pointTrace ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    simp only [pointTrace, List.map_cons, List.filter_cons, shiftPoint_point_iff] at ih ⊢
    split <;> simp only [trace_cons, shiftPoint_length, ih]

private theorem filterMap_points_le {α : Type*} (ss : List Segment) (f : Segment → Option α)
    (hf : ∀ s a, f s = some a → s.start = s.finish) :
    (ss.filterMap f).length ≤ pointTrace ss := by
  induction ss with
  | nil => exact Nat.le_refl 0
  | cons s ss ih =>
    cases he : f s with
    | none =>
      have hm : pointTrace ss ≤ pointTrace (s :: ss) := by
        by_cases hs : s.start = s.finish <;>
          simp only [pointTrace, List.filter_cons, hs, decide_true, decide_false, Bool.false_eq_true,
            ite_true, ite_false, trace_cons] <;> omega
      simpa only [List.filterMap_cons, he, List.length_nil, List.length_cons] using ih.trans hm
    | some a =>
      have hs := hf s a he
      have hlen := cells_length_point hs
      simp only [List.filterMap_cons, he, pointTrace, List.filter_cons, hs, decide_true,
        ite_true, trace_cons, hlen, List.length_cons] at ih ⊢
      omega

private theorem guard_length_pointTrace (l : PortLayout) (p : Coordinates) (ss : List Segment) :
    (guardColumns l p ss).length ≤ pointTrace ss := by
  apply filterMap_points_le
  intro s a hs
  split at hs
  · rename_i h; exact h.1
  · cases hs

private theorem marked_aux_length (l : PortLayout) (p : Coordinates) :
    ((streetColumns l p).filter fun x => decide (x ≠ 0 ∧ x ≠ p.W) && !((axisColumns l p).contains x)).length ≤
      (originalAuxiliary l p).length := by
  let pred (x : ℕ) := decide (x ≠ 0 ∧ x ≠ p.W) && !((axisColumns l p).contains x)
  have haxis : (axisColumns l p).filter pred = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    simp [pred, hx]
  have hframe : ([0, p.W].filter pred) = [] := by simp [pred]
  change (([0, p.W] ++ axisColumns l p ++ originalAuxiliary l p).filter pred).length ≤ _
  simp only [List.filter_append, haxis, hframe, List.nil_append]
  exact List.length_filter_le _ _

private theorem marked_point_trace (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) :
    pointTrace (markedInterior l (coordinates p)) ≤
      2 * traceLength (baseSmallSegments l p) + 4 * (originalAuxiliary l (coordinates p)).length +
        2 * (centers l).length := by
  unfold markedInterior
  extract_lets base guards shifted aux marked
  have hb : pointTrace base ≤ traceLength (baseSmallSegments l p) := base_point_trace l p hl hM
  have hshift : pointTrace shifted = pointTrace base := by
    dsimp only [shifted]
    split
    · exact pointTrace_shift _ _ _
    · rfl
  have haux : aux.length ≤ (originalAuxiliary l (coordinates p)).length := marked_aux_length l (coordinates p)
  have ha := trace_flatMap_le aux (fun x => [point x ((coordinates p).D - 2),
    point x ((coordinates p).D + 2)]) 2 (fun _ _ => by simp)
  have ham := pointTrace_le (aux.flatMap fun x => [point x ((coordinates p).D - 2),
    point x ((coordinates p).D + 2)])
  have hm : pointTrace marked ≤ traceLength (baseSmallSegments l p) +
      2 * (originalAuxiliary l (coordinates p)).length := by
    dsimp only [marked]
    rw [pointTrace_append, hshift]
    omega
  have hD : 0 < p.D := by have h := p.outer_distance; omega
  have hW : 0 < (coordinates p).W := by change 0 < (p.axes + 1) * p.D; positivity
  have hH : 0 < (coordinates p).H := by change 0 < 2 * p.D; omega
  have hg : (guardColumns l (coordinates p) (frame (coordinates p) ++ marked)).length ≤ pointTrace marked := by
    rw [guardColumns_frame_append l (coordinates p) marked hW hH]
    exact guard_length_pointTrace l (coordinates p) marked
  have hgp := pointTrace_le ((guardColumns l (coordinates p) (frame (coordinates p) ++ marked)).map
    fun x => point x ((coordinates p).D - 4))
  rw [trace_points _ (fun x => (x, (coordinates p).D - 4))] at hgp
  have hs := trace_flatMap_le (centers l) (fun i =>
    [point ((coordinates p).x i + 2) ((coordinates p).D + 4),
      point ((coordinates p).x i + 10) ((coordinates p).D + 4)]) 2 (fun _ _ => by simp)
  have hsp := pointTrace_le ((centers l).flatMap fun i =>
    [point ((coordinates p).x i + 2) ((coordinates p).D + 4),
      point ((coordinates p).x i + 10) ((coordinates p).D + 4)])
  change pointTrace ((marked ++ _) ++ _) ≤ _
  rw [pointTrace_append, pointTrace_append]
  omega

private theorem gate_private_trace (p : Scales.Parameters) (i : ℕ) :
    traceLength (((gateFixedSegments (coordinates p) i).drop 5).take 1) ≤ 4 := by
  have hb := segment_length_le ((coordinates p).x i + 1)
    (onSide (coordinates p) .lower ((coordinates p).depth 1 + 2)) ((coordinates p).x i + 4)
    (onSide (coordinates p) .lower ((coordinates p).depth 1 + 2))
  simp only [Nat.dist] at hb
  dsimp only [gateFixedSegments]
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero, trace_cons, trace_nil]
  omega

/-- Actual emitted fixed points, the four-cell private gate branches, and all signal holes. -/
def readerSmallSegments (l : PortLayout) (p : Scales.Parameters) (state : SignalState) : List Segment :=
  ((markedInterior l (coordinates p)).filter fun s => decide (s.start = s.finish)) ++
  (centers l).flatMap (fun i => ((gateFixedSegments (coordinates p) i).drop 5).take 1) ++
  l.signalSegments p state

private theorem gate_private_nonpoint (p : Scales.Parameters) (i : ℕ) {s : Segment}
    (hs : s ∈ ((gateFixedSegments (coordinates p) i).drop 5).take 1) : s.start ≠ s.finish := by
  dsimp only [gateFixedSegments] at hs
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.drop_succ_cons,
    List.drop_zero, List.take_succ_cons, List.take_zero, List.mem_singleton] at hs
  subst s
  intro heq
  have hx := congrArg Prod.fst heq
  dsimp only [segment] at hx
  omega

/-- Every segment in the small stock is a literal segment of the actual complete encoding. -/
theorem readerSmallSegments_subset_encoded (l : PortLayout) (p : Scales.Parameters) (state : SignalState) :
    ∀ s ∈ l.readerSmallSegments p state, s ∈ l.encodedSegments p state := by
  intro s hs
  simp only [readerSmallSegments, List.mem_append, or_assoc] at hs
  rcases hs with hpoint | hbranch | hsignal
  · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_filter.mp hpoint).1)
  · obtain ⟨i, hi, hbranch⟩ := List.mem_flatMap.mp hbranch
    apply List.mem_append_left
    apply long_segment_mem_fixed l p
    · simp only [interiorFixed, List.mem_append, or_assoc]
      right; left
      exact List.mem_flatMap.mpr ⟨i, hi, List.mem_of_mem_drop (List.mem_of_mem_take hbranch)⟩
    · exact gate_private_nonpoint p i hbranch
  · exact List.mem_append_right _ hsignal

/-- The complete small stock of the actual marked source fits the constant reader allowance. -/
theorem readerSmallSegments_trace_length_le (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) : ((l.readerSmallSegments p state).flatMap Segment.cells).length ≤ p.Q := by
  have hb := base_small_trace l p hl hM ha
  have hp := marked_point_trace l p hl hM
  have hg := trace_flatMap_le (centers l)
    (fun i => ((gateFixedSegments (coordinates p) i).drop 5).take 1) 4 (fun i _ => gate_private_trace p i)
  have hs := l.signalSegments_trace_length_le p hl state
  change traceLength (l.signalSegments p state) ≤ 54 * l.portCount at hs
  have hE : l.endpoints.length ≤ 2 * p.axes := (l.endpoints_length_le_twice hl).trans (by omega)
  have hC : 2 * (centers l).length ≤ p.axes := (l.gateCenters_length_twice_le hl).trans ha
  have hA : (originalAuxiliary l (coordinates p)).length ≤ 7 * p.axes := by
    rw [auxiliary_length]
    omega
  change traceLength _ ≤ _
  rw [readerSmallSegments, trace_append, trace_append]
  change pointTrace _ + _ + _ ≤ _
  unfold Scales.Parameters.Q
  nlinarith

end PushPuzzle.PushS.PortLayout
