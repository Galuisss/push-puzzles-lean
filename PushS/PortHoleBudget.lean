/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortCoreCounts
public import PushS.Distant
import all PushS.PortSegments
import CslibFrontier.Foundations.Data.List.Counting

/-!
# Hole budgets for the actual marked port board

Count the complete emitted segment traces before taking their union. Coincident traces only
decrease the number of holes. Page partitions bound the number of actual emitter groups.
-/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

private def traceLength (ss : List Segment) : ℕ := (ss.flatMap Segment.cells).length

@[simp] private theorem trace_nil : traceLength [] = 0 := rfl

@[simp] private theorem trace_cons (s : Segment) (ss : List Segment) :
    traceLength (s :: ss) = s.cells.length + traceLength ss := by
  simp [traceLength]

@[simp] private theorem trace_append (ss tt : List Segment) :
    traceLength (ss ++ tt) = traceLength ss + traceLength tt := by
  simp [traceLength, List.flatMap_append]

private theorem trace_flatMap_le {α : Type*} (xs : List α) (f : α → List Segment) (b : ℕ)
    (hb : ∀ x ∈ xs, traceLength (f x) ≤ b) : traceLength (xs.flatMap f) ≤ xs.length * b := by
  simpa only [traceLength, List.flatMap_assoc] using
    (List.length_flatMap_le (l := xs) (f := fun x => (f x).flatMap Segment.cells) hb)

private theorem trace_filterMap_le {α : Type*} (xs : List α) (f : α → Option Segment)
    (b : ℕ) (hb : ∀ x ∈ xs, ∀ s, f x = some s → s.cells.length ≤ b) :
    traceLength (xs.filterMap f) ≤ xs.length * b := by
  rw [List.filterMap_eq_flatMap_toList]
  apply trace_flatMap_le
  intro x hx
  cases he : f x with
  | none => simp
  | some s => simpa using hb x hx s he

private theorem trace_map_le {α : Type*} (xs : List α) (f : α → Segment) (b : ℕ)
    (hb : ∀ x ∈ xs, (f x).cells.length ≤ b) : traceLength (xs.map f) ≤ xs.length * b := by
  simpa only [traceLength, List.flatMap_map, Function.comp_def] using
    (List.length_flatMap_le (l := xs) (f := fun x => (f x).cells) hb)

private theorem cells_length_le (s : Segment) :
    s.cells.length ≤ Nat.dist s.start.1 s.finish.1 + Nat.dist s.start.2 s.finish.2 + 1 := by
  rcases s with ⟨⟨x, y⟩, ⟨u, v⟩⟩
  simp only [Segment.cells]
  split_ifs with hy hx
  · subst v
    simp only [List.length_map, List.length_range, Nat.dist]
    omega
  · subst u
    simp only [List.length_map, List.length_range, Nat.dist]
    omega
  · simp

private theorem segment_length_le (x y u v : ℕ) :
    (segment x y u v).cells.length ≤ Nat.dist x u + Nat.dist y v + 1 := by
  have h := cells_length_le (segment x y u v)
  simp only [segment, Nat.dist] at h ⊢
  omega

@[simp] private theorem point_length (x y : ℕ) : (point x y).cells.length = 1 := by
  simp [point, segment, Segment.cells]

private theorem cells_length_point {s : Segment} (h : s.start = s.finish) : s.cells.length = 1 := by
  rcases s with ⟨⟨x, y⟩, ⟨u, v⟩⟩
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
  simp [Segment.cells]

private theorem filterMap_length_le_trace {α : Type*} (ss : List Segment)
    (f : Segment → Option α) (hf : ∀ s a, f s = some a → 1 ≤ s.cells.length) :
    (ss.filterMap f).length ≤ traceLength ss := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    cases he : f s with
    | none => simp [he]; omega
    | some a =>
      have hs := hf s a he
      simp [he]
      omega

private theorem trace_points {α : Type*} (xs : List α) (f : α → ℕ × ℕ) :
    traceLength (xs.map fun a => point (f a).1 (f a).2) = xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [ih, Nat.add_comm]

private theorem pointHoles_card_le (ss : List Segment) :
    (pointHoles ss).card ≤ traceLength ss :=
  List.toFinset_card_le _

private theorem placements_length (l : PortLayout) :
    (placements l).length = l.upperPairs.length + l.lowerGroups.length := by
  simp [placements]

private theorem placements_length_le (l : PortLayout) (hl : l.pages.Valid) :
    (placements l).length ≤ 2 * l.portCount := by
  have hu := hl.upper.length_le
  have hb := hl.lower.length_le
  simp only [pages, PageLevels.Pages.upperPage, PageLevels.Pages.lowerPage,
    List.length_map] at hu hb
  rw [placements_length]
  omega

private theorem endpoints_length (l : PortLayout) :
    (endpoints l).length = 2 * (placements l).length := by
  unfold endpoints
  rw [List.length_flatMap_of_forall_length_eq (k := 2) (fun _ _ => rfl)]
  omega

/-- The actual endpoint emitter has at most four endpoints per declared axis. -/
theorem endpoints_length_le (l : PortLayout) (hl : l.pages.Valid) :
    (endpoints l).length ≤ 4 * l.portCount := by
  rw [endpoints_length]
  have h := placements_length_le l hl
  omega

private theorem centers_length_le (l : PortLayout) (hl : l.pages.Valid) :
    (centers l).length ≤ l.portCount := by
  have hb := hl.lower.length_le
  simp only [pages, PageLevels.Pages.lowerPage, List.length_map] at hb
  exact (List.length_filterMap_le _ _).trans hb

private theorem workingRows_length_le (l : PortLayout) (p : Coordinates) :
    (workingRows l p).length ≤ 3 * p.levels := by
  have h : (workingRows l p).length ≤ (List.range p.levels).length * 3 := by
    apply List.length_flatMap_le
    intro j _
    dsimp only
    split <;> simp
  simpa only [List.length_range, Nat.mul_comm] using h

private theorem pageColumns_length_le (l : PortLayout) (p : Coordinates) (side : Side) :
    (pageColumns l p side).length ≤ 2 + 3 * (endpoints l).length + 6 * (centers l).length := by
  have he : (((endpoints l).filter (fun e => decide (e.side = side))).flatMap (fun e =>
      let (f, r) := auxiliary p e
      [f, p.x e.port, r])).length =
        ((endpoints l).filter (fun e => decide (e.side = side))).length * 3 :=
    List.length_flatMap_of_forall_length_eq (fun _ _ => rfl)
  have hc : ((centers l).flatMap fun i => p.x i :: specialColumns p i).length =
      (centers l).length * 6 :=
    List.length_flatMap_of_forall_length_eq (fun _ _ => rfl)
  have hf := List.length_filter_le (fun e : Endpoint => decide (e.side = side)) (endpoints l)
  unfold pageColumns
  simp only [List.length_append, List.length_cons, List.length_nil, he]
  split <;> simp only [hc, List.length_nil] <;> omega

private theorem auxiliary_length (l : PortLayout) (p : Coordinates) :
    (originalAuxiliary l p).length = 2 * (endpoints l).length + 5 * (centers l).length := by
  have he : ((endpoints l).flatMap fun e =>
      let (f, r) := auxiliary p e
      [f, r]).length = (endpoints l).length * 2 :=
    List.length_flatMap_of_forall_length_eq (fun _ _ => rfl)
  have hc : ((centers l).flatMap (specialColumns p)).length = (centers l).length * 5 :=
    List.length_flatMap_of_forall_length_eq (fun _ _ => rfl)
  simp only [originalAuxiliary, List.length_append, he, hc]
  omega

private theorem streetColumns_length (l : PortLayout) (p : Coordinates) :
    (streetColumns l p).length =
      2 + l.portCount + 2 * (endpoints l).length + 5 * (centers l).length := by
  simp only [streetColumns, axisColumns, List.length_append, List.length_map,
    List.length_range, List.length_cons, List.length_nil, auxiliary_length]
  omega

private theorem adjacentPairs_length_le (xs : List ℕ) :
    (adjacentPairs xs).length ≤ xs.length ^ 2 := by
  unfold adjacentPairs
  rw [pow_two]
  apply List.length_flatMap_le
  intro a _
  exact List.length_filterMap_le _ _

private theorem wide_trace_le (l : PortLayout) (p : Coordinates) (side : Side) :
    traceLength (wideFixed l p side) ≤ 3 * p.levels * (pageColumns l p side).length ^ 2 := by
  have hw := workingRows_length_le l p
  have hp := adjacentPairs_length_le (pageColumns l p side)
  have ht : traceLength (wideFixed l p side) ≤
      (adjacentPairs (pageColumns l p side)).length * (3 * p.levels) := by
    apply trace_flatMap_le
    rintro ⟨a, b⟩ _
    dsimp only
    split
    · refine (trace_filterMap_le (workingRows l p) _ 1 ?_).trans ?_
      · intro y _ s hs
        split at hs
        · cases hs
        · cases hs
          simp
      · simpa only [Nat.mul_one] using hw
    · simp
  exact ht.trans (by nlinarith)

private theorem endpointFixed_trace_le (l : PortLayout) (p : Scales.Parameters) (e : Endpoint) :
    traceLength (endpointFixedSegments l (coordinates p) e) ≤
      2 * p.Y p.levels + p.L p.levels + 6 * p.levels + 9 := by
  let c := coordinates p
  have hx : c.length e.level + 64 < c.x e.port := readLength_add_lt_x p e.port e.level
  have hy : c.depth e.level + 64 < c.H := readDepth_add_lt_H p e.level
  have hY : c.depth e.level ≤ p.Y p.levels := readDepth_le_last p e.level
  have hL : c.length e.level ≤ p.L p.levels := readLength_le_last p e.level
  have hlong : traceLength
      [segment (auxiliary c e).1 (onSide c e.side 1)
        (auxiliary c e).1 (onSide c e.side (c.depth e.level + 2)),
       segment (auxiliary c e).2 (onSide c e.side 1)
        (auxiliary c e).2 (onSide c e.side (c.depth e.level - 1)),
       segment (inward (auxiliary c e).1 e.inward 1) (onSide c e.side (c.depth e.level + 2))
        (outward (c.x e.port) e.inward 1) (onSide c e.side (c.depth e.level + 2))] ≤
        2 * c.depth e.level + c.length e.level + 7 := by
    have h1 := segment_length_le (auxiliary c e).1 (onSide c e.side 1)
      (auxiliary c e).1 (onSide c e.side (c.depth e.level + 2))
    have h2 := segment_length_le (auxiliary c e).2 (onSide c e.side 1)
      (auxiliary c e).2 (onSide c e.side (c.depth e.level - 1))
    have h3 := segment_length_le (inward (auxiliary c e).1 e.inward 1)
      (onSide c e.side (c.depth e.level + 2)) (outward (c.x e.port) e.inward 1)
      (onSide c e.side (c.depth e.level + 2))
    simp only [trace_cons, trace_nil]
    cases hs : e.side <;> cases hd : e.inward <;>
      simp [auxiliary, outward, inward, onSide, hs, hd, Nat.dist] at h1 h2 h3 ⊢ <;> omega
  have hpoints : traceLength ((workingRows l c).flatMap fun v =>
      (if v ≤ c.depth e.level then
        [point (((auxiliary c e).1 + c.x e.port) / 2) (onSide c e.side v)] else []) ++
      (if v < c.depth e.level then [point (inward (c.x e.port) e.inward 1)
        (onSide c e.side v)] else [])) ≤ 6 * p.levels := by
    have hh : traceLength ((workingRows l c).flatMap fun v =>
        (if v ≤ c.depth e.level then
          [point (((auxiliary c e).1 + c.x e.port) / 2) (onSide c e.side v)] else []) ++
        (if v < c.depth e.level then [point (inward (c.x e.port) e.inward 1)
          (onSide c e.side v)] else [])) ≤ (workingRows l c).length * 2 := by
      apply trace_flatMap_le
      intro v _
      split_ifs <;> simp
    have hw := workingRows_length_le l c
    change (workingRows l c).length ≤ 3 * p.levels at hw
    omega
  have hmiddle : traceLength (if e.level < c.levels then
      [point (auxiliary c e).1 (onSide c e.side ((c.depth e.level + c.depth (e.level + 1)) / 2)),
       point (auxiliary c e).2 (onSide c e.side ((c.depth e.level + c.depth (e.level + 1)) / 2))]
      else []) ≤ 2 := by split <;> simp
  change traceLength (_ ++ _ ++ _) ≤ _
  rw [trace_append, trace_append]
  simp only [c, auxiliary] at hlong hpoints hmiddle hY hL
  dsimp only
  omega

private theorem gateFixed_trace_le (p : Scales.Parameters) (middle : ℕ) :
    traceLength (gateFixedSegments (coordinates p) middle) ≤ 4 * p.Y p.levels + 12 := by
  let c := coordinates p
  have hy : c.depth 1 + 64 < c.H := readDepth_add_lt_H p 1
  have hlo : 16384 ≤ c.depth 1 := readDepth_ge p (by omega) p.levels_pos
  have hY : c.depth 1 ≤ p.Y p.levels := readDepth_le_last p 1
  have hside : Side.lower ≠ Side.upper := by decide
  have hlong : traceLength ([c.x middle - 2, c.x middle + 6, c.x middle + 8,
      c.x middle + 12].map fun col =>
      segment col (onSide c .lower 1) col (onSide c .lower (c.depth 1 - 1))) ≤
        4 * p.Y p.levels := by
    refine (trace_map_le _ _ (p.Y p.levels) ?_).trans_eq (by simp)
    intro col _
    refine (segment_length_le _ _ _ _).trans ?_
    simp only [onSide, hside, ite_false, Nat.dist]
    omega
  have hlocal : traceLength
      [point (c.x middle + 4) (onSide c .lower (c.depth 1 + 1)),
       segment (c.x middle + 1) (onSide c .lower (c.depth 1 + 2))
        (c.x middle + 4) (onSide c .lower (c.depth 1 + 2)),
       point (c.x middle) (onSide c .lower (c.depth 1 / 2)),
       point (c.x middle + 4) (onSide c .lower (c.depth 1 / 2))] ≤ 7 := by
    have h := segment_length_le (c.x middle + 1) (onSide c .lower (c.depth 1 + 2))
      (c.x middle + 4) (onSide c .lower (c.depth 1 + 2))
    simp only [trace_cons, trace_nil, point_length]
    simp only [Nat.dist] at h
    omega
  have hmarkers : traceLength (if 1 < c.levels then
      (specialColumns c middle).map fun col =>
        point col (onSide c .lower ((c.depth 1 + c.depth 2) / 2)) else []) ≤ 5 := by
    split <;> simp [specialColumns]
  change traceLength (_ ++ _ ++ _) ≤ _
  rw [trace_append, trace_append]
  simp only [c] at hlong hlocal hmarkers
  dsimp only
  omega

private theorem shiftPoint_length (guards rows : List ℕ) (s : Segment) :
    (shiftPoint guards rows s).cells.length = s.cells.length := by
  unfold shiftPoint
  split
  · next h => simp only [point_length, cells_length_point h.1]
  · rfl

private theorem trace_shift (guards rows : List ℕ) (ss : List Segment) :
    traceLength (ss.map (shiftPoint guards rows)) = traceLength ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih => simp only [List.map_cons, trace_cons, shiftPoint_length, ih]

private theorem guardColumns_length_le (l : PortLayout) (p : Coordinates) (ss : List Segment) :
    (guardColumns l p ss).length ≤ traceLength ss := by
  apply filterMap_length_le_trace
  intro s a hs
  split at hs
  · next h => exact le_of_eq (cells_length_point h.1).symm
  · cases hs

private theorem guardColumns_frame_append (l : PortLayout) (p : Coordinates)
    (ss : List Segment) (hw : 0 < p.W) (hh : 0 < p.H) :
    guardColumns l p (frame p ++ ss) = guardColumns l p ss := by
  have hw0 : 0 ≠ p.W := by omega
  have hh0 : 0 ≠ p.H := by omega
  have he : guardColumns l p (frame p) = [] := by
    simp [guardColumns, frame, segment, hw0, hh0]
  unfold guardColumns at he ⊢
  rw [List.filterMap_append, he, List.nil_append]

private theorem interiorFixed_trace_le (l : PortLayout) (p : Scales.Parameters) :
    traceLength (interiorFixed l (coordinates p)) ≤
      (endpoints l).length * (2 * p.Y p.levels + p.L p.levels + 6 * p.levels + 9) +
      (centers l).length * (4 * p.Y p.levels + 12) +
      6 * p.levels * (2 + 3 * (endpoints l).length + 6 * (centers l).length) ^ 2 +
      2 * (endpoints l).length + 5 * (centers l).length := by
  let c := coordinates p
  have he := trace_flatMap_le (endpoints l) (endpointFixedSegments l c)
    (2 * p.Y p.levels + p.L p.levels + 6 * p.levels + 9)
    (fun e _ => endpointFixed_trace_le l p e)
  have hc := trace_flatMap_le (centers l) (gateFixedSegments c)
    (4 * p.Y p.levels + 12) (fun i _ => gateFixed_trace_le p i)
  have hu : traceLength (wideFixed l c .upper) ≤
      3 * p.levels * (2 + 3 * (endpoints l).length + 6 * (centers l).length) ^ 2 := by
    refine (wide_trace_le l c .upper).trans (Nat.mul_le_mul_left _ ?_)
    simpa only [pow_two] using Nat.mul_le_mul (pageColumns_length_le l c .upper)
      (pageColumns_length_le l c .upper)
  have hb : traceLength (wideFixed l c .lower) ≤
      3 * p.levels * (2 + 3 * (endpoints l).length + 6 * (centers l).length) ^ 2 := by
    refine (wide_trace_le l c .lower).trans (Nat.mul_le_mul_left _ ?_)
    simpa only [pow_two] using Nat.mul_le_mul (pageColumns_length_le l c .lower)
      (pageColumns_length_le l c .lower)
  have ha : traceLength ((originalAuxiliary l c).map fun x => point x c.D) =
      2 * (endpoints l).length + 5 * (centers l).length :=
    (trace_points (originalAuxiliary l c) (fun x => (x, c.D))).trans (auxiliary_length l c)
  change traceLength (interiorFixed l c) ≤ _
  simp only [interiorFixed, trace_append]
  nlinarith only [he, hc, hu, hb, ha]

private theorem markedInterior_trace_le (l : PortLayout) (p : Scales.Parameters) :
    traceLength (markedInterior l (coordinates p)) ≤
      2 * traceLength (interiorFixed l (coordinates p)) +
        4 * (streetColumns l (coordinates p)).length + 2 * (centers l).length := by
  let c := coordinates p
  let base := interiorFixed l c
  let guards := guardColumns l c (frame c ++ base)
  let shifted := if guards.any (fun x => guards.contains (x + 1)) then
    base.map (shiftPoint guards (streetRows c)) else base
  let aux := (streetColumns l c).filter fun x =>
    decide (x ≠ 0 ∧ x ≠ c.W) && !((axisColumns l c).contains x)
  let marked := shifted ++ aux.flatMap (fun x => [point x (c.D - 2), point x (c.D + 2)])
  have hshift : traceLength shifted = traceLength base := by
    dsimp only [shifted]
    split
    · exact trace_shift _ _ _
    · rfl
  have ha : traceLength (aux.flatMap fun x => [point x (c.D - 2), point x (c.D + 2)]) ≤
      aux.length * 2 := trace_flatMap_le _ _ 2 (fun _ _ => by simp)
  have haux : aux.length ≤ (streetColumns l c).length := List.length_filter_le _ _
  have hmarked : traceLength marked ≤ traceLength base + 2 * (streetColumns l c).length := by
    dsimp only [marked]
    rw [trace_append, hshift]
    omega
  have hD : 0 < p.D := by have h := p.outer_distance; omega
  have hW : 0 < c.W := Nat.mul_pos (by omega) hD
  have hH : 0 < c.H := by change 0 < 2 * p.D; omega
  have hguards : (guardColumns l c (frame c ++ marked)).length ≤ traceLength marked := by
    rw [guardColumns_frame_append l c marked hW hH]
    exact guardColumns_length_le l c marked
  have hg : traceLength ((guardColumns l c (frame c ++ marked)).map fun x => point x (c.D - 4)) =
      (guardColumns l c (frame c ++ marked)).length :=
    trace_points _ (fun x => (x, c.D - 4))
  have hs : traceLength ((centers l).flatMap fun i =>
      [point (c.x i + 2) (c.D + 4), point (c.x i + 10) (c.D + 4)]) ≤ (centers l).length * 2 :=
    trace_flatMap_le _ _ 2 (fun _ _ => by simp)
  change traceLength (marked ++
      (guardColumns l c (frame c ++ marked)).map (fun x => point x (c.D - 4)) ++
      (centers l).flatMap (fun i =>
        [point (c.x i + 2) (c.D + 4), point (c.x i + 10) (c.D + 4)])) ≤
    2 * traceLength base + 4 * (streetColumns l c).length + 2 * (centers l).length
  rw [trace_append, trace_append, hg]
  omega

private theorem interiorFixed_trace_uniform (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) :
    traceLength (interiorFixed l (coordinates p)) ≤
      12 * (p.axes + 1) * p.Y p.levels + 4 * (p.axes + 1) * p.L p.levels +
      24 * (p.axes + 1) * p.levels + 61 * (p.axes + 1) +
      2400 * p.levels * (p.axes + 1) ^ 2 := by
  let N := p.axes + 1
  have hn : 1 ≤ N := by omega
  have he : (endpoints l).length ≤ 4 * N := by
    have h := endpoints_length_le l hl
    omega
  have hc : (centers l).length ≤ N := by
    have h := centers_length_le l hl
    omega
  have hp : 2 + 3 * (endpoints l).length + 6 * (centers l).length ≤ 20 * N := by omega
  have hep := Nat.mul_le_mul_right (2 * p.Y p.levels + p.L p.levels + 6 * p.levels + 9) he
  have hcp := Nat.mul_le_mul_right (4 * p.Y p.levels + 12) hc
  have hpp := Nat.mul_le_mul_left (6 * p.levels) (Nat.mul_le_mul hp hp)
  have hi := interiorFixed_trace_le l p
  change traceLength (interiorFixed l (coordinates p)) ≤
    12 * N * p.Y p.levels + 4 * N * p.L p.levels + 24 * N * p.levels + 61 * N +
      2400 * p.levels * N ^ 2
  nlinarith only [hep, hcp, hpp, hi, he, hc]

private theorem endpoint_trace_le (p : Scales.Parameters) (state : SignalState) (e : Endpoint) :
    traceLength (endpointSegments (coordinates p) state e) ≤ 6 := by
  have hy : (coordinates p).depth e.level + 64 < (coordinates p).H :=
    readDepth_add_lt_H p e.level
  have hx : 64 < (coordinates p).x e.port := by
    have h := readLength_add_lt_x p e.port 0
    change readLength p 0 + 64 < (coordinates p).x e.port at h
    omega
  have ha := Bool.toNat_le (if e.side = .upper then state.axes.getD e.port false
    else !(state.axes.getD e.port false))
  have hb := Bool.toNat_le (if e.inward then state.internal.getD e.internal false
    else !(state.internal.getD e.internal false))
  have hav := segment_length_le ((coordinates p).x e.port)
    (onSide (coordinates p) e.side ((coordinates p).depth e.level))
    ((coordinates p).x e.port)
    (onSide (coordinates p) e.side ((coordinates p).depth e.level + 1 +
      (if e.side = .upper then state.axes.getD e.port false
        else !(state.axes.getD e.port false)).toNat))
  have hhv := segment_length_le (inward ((coordinates p).x e.port) e.inward 1)
    (onSide (coordinates p) e.side ((coordinates p).depth e.level))
    (inward ((coordinates p).x e.port) e.inward (1 +
      (if e.inward then state.internal.getD e.internal false
        else !(state.internal.getD e.internal false)).toNat))
    (onSide (coordinates p) e.side ((coordinates p).depth e.level))
  dsimp only [endpointSegments]
  simp only [trace_cons, trace_nil]
  cases hs : e.side <;> cases hd : e.inward <;>
    simp [onSide, inward, hs, hd, Nat.dist] at hav hhv ha hb ⊢ <;> omega

private theorem gate_trace_le (p : Scales.Parameters) (state : SignalState)
    (kind : Shuttle.Kind) (first internal : ℕ) :
    traceLength (gateSegments (coordinates p) state kind first internal) ≤ 15 := by
  have hy : (coordinates p).depth 1 + 64 < (coordinates p).H := readDepth_add_lt_H p 1
  have hx : 64 < (coordinates p).x (first + 1) := by
    have h := readLength_add_lt_x p (first + 1) 0
    change readLength p 0 + 64 < (coordinates p).x (first + 1) at h
    omega
  have hk : 2 ≤ kappaNat kind ∧ kappaNat kind ≤ 4 := by cases kind <;> decide
  have hl := Bool.toNat_le (state.internal.getD internal false)
  have hr := Bool.toNat_le (state.internal.getD (internal + 2) false)
  have ha := Bool.toNat_le (state.axes.getD (first + 1) false)
  have hs : 1 ≤ (if state.internal.getD (internal + 1) false then 6 else 1) ∧
      (if state.internal.getD (internal + 1) false then 6 else 1) ≤ 6 := by
    cases state.internal.getD (internal + 1) false <;> decide
  have hG := segment_length_le
    ((coordinates p).x (first + 1) + 2 + (state.internal.getD internal false).toNat - kappaNat kind)
    (onSide (coordinates p) .lower ((coordinates p).depth 1))
    ((coordinates p).x (first + 1) + if state.internal.getD (internal + 1) false then 6 else 1)
    (onSide (coordinates p) .lower ((coordinates p).depth 1))
  have hJ := segment_length_le
    ((coordinates p).x (first + 1) + (if state.internal.getD (internal + 1) false then 6 else 1) + 3)
    (onSide (coordinates p) .lower ((coordinates p).depth 1))
    ((coordinates p).x (first + 1) + 11 + (state.internal.getD (internal + 2) false).toNat)
    (onSide (coordinates p) .lower ((coordinates p).depth 1))
  have hA := segment_length_le ((coordinates p).x (first + 1))
    (onSide (coordinates p) .lower ((coordinates p).depth 1 + 1))
    ((coordinates p).x (first + 1))
    (onSide (coordinates p) .lower ((coordinates p).depth 1 + 2 -
      (state.axes.getD (first + 1) false).toNat))
  dsimp only [gateSegments]
  simp only [trace_cons, trace_nil]
  have hside : Side.lower ≠ Side.upper := by decide
  simp only [onSide, hside, ite_false, Nat.dist] at hG hJ hA ⊢
  omega

private theorem triple_trace_le (p : Scales.Parameters) (state : SignalState) (g : Placement) :
    traceLength (tripleSignal (coordinates p) state g) ≤ 15 := by
  cases hg : g.gate with
  | none => simp [tripleSignal, hg]
  | some kind => simpa [tripleSignal, hg] using gate_trace_le p state kind g.left g.internal

/-- Before taking the hole union, every actual signal trace uses at most 54 cells per axis. -/
theorem signalSegments_trace_length_le (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (state : SignalState) :
    ((l.signalSegments p state).flatMap Segment.cells).length ≤ 54 * l.portCount := by
  have he := trace_flatMap_le (endpoints l) (endpointSegments (coordinates p) state) 6
    (fun e _ => endpoint_trace_le p state e)
  have hg := trace_flatMap_le (placements l) (tripleSignal (coordinates p) state) 15
    (fun g _ => triple_trace_le p state g)
  have hp := placements_length_le l hl
  rw [endpoints_length] at he
  change traceLength (rawSignals l (coordinates p) state) ≤ _
  rw [rawSignals, trace_append]
  omega

private theorem nonframe_trace_polynomial (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) (state : SignalState) :
    traceLength (markedInterior l (coordinates p) ++ l.signalSegments p state) ≤
      24 * (p.axes + 1) * p.Y p.levels + 8 * (p.axes + 1) * p.L p.levels +
      8192 * (p.axes + 1) ^ 2 * (p.levels + 1) := by
  let N := p.axes + 1
  have hn : 1 ≤ N := by omega
  have he : (endpoints l).length ≤ 4 * N := by
    have h := endpoints_length_le l hl
    omega
  have hc : (centers l).length ≤ N := by
    have h := centers_length_le l hl
    omega
  have hcols : (streetColumns l (coordinates p)).length ≤ 16 * N := by
    rw [streetColumns_length]
    omega
  have hs : traceLength (l.signalSegments p state) ≤ 54 * N := by
    have h := signalSegments_trace_length_le l p hl state
    change traceLength (l.signalSegments p state) ≤ _ at h
    omega
  have hm := markedInterior_trace_le l p
  have hi := interiorFixed_trace_uniform l p hl ha
  have hNN : N ≤ N ^ 2 := by nlinarith only [hn]
  have hNM := Nat.mul_le_mul_right p.levels hNN
  have hpoint : 48 * N * p.levels + 242 * N + 4800 * p.levels * N ^ 2 ≤
      8192 * N ^ 2 * (p.levels + 1) := by
    nlinarith only [hNN, hNM, Nat.zero_le (N ^ 2 * p.levels), Nat.zero_le (N ^ 2)]
  rw [trace_append]
  change traceLength (markedInterior l (coordinates p)) + traceLength (l.signalSegments p state) ≤
    24 * N * p.Y p.levels + 8 * N * p.L p.levels + 8192 * N ^ 2 * (p.levels + 1)
  change traceLength (interiorFixed l (coordinates p)) ≤
    12 * N * p.Y p.levels + 4 * N * p.L p.levels + 24 * N * p.levels + 61 * N +
      2400 * p.levels * N ^ 2 at hi
  nlinarith only [hm, hi, hcols, hc, hs, hpoint]

private theorem polynomial_le_budget (p : Scales.Parameters) :
    24 * (p.axes + 1) * p.Y p.levels + 8 * (p.axes + 1) * p.L p.levels +
      8192 * (p.axes + 1) ^ 2 * (p.levels + 1) ≤ 2 * p.b p.levels := by
  let N := p.axes + 1
  have hy := p.Y_ge_A p.levels
  have hA : p.A = 4096 * N * (p.levels + 1) := by
    dsimp [Scales.Parameters.A, Scales.Parameters.Q, N]
    ring
  rw [hA] at hy
  have hpoint := Nat.mul_le_mul_left (2 * N) hy
  have hS : 2 ≤ p.S := by unfold Scales.Parameters.S; omega
  have hL : 2 * p.Y p.levels ≤ p.L p.levels := by
    rw [p.L_eq p.levels p.levels_pos]
    have h := Nat.mul_le_mul_left (p.Y p.levels) hS
    omega
  have hL' : 10 * p.Y p.levels ≤ 8 * p.L p.levels := by omega
  have hscaled := Nat.mul_le_mul_left N hL'
  unfold Scales.Parameters.b
  change 24 * N * p.Y p.levels + 8 * N * p.L p.levels +
    8192 * N ^ 2 * (p.levels + 1) ≤ 2 * (p.Q + 8 * N * (p.Y p.levels + p.L p.levels + 10))
  nlinarith only [hpoint, hscaled]

private def cellCoordinates (w h : ℕ) : Cell w h ↪ ℕ × ℕ where
  toFun q := (q.1.val, q.2.val)
  inj' _ _ he := Prod.ext (Fin.ext (congrArg Prod.fst he)) (Fin.ext (congrArg Prod.snd he))

private theorem frame_contains (p : Coordinates) (a : Cell (p.W + 1) (p.H + 1))
    (hs : ∃ s ∈ frame p, s.Contains (a.1.val, a.2.val)) : a ∈ Boundary.frame := by
  obtain ⟨s, hs, hq⟩ := hs
  have hb : a.2.val = 0 ∨ a.1.val + 1 = p.W + 1 ∨
      a.2.val + 1 = p.H + 1 ∨ a.1.val = 0 := by
    simp only [frame, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl <;>
      simp only [segment, Segment.Contains] at hq <;> omega
  simpa only [Boundary.frame, Boundary.edge, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and, or_assoc] using hb

private theorem interior_subset (l : PortLayout) (p : Scales.Parameters) (state : SignalState) :
    ((SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) \ Boundary.frame).map
      (cellCoordinates (p.W + 1) (p.H + 1))) ⊆
        pointHoles (markedInterior l (coordinates p) ++ l.signalSegments p state) := by
  intro q hq
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hq
  obtain ⟨hhole, hframe⟩ := Finset.mem_sdiff.mp ha
  obtain ⟨s, hs, ha⟩ := (SegmentRecipe.mem_holes _ a).mp hhole
  simp only [encodedSegments, fixedSegments, List.mem_append] at hs
  rcases hs with (hs | hs) | hs
  · exact False.elim (hframe (frame_contains (coordinates p) a ⟨s, hs, ha⟩))
  · exact (mem_pointHoles _ _).mpr ⟨s, List.mem_append_left _ hs, ha⟩
  · exact (mem_pointHoles _ _).mpr ⟨s, List.mem_append_right _ hs, ha⟩

/-- The actual finite board has at most twice the geometric outer budget in interior holes,
for every physical signal state. -/
theorem encodedSegments_interior_card_le (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) (state : SignalState) :
    (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) \ Boundary.frame).card ≤
      2 * p.b p.levels := by
  have hc := Finset.card_le_card (interior_subset l p state)
  rw [Finset.card_map] at hc
  exact hc.trans ((pointHoles_card_le _).trans
    ((nonframe_trace_polynomial l p hl ha state).trans (polynomial_le_budget p)))

/-- The actual initial holes make the central band of radius four remote whenever its horizontal
coordinates retain the half-spacing margins of the separator markers. -/
theorem far_of_central_margins (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) (state : SignalState)
    (s : State (p.W + 1) (p.H + 1))
    (hs : PushS.holes s = SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state))
    (q : Cell (p.W + 1) (p.H + 1))
    (hx : p.D ≤ 2 * q.1.val + p.L p.levels + 4)
    (hx' : p.D + 2 * q.1.val ≤ 2 * p.W + p.L p.levels + 4)
    (hy : p.D ≤ q.2.val + 4) (hy' : q.2.val ≤ p.D + 4) : Distant.Far s q := by
  have hb := l.encodedSegments_interior_card_le p hl ha state
  rw [← hs] at hb
  apply (Distant.far_iff_margins s q).mpr
  have hd := p.outer_distance
  have hh : p.H = 2 * p.D := rfl
  omega

end PushPuzzle.PushS.PortLayout
