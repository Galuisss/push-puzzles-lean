/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortSegments
public import PushS.PortLayoutCoordinates
import all PushS.PortSegments

/-!
# Bounds of the actual physical hole segments

The bounded table reads control every local endpoint, branch, separator and marker.
Only the supplied page partition and the number of allocated axes are used here.
-/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS.Reduction

private def Box (p : Scales.Parameters) (s : Segment) : Prop :=
  s.start.1 ≤ p.W ∧ s.finish.1 ≤ p.W ∧ s.start.2 ≤ p.H ∧ s.finish.2 ≤ p.H

private def AllBox (p : Scales.Parameters) (ss : List Segment) : Prop := ∀ s ∈ ss, Box p s

private theorem box_segment (p : Scales.Parameters) {x y u v : ℕ}
    (hx : x ≤ p.W) (hy : y ≤ p.H) (hu : u ≤ p.W) (hv : v ≤ p.H) :
    Box p (segment x y u v) := by
  simp only [Box, segment]
  omega

private theorem box_point (p : Scales.Parameters) {x y : ℕ}
    (hx : x ≤ p.W) (hy : y ≤ p.H) : Box p (point x y) := box_segment p hx hy hx hy

private theorem box_append (p : Scales.Parameters) {ss tt : List Segment}
    (hs : AllBox p ss) (ht : AllBox p tt) : AllBox p (ss ++ tt) := by
  intro s h
  exact (List.mem_append.mp h).elim (hs s) (ht s)

private theorem box_map (p : Scales.Parameters) {α : Type} {xs : List α} {f : α → Segment}
    (h : ∀ x ∈ xs, Box p (f x)) : AllBox p (xs.map f) := by
  intro s hs
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hs
  exact h x hx

private theorem box_flatMap (p : Scales.Parameters) {α : Type} {xs : List α}
    {f : α → List Segment} (h : ∀ x ∈ xs, AllBox p (f x)) : AllBox p (xs.flatMap f) := by
  intro s hs
  obtain ⟨x, hx, hs⟩ := List.mem_flatMap.mp hs
  exact h x hx s hs

private theorem onSide_le (p : Scales.Parameters) (side : Side) {y : ℕ} (hy : y ≤ p.H) :
    onSide (coordinates p) side y ≤ p.H := by
  cases side <;> simp [onSide, coordinates]
  exact hy

private theorem x_margin (p : Scales.Parameters) {i : ℕ} (hi : i < p.axes) (j : ℕ) :
    p.x i + readLength p j + 64 < p.W := x_add_readLength_lt_W p hi j

private theorem group_mem_bound (p : PageLevels.Page) (hp : p.Valid)
    {g : PageLevels.Group} (hg : g ∈ p.groups) : g.left < g.right ∧ g.right < p.portCount := by
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hg
  exact hp.bounded i

private theorem placement_ports (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) {g : Placement}
    (hg : g ∈ placements l) :
    g.left < p.axes ∧ g.right < p.axes ∧ (g.gate.isSome → g.left + 1 < p.axes) := by
  simp only [placements, List.mem_append, List.mem_map] at hg
  rcases hg with ⟨⟨⟨a, b⟩, i⟩, hi, rfl⟩ | ⟨⟨lower, i⟩, hi, rfl⟩
  · have hm := List.fst_mem_of_mem_zipIdx hi
    have hb := group_mem_bound l.pages.upperPage hl.upper
      (List.mem_map.mpr ⟨(a, b), hm, rfl⟩)
    simp only [pages, PageLevels.Pages.upperPage, PageLevels.Group.left,
      PageLevels.Group.right] at hb
    simp only [Option.isSome_none, Bool.false_eq_true, false_implies, and_true]
    omega
  · have hm := List.fst_mem_of_mem_zipIdx hi
    have hb := group_mem_bound l.pages.lowerPage hl.lower
      (List.mem_map.mpr ⟨lower, hm, rfl⟩)
    cases lower <;> simp only [encLowerGroup_elim, encLowerGroup_toSum, Sum.elim_inl, Sum.elim_inr, LowerGroup.shape, pages,
      PageLevels.Pages.lowerPage, PageLevels.Group.left, PageLevels.Group.right] at hb ⊢
    · simp only [Option.isSome_none, Bool.false_eq_true, false_implies, and_true]
      omega
    · simp only [Option.isSome_some, true_implies]
      omega

private theorem endpoint_port (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) {e : Endpoint}
    (he : e ∈ endpoints l) : e.port < p.axes := by
  obtain ⟨g, hg, he⟩ := List.mem_flatMap.mp he
  have hb := placement_ports l p hl ha hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact hb.1
  · exact hb.2.1

private theorem center_port (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) {i : ℕ} (hi : i ∈ centers l) : i < p.axes := by
  obtain ⟨g, hg, hi⟩ := List.mem_filterMap.mp hi
  have hb := group_mem_bound l.pages.lowerPage hl.lower (List.mem_map.mpr ⟨g, hg, rfl⟩)
  cases g with
  | wire a b => simp [encLowerGroup_elim, encLowerGroup_toSum, Sum.elim_inl] at hi
  | gate kind a =>
    simp only [encLowerGroup_elim, encLowerGroup_toSum, Sum.elim_inr, Option.some.injEq] at hi
    simp only [LowerGroup.shape, PageLevels.Group.left, PageLevels.Group.right] at hb
    have hb' : a + 2 < l.portCount := hb.2
    omega

private theorem frame_box (p : Scales.Parameters) : AllBox p (frame (coordinates p)) := by
  intro s hs
  simp only [frame, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl <;>
    exact box_segment p (by simp [coordinates]) (by simp [coordinates])
      (by simp [coordinates]) (by simp [coordinates])

private theorem auxiliary_margin (p : Scales.Parameters) (e : Endpoint) (he : e.port < p.axes) :
    (auxiliary (coordinates p) e).1 + 32 < p.W ∧
      (auxiliary (coordinates p) e).2 + 32 < p.W := by
  have hx := x_margin p he e.level
  simp only [auxiliary, Coordinates.x, Coordinates.length, coordinates]
  simp only [readLength, Scales.Parameters.x] at hx
  change _ + 32 < p.W ∧ _ + 32 < p.W
  cases e.inward <;> simp only [outward, inward, Bool.false_eq_true, ite_false, ite_true] <;> omega

private theorem workingRow_le (l : PortLayout) (p : Scales.Parameters) {y : ℕ}
    (hy : y ∈ workingRows l (coordinates p)) : y + 32 < p.H := by
  obtain ⟨j, _, hy⟩ := List.mem_flatMap.mp hy
  have hm := readDepth_add_lt_H p (j + 1)
  dsimp only at hy
  split at hy <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  all_goals simp only [Coordinates.depth, coordinates, readDepth] at hy hm
  all_goals omega

private theorem box_side_segment (p : Scales.Parameters) (side : Side) {x y u v : ℕ}
    (hx : x ≤ p.W) (hy : y ≤ p.H) (hu : u ≤ p.W) (hv : v ≤ p.H) :
    Box p (segment x (onSide (coordinates p) side y) u (onSide (coordinates p) side v)) :=
  box_segment p hx (onSide_le p side hy) hu (onSide_le p side hv)

private theorem box_side_point (p : Scales.Parameters) (side : Side) {x y : ℕ}
    (hx : x ≤ p.W) (hy : y ≤ p.H) :
    Box p (point x (onSide (coordinates p) side y)) :=
  box_point p hx (onSide_le p side hy)

private theorem endpointFixedSegments_box (l : PortLayout) (p : Scales.Parameters) (e : Endpoint)
    (he : e.port < p.axes) : AllBox p (endpointFixedSegments l (coordinates p) e) := by
  have hx : (coordinates p).x e.port + 64 < p.W := by
    have h := x_margin p he e.level
    change p.x e.port + 64 < p.W
    omega
  have hy : (coordinates p).depth e.level + 64 < p.H := readDepth_add_lt_H p e.level
  have hnext : (coordinates p).depth (e.level + 1) + 64 < p.H :=
    readDepth_add_lt_H p (e.level + 1)
  have hH : 64 < p.H := by have := readDepth_add_lt_H p 0; omega
  obtain ⟨hf, hr⟩ := auxiliary_margin p e he
  dsimp only [endpointFixedSegments]
  simp only [List.append_assoc]
  apply box_append p
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact box_side_segment p e.side (by omega) (by omega) (by omega) (by omega)
    · exact box_side_segment p e.side (by omega) (by omega) (by omega) (by omega)
    · apply box_side_segment p e.side
      · cases e.inward <;> simp only [inward, Bool.false_eq_true,
          ite_false, ite_true] <;> omega
      · omega
      · cases e.inward <;> simp only [outward, Bool.false_eq_true,
          ite_false, ite_true] <;> omega
      · omega
  · apply box_append p
    · apply box_flatMap p
      intro v _
      apply box_append p
      · split
        · intro s hs
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
          subst s
          apply box_side_point p e.side <;> omega
        · exact fun _ h => False.elim (List.not_mem_nil h)
      · split
        · intro s hs
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
          subst s
          apply box_side_point p e.side
          · cases e.inward <;> simp only [inward, Bool.false_eq_true,
              ite_false, ite_true] <;> omega
          · omega
        · exact fun _ h => False.elim (List.not_mem_nil h)
    · split
      · intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        all_goals apply box_side_point p e.side <;> omega
      · exact fun _ h => False.elim (List.not_mem_nil h)

private theorem specialColumn_le (p : Scales.Parameters) {i x : ℕ} (hi : i < p.axes)
    (hx : x ∈ specialColumns (coordinates p) i) : x + 32 < p.W := by
  have hm := x_margin p hi 0
  change p.x i + readLength p 0 + 64 < p.W at hm
  simp only [specialColumns, List.mem_cons, List.not_mem_nil, or_false] at hx
  change x = p.x i - 2 ∨ x = p.x i + 4 ∨ x = p.x i + 6 ∨
    x = p.x i + 8 ∨ x = p.x i + 12 at hx
  omega

private theorem gateFixedSegments_box (p : Scales.Parameters) (i : ℕ) (hi : i < p.axes) :
    AllBox p (gateFixedSegments (coordinates p) i) := by
  have hx : (coordinates p).x i + 64 < p.W := by
    have h := x_margin p hi 0
    change p.x i + 64 < p.W
    omega
  have hy : (coordinates p).depth 1 + 64 < p.H := readDepth_add_lt_H p 1
  have hn : (coordinates p).depth 2 + 64 < p.H := readDepth_add_lt_H p 2
  have hH : 64 < p.H := by have := readDepth_add_lt_H p 0; omega
  dsimp only [gateFixedSegments]
  simp only [List.append_assoc]
  apply box_append p
  · apply box_map p
    intro col hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    apply box_side_segment p .lower <;> omega
  · apply box_append p
    · intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl
      · apply box_side_point p .lower <;> omega
      · apply box_side_segment p .lower <;> omega
      · apply box_side_point p .lower <;> omega
      · apply box_side_point p .lower <;> omega
    · split
      · apply box_map p
        intro col hc
        have hcol := specialColumn_le p hi hc
        apply box_side_point p .lower <;> omega
      · exact fun _ h => False.elim (List.not_mem_nil h)

private theorem pageColumn_le (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) (side : Side) {x : ℕ}
    (hx : x ∈ pageColumns l (coordinates p) side) : x ≤ p.W := by
  simp only [pageColumns, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hx
  rcases hx with rfl | rfl | hx | hx
  · exact Nat.zero_le _
  · rfl
  · obtain ⟨e, he, hx⟩ := List.mem_flatMap.mp hx
    have hb := endpoint_port l p hl ha (List.mem_of_mem_filter he)
    have hm := x_margin p hb e.level
    obtain ⟨hf, hr⟩ := auxiliary_margin p e hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    change x = _ ∨ x = p.x e.port ∨ x = _ at hx
    omega
  · split at hx
    · obtain ⟨i, hi, hx⟩ := List.mem_flatMap.mp hx
      have hb := center_port l p hl ha hi
      rcases List.mem_cons.mp hx with rfl | hx
      · have hm := x_margin p hb 0
        change p.x i ≤ p.W
        omega
      · have hm := specialColumn_le p hb hx
        omega
    · exact False.elim (List.not_mem_nil hx)

private theorem auxiliaryColumn_le (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) {x : ℕ}
    (hx : x ∈ originalAuxiliary l (coordinates p)) : x ≤ p.W := by
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨e, he, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨hf, hr⟩ := auxiliary_margin p e (endpoint_port l p hl ha he)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    omega
  · obtain ⟨i, hi, hx⟩ := List.mem_flatMap.mp hx
    have h := specialColumn_le p (center_port l p hl ha hi) hx
    omega

private theorem axisColumn_le (l : PortLayout) (p : Scales.Parameters)
    (ha : l.portCount ≤ p.axes) {x : ℕ} (hx : x ∈ axisColumns l (coordinates p)) : x ≤ p.W := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  have hi' := List.mem_range.mp hi
  have hm := x_margin p (show i < p.axes by omega) 0
  change p.x i ≤ p.W
  omega

private theorem streetColumn_le (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) {x : ℕ}
    (hx : x ∈ streetColumns l (coordinates p)) : x ≤ p.W := by
  simp only [streetColumns, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hx
  rcases hx with rfl | rfl | hx | hx
  · exact Nat.zero_le _
  · rfl
  · exact axisColumn_le l p ha hx
  · exact auxiliaryColumn_le l p hl ha hx

private theorem adjacentPair_mem {xs : List ℕ} {a b : ℕ} (hab : (a, b) ∈ adjacentPairs xs) :
    a ∈ xs ∧ b ∈ xs := by
  obtain ⟨x, hx, hab⟩ := List.mem_flatMap.mp hab
  obtain ⟨y, hy, hab⟩ := List.mem_filterMap.mp hab
  split at hab
  · simp only [Option.some.injEq, Prod.mk.injEq] at hab
    rcases hab with ⟨rfl, rfl⟩
    exact ⟨hx, hy⟩
  · cases hab

private theorem wideFixed_box (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) (side : Side) :
    AllBox p (wideFixed l (coordinates p) side) := by
  dsimp only [wideFixed]
  apply box_flatMap p
  rintro ⟨a, b⟩ hab
  dsimp only
  have hc := adjacentPair_mem hab
  have hca := pageColumn_le l p hl ha side hc.1
  have hcb := pageColumn_le l p hl ha side hc.2
  split
  · intro s hs
    obtain ⟨y, hy, hs⟩ := List.mem_filterMap.mp hs
    have hrow := workingRow_le l p hy
    split at hs
    · cases hs
    · simp only [Option.some.injEq] at hs
      subst s
      apply box_side_point p side <;> omega
  · exact fun _ h => False.elim (List.not_mem_nil h)

private theorem interiorFixed_box (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) :
    AllBox p (interiorFixed l (coordinates p)) := by
  dsimp only [interiorFixed]
  simp only [List.append_assoc]
  refine box_append p (box_flatMap p (fun e he =>
    endpointFixedSegments_box l p e (endpoint_port l p hl ha he))) ?_
  refine box_append p (box_flatMap p (fun i hi =>
    gateFixedSegments_box p i (center_port l p hl ha hi))) ?_
  refine box_append p (wideFixed_box l p hl ha .upper) ?_
  refine box_append p (wideFixed_box l p hl ha .lower) ?_
  apply box_map p
  intro x hx
  apply box_point p (auxiliaryColumn_le l p hl ha hx)
  have h := central_marker_bounds p
  change p.D ≤ p.H
  omega

private theorem guardColumn_le (l : PortLayout) (p : Scales.Parameters)
    {ss : List Segment} (hb : AllBox p ss) {x : ℕ}
    (hx : x ∈ guardColumns l (coordinates p) ss) : x ≤ p.W := by
  obtain ⟨s, hs, hx⟩ := List.mem_filterMap.mp hx
  split at hx
  · simp only [Option.some.injEq] at hx
    subst x
    exact (hb s hs).1
  · cases hx

private theorem shiftPoint_box (p : Scales.Parameters) (guards rows : List ℕ) (s : Segment)
    (hs : Box p s) : Box p (shiftPoint guards rows s) := by
  unfold shiftPoint
  split
  · apply box_point p <;> obtain ⟨_, _, _, _⟩ := hs <;> omega
  · exact hs

private theorem markedInterior_box (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) :
    AllBox p (markedInterior l (coordinates p)) := by
  let base := interiorFixed l (coordinates p)
  let guards := guardColumns l (coordinates p) (frame (coordinates p) ++ base)
  let shifted := if guards.any (fun x => guards.contains (x + 1)) then
    base.map (shiftPoint guards (streetRows (coordinates p))) else base
  let aux := (streetColumns l (coordinates p)).filter fun x =>
    decide (x ≠ 0 ∧ x ≠ (coordinates p).W) && !((axisColumns l (coordinates p)).contains x)
  let marked := shifted ++ aux.flatMap (fun x =>
    [point x ((coordinates p).D - 2), point x ((coordinates p).D + 2)])
  have hbase : AllBox p base := interiorFixed_box l p hl ha
  have hshift : AllBox p shifted := by
    dsimp only [shifted]
    split
    · exact box_map p (fun s hs => shiftPoint_box p _ _ s (hbase s hs))
    · exact hbase
  have hcenter := central_marker_bounds p
  have hmarked : AllBox p marked := by
    apply box_append p hshift
    apply box_flatMap p
    intro x hx
    have hcol := streetColumn_le l p hl ha (List.mem_of_mem_filter hx)
    intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> apply box_point p hcol <;> simp only [coordinates] <;> omega
  change AllBox p ((marked ++ _) ++ _)
  apply box_append p
  · apply box_append p hmarked
    apply box_map p
    intro x hx
    apply box_point p (guardColumn_le l p (box_append p (frame_box p) hmarked) hx)
    change p.D - 4 ≤ p.H
    omega
  · apply box_flatMap p
    intro i hi
    have hm := x_margin p (center_port l p hl ha hi) 0
    intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> apply box_point p <;>
      simp only [Coordinates.x, coordinates, Scales.Parameters.x] at hm ⊢ <;> omega

private theorem endpointSegments_box (p : Scales.Parameters) (state : SignalState) (e : Endpoint)
    (he : e.port < p.axes) : AllBox p (endpointSegments (coordinates p) state e) := by
  have hx : (coordinates p).x e.port + 64 < p.W := by
    have h := x_margin p he 0
    change p.x e.port + 64 < p.W
    omega
  have hy : (coordinates p).depth e.level + 64 < p.H := readDepth_add_lt_H p e.level
  have hinput := Bool.toNat_le (if e.side = .upper then state.axes.getD e.port false
    else !(state.axes.getD e.port false))
  have hreceiving := Bool.toNat_le (if e.inward then state.internal.getD e.internal false
    else !(state.internal.getD e.internal false))
  have hbit := Bool.toNat_le (state.internal.getD e.internal false)
  have hnbit := Bool.toNat_le (!(state.internal.getD e.internal false))
  intro s hs
  dsimp only [endpointSegments] at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · apply box_side_segment p e.side <;> omega
  · apply box_side_segment p e.side
    · cases e.inward <;> simp only [inward, Bool.false_eq_true, ite_false, ite_true] <;> omega
    · omega
    · cases e.inward <;> simp only [inward, Bool.false_eq_true, ite_false, ite_true] <;> omega
    · omega

private theorem tripleSignal_box (p : Scales.Parameters) (state : SignalState) (g : Placement)
    (hg : g.left + 1 < p.axes) : AllBox p (tripleSignal (coordinates p) state g) := by
  have hx : (coordinates p).x (g.left + 1) + 64 < p.W := by
    have h := x_margin p hg 0
    change p.x (g.left + 1) + 64 < p.W
    omega
  have hy : (coordinates p).depth 1 + 64 < p.H := readDepth_add_lt_H p 1
  have hleft := Bool.toNat_le (state.internal.getD g.internal false)
  have hright := Bool.toNat_le (state.internal.getD (g.internal + 2) false)
  have haxis := Bool.toNat_le (state.axes.getD (g.left + 1) false)
  have hshort : (if state.internal.getD (g.internal + 1) false then 6 else 1) ≤ (6 : ℕ) := by
    split <;> omega
  dsimp only [tripleSignal, gateSegments]
  cases g.gate with
  | none => exact fun _ h => False.elim (List.not_mem_nil h)
  | some kind =>
    intro s hs
    simp only [Option.elim_some, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl <;> apply box_side_segment p .lower <;> omega

/-- Every fixed physical segment stays inside the actual allocated rectangle. -/
theorem fixedSegments_contains_bounds (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) {s : Segment}
    (hs : s ∈ l.fixedSegments p) {q : ℕ × ℕ} (hq : s.Contains q) :
    q.1 ≤ p.W ∧ q.2 ≤ p.H := by
  have hb := box_append p (frame_box p) (markedInterior_box l p hl ha) s hs
  simp only [Box, Segment.Contains] at hb hq
  omega

/-- Every physical signal segment stays in the rectangle, for arbitrary physical bits. -/
theorem signalSegments_contains_bounds (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) (state : SignalState) {s : Segment}
    (hs : s ∈ l.signalSegments p state) {q : ℕ × ℕ} (hq : s.Contains q) :
    q.1 ≤ p.W ∧ q.2 ≤ p.H := by
  have hb : Box p s := by
    rcases List.mem_append.mp hs with hs | hs
    · obtain ⟨e, he, hs⟩ := List.mem_flatMap.mp hs
      exact endpointSegments_box p state e (endpoint_port l p hl ha he) s hs
    · obtain ⟨g, hg, hs⟩ := List.mem_flatMap.mp hs
      cases hgate : g.gate with
      | none => simp [tripleSignal, hgate] at hs
      | some kind =>
        have hport := (placement_ports l p hl ha hg).2.2
        exact tripleSignal_box p state g (hport (by simp [hgate])) s hs
  simp only [Box, Segment.Contains] at hb hq
  omega

/-- The complete actual fixed/signal hole union is inside the emitted rectangle. -/
theorem encodedSegments_contains_bounds (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) (state : SignalState) {s : Segment}
    (hs : s ∈ l.encodedSegments p state) {q : ℕ × ℕ} (hq : s.Contains q) :
    q.1 ≤ p.W ∧ q.2 ≤ p.H := by
  rcases List.mem_append.mp hs with hs | hs
  · exact l.fixedSegments_contains_bounds p hl ha hs hq
  · exact l.signalSegments_contains_bounds p hl ha state hs hq

end PushPuzzle.PushS.PortLayout
