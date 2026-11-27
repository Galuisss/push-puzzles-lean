/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortHoleBudget
public import PushS.PortSegmentBounds
import all PushS.PortSegments
import all PushS.PortSegmentBounds
import all PushS.PortHoleBudget

/-!
# Horizontal margins of the actual central markers

The ordinary streets stay within one branch length of their port axes. Separator columns
also include midpoints of adjacent streets and the emitter's one-cell even rounding.
Their half-spacing margins place all central acceptance markers beyond the whole-board
interior-hole budget.
-/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS.Reduction

private def ColumnMargin (p : Scales.Parameters) (x : ℕ) (slack : ℕ := 1) : Prop :=
  p.D ≤ 2 * x + p.L p.levels + slack ∧
    p.D + 2 * x ≤ 2 * p.W + p.L p.levels + slack

private def ColumnInset (p : Scales.Parameters) (x : ℕ) : Prop :=
  p.D ≤ x + p.L p.levels ∧ x + p.D ≤ p.W + p.L p.levels

private def SegmentMargins (p : Scales.Parameters) (s : Segment) (slack : ℕ := 1) : Prop :=
  ColumnMargin p s.start.1 slack ∧ ColumnMargin p s.finish.1 slack

private def AllMargins (p : Scales.Parameters) (ss : List Segment) (slack : ℕ := 1) : Prop :=
  ∀ s ∈ ss, SegmentMargins p s slack

private theorem coordinate_x (p : Scales.Parameters) (i : ℕ) :
    (coordinates p).x i = p.x i := rfl

private theorem axis_margins (p : Scales.Parameters) {i : ℕ} (hi : i < p.axes) :
    p.D ≤ p.x i ∧ p.x i + p.D ≤ p.W := by
  have hl := Nat.mul_le_mul_right p.D (show 1 ≤ i + 1 by omega)
  have hr := Nat.mul_le_mul_right p.D (show i + 2 ≤ p.axes + 1 by omega)
  simp only [Scales.Parameters.x, Scales.Parameters.W, Nat.add_mul, Nat.one_mul] at *
  omega

private theorem length_floor (p : Scales.Parameters) : 64 ≤ p.L p.levels := by
  have h := readLength_ge p p.levels_pos le_rfl
  rw [readLength_eq p p.levels_pos le_rfl] at h
  omega

private theorem near_axis_inset (p : Scales.Parameters) {i x : ℕ} (hi : i < p.axes)
    (hl : p.x i ≤ x + p.L p.levels) (hr : x ≤ p.x i + p.L p.levels) :
    ColumnInset p x := by
  obtain ⟨ha, hb⟩ := axis_margins p hi
  dsimp only [ColumnInset]
  omega

private theorem inset_margin (p : Scales.Parameters) {x : ℕ} (hx : ColumnInset p x) :
    ColumnMargin p x := by
  have hd := p.outer_distance
  dsimp only [ColumnInset, ColumnMargin] at *
  omega

private theorem near_axis_margin (p : Scales.Parameters) {i x : ℕ} (hi : i < p.axes)
    (hl : p.x i ≤ x + p.L p.levels) (hr : x ≤ p.x i + p.L p.levels) :
    ColumnMargin p x := inset_margin p (near_axis_inset p hi hl hr)

private theorem margin_segment (p : Scales.Parameters) {x y u v : ℕ}
    (hx : ColumnMargin p x) (hu : ColumnMargin p u) :
    SegmentMargins p (segment x y u v) := by
  simp only [SegmentMargins, segment, ColumnMargin] at *
  omega

private theorem margin_point (p : Scales.Parameters) {x y : ℕ} (hx : ColumnMargin p x) :
    SegmentMargins p (point x y) := margin_segment p hx hx

private theorem margins_append (p : Scales.Parameters) {ss tt : List Segment}
    (hs : AllMargins p ss) (ht : AllMargins p tt) : AllMargins p (ss ++ tt) := by
  intro s h
  exact (List.mem_append.mp h).elim (hs s) (ht s)

private theorem margins_map (p : Scales.Parameters) {α : Type} {xs : List α}
    {f : α → Segment} (h : ∀ x ∈ xs, SegmentMargins p (f x)) : AllMargins p (xs.map f) := by
  intro s hs
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hs
  exact h x hx

private theorem margins_flatMap (p : Scales.Parameters) {α : Type} {xs : List α}
    {f : α → List Segment} (h : ∀ x ∈ xs, AllMargins p (f x)) :
    AllMargins p (xs.flatMap f) := by
  intro s hs
  obtain ⟨x, hx, hs⟩ := List.mem_flatMap.mp hs
  exact h x hx s hs

private theorem auxiliary_near_axis (p : Scales.Parameters) (e : Endpoint) :
    let (f, r) := auxiliary (coordinates p) e
    p.x e.port ≤ f + p.L p.levels ∧ f ≤ p.x e.port + p.L p.levels ∧
      p.x e.port ≤ r + p.L p.levels ∧ r ≤ p.x e.port + p.L p.levels := by
  have hl := readLength_le_last p e.level
  have hx := readLength_add_lt_x p e.port e.level
  have hm := length_floor p
  dsimp only [auxiliary, Coordinates.x, Coordinates.length, coordinates]
  change _ ≤ _ ∧ _ ≤ _ ∧ _ ≤ _ ∧ _ ≤ _
  change readLength p e.level + 64 < (e.port + 1) * p.D at hx
  change readLength p e.level ≤ p.L p.levels at hl
  dsimp only [readLength] at hl hx
  cases e.inward <;> simp only [outward, inward, Bool.false_eq_true, ite_false, ite_true]
  all_goals dsimp only [Scales.Parameters.x]; omega

private theorem endpointFixed_margins (l : PortLayout) (p : Scales.Parameters) (e : Endpoint)
    (he : e.port < p.axes) : AllMargins p (endpointFixedSegments l (coordinates p) e) := by
  have hn := auxiliary_near_axis p e
  have hx := readLength_add_lt_x p e.port e.level
  have hL := length_floor p
  let x := p.x e.port
  let f := (auxiliary (coordinates p) e).1
  let r := (auxiliary (coordinates p) e).2
  change x ≤ f + p.L p.levels ∧ f ≤ x + p.L p.levels ∧
    x ≤ r + p.L p.levels ∧ r ≤ x + p.L p.levels at hn
  have hf := near_axis_margin p he hn.1 hn.2.1
  have hr := near_axis_margin p he hn.2.2.1 hn.2.2.2
  have hmid : ColumnMargin p ((f + x) / 2) := near_axis_margin p he (by omega) (by omega)
  have hshort : ColumnMargin p (inward x e.inward 1) := by
    apply near_axis_margin p he <;> cases e.inward <;>
      simp only [inward, Bool.false_eq_true, ite_false, ite_true] <;> omega
  have hlong : ColumnMargin p (inward f e.inward 1) := by
    have hlen := readLength_le_last p e.level
    dsimp only [readLength] at hlen hx
    apply near_axis_margin p he
    all_goals
      dsimp only [f, auxiliary, Coordinates.x, Coordinates.length, coordinates]
      cases e.inward <;> simp only [inward, outward, Bool.false_eq_true, ite_false, ite_true]
      all_goals dsimp only [Scales.Parameters.x] at *; omega
  have hfar : ColumnMargin p (outward x e.inward 1) := by
    apply near_axis_margin p he <;> cases e.inward <;>
      simp only [outward, Bool.false_eq_true, ite_false, ite_true] <;> omega
  dsimp only [endpointFixedSegments]
  simp only [List.append_assoc]
  apply margins_append p
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact margin_segment p hf hf
    · exact margin_segment p hr hr
    · exact margin_segment p hlong hfar
  · apply margins_append p
    · apply margins_flatMap p
      intro v _
      apply margins_append p
      · split
        · intro s hs
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
          subst s
          exact margin_point p hmid
        · exact fun _ h => False.elim (List.not_mem_nil h)
      · split
        · intro s hs
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
          subst s
          exact margin_point p hshort
        · exact fun _ h => False.elim (List.not_mem_nil h)
    · split
      · intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        · exact margin_point p hf
        · exact margin_point p hr
      · exact fun _ h => False.elim (List.not_mem_nil h)

private theorem specialColumn_inset (p : Scales.Parameters) {i x : ℕ} (hi : i < p.axes)
    (hx : x ∈ specialColumns (coordinates p) i) : ColumnInset p x := by
  have hL := length_floor p
  have ha := readLength_add_lt_x p i 0
  simp only [specialColumns, List.mem_cons, List.not_mem_nil, or_false] at hx
  change x = p.x i - 2 ∨ x = p.x i + 4 ∨ x = p.x i + 6 ∨
    x = p.x i + 8 ∨ x = p.x i + 12 at hx
  apply near_axis_inset p hi <;> omega

private theorem gateFixed_margins (p : Scales.Parameters) {i : ℕ} (hi : i < p.axes) :
    AllMargins p (gateFixedSegments (coordinates p) i) := by
  have hL := length_floor p
  have ha := readLength_add_lt_x p i 0
  have hn : ∀ x, p.x i ≤ x + p.L p.levels → x ≤ p.x i + p.L p.levels →
      ColumnMargin p x := fun _ => near_axis_margin p hi
  dsimp only [gateFixedSegments]
  simp only [coordinate_x, List.append_assoc]
  apply margins_append p
  · apply margins_map p
    intro col hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    have hcol : ColumnMargin p col := hn col (by omega) (by omega)
    exact margin_segment p hcol hcol
  · apply margins_append p
    · intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl
      all_goals first
        | exact margin_point p (hn _ (by omega) (by omega))
        | exact margin_segment p (hn _ (by omega) (by omega)) (hn _ (by omega) (by omega))
    · split
      · apply margins_map p
        intro col hc
        exact margin_point p (inset_margin p (specialColumn_inset p hi hc))
      · exact fun _ h => False.elim (List.not_mem_nil h)

private theorem pageColumn_shape (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) (side : Side) {x : ℕ}
    (hx : x ∈ pageColumns l (coordinates p) side) :
    x = 0 ∨ x = p.W ∨ ColumnInset p x := by
  simp only [pageColumns, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hx
  rcases hx with rfl | rfl | hx | hx
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · obtain ⟨e, he, hx⟩ := List.mem_flatMap.mp hx
    have hb := endpoint_port l p hl ha (List.mem_of_mem_filter he)
    have hn := auxiliary_near_axis p e
    simp only [List.mem_cons, List.not_mem_nil, or_false, coordinate_x] at hx
    apply Or.inr ∘ Or.inr
    rcases hx with rfl | rfl | rfl
    · exact near_axis_inset p hb hn.1 hn.2.1
    · exact near_axis_inset p hb (by omega) (by omega)
    · exact near_axis_inset p hb hn.2.2.1 hn.2.2.2
  · split at hx
    · obtain ⟨i, hi, hx⟩ := List.mem_flatMap.mp hx
      have hb := center_port l p hl ha hi
      apply Or.inr ∘ Or.inr
      simp only [coordinate_x] at hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact near_axis_inset p hb (by omega) (by omega)
      · exact specialColumn_inset p hb hx
    · cases hx

private theorem adjacentPair_mem {xs : List ℕ} {a b : ℕ} (hab : (a, b) ∈ adjacentPairs xs) :
    a ∈ xs ∧ b ∈ xs ∧ a < b := by
  obtain ⟨x, hx, hab⟩ := List.mem_flatMap.mp hab
  obtain ⟨y, hy, hab⟩ := List.mem_filterMap.mp hab
  split at hab
  · rename_i hcond
    simp only [Option.some.injEq, Prod.mk.injEq] at hab
    rcases hab with ⟨rfl, rfl⟩
    exact ⟨hx, hy, hcond.1⟩
  · cases hab

private theorem page_midpoint_margin (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) (side : Side) {a b : ℕ}
    (hab : (a, b) ∈ adjacentPairs (pageColumns l (coordinates p) side)) :
    ColumnMargin p ((a + b) / 2) := by
  obtain ⟨ha', hb', hab⟩ := adjacentPair_mem hab
  have hsa := pageColumn_shape l p hl ha side ha'
  have hsb := pageColumn_shape l p hl ha side hb'
  have hwa := pageColumn_le l p hl ha side ha'
  have hwb := pageColumn_le l p hl ha side hb'
  have hw := (axis_margins p (show 0 < p.axes by have := p.axes_pos; omega)).2
  dsimp only [ColumnInset, ColumnMargin] at *
  rcases hsa with hsa | hsa | hsa <;> rcases hsb with hsb | hsb | hsb <;> omega

private theorem wideFixed_margins (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) (side : Side) :
    AllMargins p (wideFixed l (coordinates p) side) := by
  apply margins_flatMap p
  intro ab hab
  dsimp only
  split
  · intro s hs
    obtain ⟨y, _, hs⟩ := List.mem_filterMap.mp hs
    split at hs
    · cases hs
    · simp only [Option.some.injEq] at hs
      subst s
      exact margin_point p (page_midpoint_margin l p hl ha side hab)
  · exact fun _ h => False.elim (List.not_mem_nil h)

private theorem originalAuxiliary_inset (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) {x : ℕ}
    (hx : x ∈ originalAuxiliary l (coordinates p)) : ColumnInset p x := by
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨e, he, hx⟩ := List.mem_flatMap.mp hx
    have hb := endpoint_port l p hl ha he
    have hn := auxiliary_near_axis p e
    rcases List.mem_cons.mp hx with rfl | hx
    · exact near_axis_inset p hb hn.1 hn.2.1
    · have heq : x = (auxiliary (coordinates p) e).2 := by exact List.mem_singleton.mp hx
      subst x
      exact near_axis_inset p hb hn.2.2.1 hn.2.2.2
  · obtain ⟨i, hi, hx⟩ := List.mem_flatMap.mp hx
    exact specialColumn_inset p (center_port l p hl ha hi) hx

private theorem interiorFixed_margins (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) :
    AllMargins p (interiorFixed l (coordinates p)) := by
  unfold interiorFixed
  apply margins_append p
  · apply margins_append p
    · apply margins_append p
      · apply margins_append p
        · exact margins_flatMap p fun e he => endpointFixed_margins l p e (endpoint_port l p hl ha he)
        · exact margins_flatMap p fun i hi => gateFixed_margins p (center_port l p hl ha hi)
      · exact wideFixed_margins l p hl ha .upper
    · exact wideFixed_margins l p hl ha .lower
  · exact margins_map p fun _ hx => margin_point p
      (inset_margin p (originalAuxiliary_inset l p hl ha hx))

private theorem streetColumn_inset (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) {x : ℕ}
    (hx : x ∈ streetColumns l (coordinates p)) (hx0 : x ≠ 0) (hxW : x ≠ p.W) :
    ColumnInset p x := by
  simp only [streetColumns, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hx
  rcases hx with rfl | rfl | hx | hx
  · exact False.elim (hx0 rfl)
  · exact False.elim (hxW rfl)
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have hb := List.mem_range.mp hi
    exact near_axis_inset p (i := i) (by omega) (by change p.x i ≤ p.x i + _; omega)
      (by change p.x i ≤ p.x i + _; omega)
  · exact originalAuxiliary_inset l p hl ha hx

private theorem margin_weaken (p : Scales.Parameters) {s : Segment} {a b : ℕ}
    (hs : SegmentMargins p s a) (hab : a ≤ b) : SegmentMargins p s b := by
  simp only [SegmentMargins, ColumnMargin] at *
  omega

private theorem margins_append_at (p : Scales.Parameters) {ss tt : List Segment} {slack : ℕ}
    (hs : AllMargins p ss slack) (ht : AllMargins p tt slack) : AllMargins p (ss ++ tt) slack := by
  intro s h
  exact (List.mem_append.mp h).elim (hs s) (ht s)

private theorem shiftPoint_margins (p : Scales.Parameters) (guards rows : List ℕ) {s : Segment}
    (hs : SegmentMargins p s) : SegmentMargins p (shiftPoint guards rows s) 3 := by
  unfold shiftPoint
  split
  · simp only [SegmentMargins, point, segment, ColumnMargin, Nat.min_self, Nat.max_self] at *
    omega
  · exact margin_weaken p hs (by omega)

private theorem guardColumns_margins (l : PortLayout) (p : Scales.Parameters)
    {ss : List Segment} {slack : ℕ} (hs : AllMargins p ss slack) {x : ℕ}
    (hx : x ∈ guardColumns l (coordinates p) (frame (coordinates p) ++ ss)) :
    ColumnMargin p x slack := by
  have hD := central_marker_bounds p
  have hW : 0 < (coordinates p).W := by
    change 0 < p.W
    have := (axis_margins p (show 0 < p.axes by have := p.axes_pos; omega)).2
    omega
  have hH : 0 < (coordinates p).H := by change 0 < p.H; omega
  rw [guardColumns_frame_append l (coordinates p) ss hW hH] at hx
  obtain ⟨s, hss, hx⟩ := List.mem_filterMap.mp hx
  split at hx
  · have he : s.start.1 = x := Option.some.inj hx
    exact he ▸ (hs s hss).1
  · cases hx

private theorem markedInterior_margins (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) :
    AllMargins p (markedInterior l (coordinates p)) 3 := by
  let c := coordinates p
  let base := interiorFixed l c
  let guards := guardColumns l c (frame c ++ base)
  let shifted := if guards.any (fun x => guards.contains (x + 1)) then
    base.map (shiftPoint guards (streetRows c)) else base
  let aux := (streetColumns l c).filter fun x =>
    decide (x ≠ 0 ∧ x ≠ c.W) && !((axisColumns l c).contains x)
  let marked := shifted ++ aux.flatMap fun x => [point x (c.D - 2), point x (c.D + 2)]
  have hbase := interiorFixed_margins l p hl ha
  have hshift : AllMargins p shifted 3 := by
    intro s hs
    dsimp only [shifted] at hs
    split at hs
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hs
      exact shiftPoint_margins p guards (streetRows c) (hbase u hu)
    · exact margin_weaken p (hbase s hs) (by omega)
  have hmarked : AllMargins p marked 3 := by
    apply margins_append_at p hshift
    intro s hs
    obtain ⟨x, hx, hs⟩ := List.mem_flatMap.mp hs
    obtain ⟨hx, hcond⟩ := List.mem_filter.mp hx
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
    have hcond' : x ≠ 0 ∧ x ≠ p.W := hcond.1
    have hm := inset_margin p (streetColumn_inset l p hl ha hx hcond'.1 hcond'.2)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> exact margin_weaken p (margin_point p hm) (by omega)
  change AllMargins p (marked ++
    (guardColumns l c (frame c ++ marked)).map (fun x => point x (c.D - 4)) ++
    (centers l).flatMap (fun i => [point (c.x i + 2) (c.D + 4), point (c.x i + 10) (c.D + 4)])) 3
  apply margins_append_at p
  · apply margins_append_at p hmarked
    intro s hs
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hs
    have hm := guardColumns_margins l p hmarked hx
    simpa only [SegmentMargins, point, segment, Nat.min_self, Nat.max_self] using And.intro hm hm
  · intro s hs
    obtain ⟨i, hi, hs⟩ := List.mem_flatMap.mp hs
    have hb := center_port l p hl ha hi
    have hL := length_floor p
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · have hm : ColumnMargin p (c.x i + 2) := near_axis_margin p hb
        (by change p.x i ≤ p.x i + 2 + p.L p.levels; omega)
        (by change p.x i + 2 ≤ p.x i + p.L p.levels; omega)
      exact margin_weaken p (margin_point p hm) (by omega)
    · have hm : ColumnMargin p (c.x i + 10) := near_axis_margin p hb
        (by change p.x i ≤ p.x i + 10 + p.L p.levels; omega)
        (by change p.x i + 10 ≤ p.x i + p.L p.levels; omega)
      exact margin_weaken p (margin_point p hm) (by omega)

/-- Every actual fixed hole off the frame retains the separator's horizontal half-spacing
margins, including the emitter's possible one-cell even rounding. -/
theorem fixedSegments_interior_column_margins (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes)
    {q : PushFS.Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.fixedSegments p))
    (hf : q ∉ Boundary.frame) :
    p.D ≤ 2 * q.1.val + p.L p.levels + 3 ∧
      p.D + 2 * q.1.val ≤ 2 * p.W + p.L p.levels + 3 := by
  obtain ⟨s, hs, hq⟩ := (SegmentRecipe.mem_holes _ q).mp hq
  rcases List.mem_append.mp hs with hs | hs
  · exact False.elim (hf (frame_contains (coordinates p) q ⟨s, hs, hq⟩))
  · have hm := markedInterior_margins l p hl ha s hs
    simp only [Segment.Contains] at hq
    dsimp only [SegmentMargins, ColumnMargin] at hm
    omega

end PushPuzzle.PushS.PortLayout
