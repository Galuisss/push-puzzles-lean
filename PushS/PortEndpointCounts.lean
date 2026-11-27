/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.SegmentCard
import all PushS.PortSegments

/-!
# Inventories of the actual ordinary endpoint segments

The first emitted segment is the axis-near trace, and the second is the horizontal-near
trace. Their integer unions are disjoint at every allocated positive working level.
-/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS.Reduction SegmentRecipe

private theorem horizontal_card (x u y : ℕ) :
    (pointHoles [segment x y u y]).card = max x u - min x u + 1 := by
  simp only [segment, Nat.min_self, Nat.max_self]
  rw [pointHoles_horizontal_card]
  omega

private theorem vertical_card (x y v : ℕ) :
    (pointHoles [segment x y x v]).card = max y v - min y v + 1 := by
  simp only [segment, Nat.min_self, Nat.max_self]
  rw [pointHoles_vertical_card]
  omega

private theorem horizontal_mem (x u y : ℕ) (q : ℕ × ℕ) :
    q ∈ pointHoles [segment x y u y] ↔ q.2 = y ∧ min x u ≤ q.1 ∧ q.1 ≤ max x u := by
  simp only [segment, Nat.min_self, Nat.max_self, mem_pointHoles_horizontal]
  omega

private theorem vertical_mem (x y v : ℕ) (q : ℕ × ℕ) :
    q ∈ pointHoles [segment x y x v] ↔ q.1 = x ∧ min y v ≤ q.2 ∧ q.2 ≤ max y v := by
  simp only [segment, Nat.min_self, Nat.max_self, mem_pointHoles_vertical]
  omega

/-- The actual axis-near trace contains two holes plus its endpoint input bit. -/
theorem endpointSegments_axis_card (p : Scales.Parameters) (state : SignalState) (e : Endpoint)
    (hj : 1 ≤ e.level) (hm : e.level ≤ p.levels) :
    (pointHoles ((endpointSegments (coordinates p) state e).take 1)).card =
      2 + (if e.side = .upper then state.axes.getD e.port false
        else !(state.axes.getD e.port false)).toNat := by
  have hlow := readDepth_ge p hj hm
  have hhigh := readDepth_add_lt_H p e.level
  have hbit := Bool.toNat_le (if e.side = .upper then state.axes.getD e.port false
    else !(state.axes.getD e.port false))
  dsimp only [endpointSegments]
  simp only [List.take_succ_cons, List.take_zero]
  rw [vertical_card]
  change 16384 ≤ (coordinates p).depth e.level at hlow
  change (coordinates p).depth e.level + 64 < p.H at hhigh
  cases hs : e.side <;> simp [onSide, hs, coordinates] at hbit hlow hhigh ⊢ <;> omega

/-- The actual horizontal-near trace contains one hole plus its receiving bit. -/
theorem endpointSegments_horizontal_card (p : Scales.Parameters) (state : SignalState)
    (e : Endpoint) :
    (pointHoles ((endpointSegments (coordinates p) state e).drop 1)).card =
      1 + (if e.inward then state.internal.getD e.internal false
        else !(state.internal.getD e.internal false)).toNat := by
  have hx := readLength_add_lt_x p e.port 0
  have hbit := Bool.toNat_le (if e.inward then state.internal.getD e.internal false
    else !(state.internal.getD e.internal false))
  dsimp only [endpointSegments]
  simp only [List.drop_succ_cons, List.drop_zero]
  rw [horizontal_card]
  change readLength p 0 + 64 < (coordinates p).x e.port at hx
  cases hd : e.inward <;> simp [inward, hd] at hbit ⊢ <;> omega

/-- The two actually emitted endpoint traces have no shared hole. -/
theorem endpointSegments_disjoint (p : Scales.Parameters) (state : SignalState) (e : Endpoint) :
    Disjoint (pointHoles ((endpointSegments (coordinates p) state e).take 1))
      (pointHoles ((endpointSegments (coordinates p) state e).drop 1)) := by
  have hx := readLength_add_lt_x p e.port 0
  dsimp only [endpointSegments]
  simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero]
  apply Finset.disjoint_left.mpr
  intro q hqv hqh
  have hv := (vertical_mem _ _ _ q).mp hqv
  have hh := (horizontal_mem _ _ _ q).mp hqh
  change readLength p 0 + 64 < (coordinates p).x e.port at hx
  cases hd : e.inward <;> simp [inward, hd] at hh <;> omega

/-- Exact cardinality of one actual ordinary endpoint's complete signal-hole union. -/
theorem endpointSegments_card (p : Scales.Parameters) (state : SignalState) (e : Endpoint)
    (hj : 1 ≤ e.level) (hm : e.level ≤ p.levels) :
    (pointHoles (endpointSegments (coordinates p) state e)).card =
      3 + (if e.side = .upper then state.axes.getD e.port false
        else !(state.axes.getD e.port false)).toNat +
      (if e.inward then state.internal.getD e.internal false
        else !(state.internal.getD e.internal false)).toNat := by
  rw [← List.take_append_drop 1 (endpointSegments (coordinates p) state e),
    pointHoles_append, Finset.card_union_of_disjoint (endpointSegments_disjoint p state e),
    endpointSegments_axis_card p state e hj hm, endpointSegments_horizontal_card]
  omega

private theorem axis_mem (p : Scales.Parameters) (state : SignalState) (e : Endpoint)
    (q : ℕ × ℕ) : q ∈ pointHoles ((endpointSegments (coordinates p) state e).take 1) ↔
    q.1 = p.x e.port ∧
      min (onSide (coordinates p) e.side (readDepth p e.level))
        (onSide (coordinates p) e.side (readDepth p e.level + 1 +
          (if e.side = .upper then state.axes.getD e.port false
            else !(state.axes.getD e.port false)).toNat)) ≤ q.2 ∧
      q.2 ≤ max (onSide (coordinates p) e.side (readDepth p e.level))
        (onSide (coordinates p) e.side (readDepth p e.level + 1 +
          (if e.side = .upper then state.axes.getD e.port false
            else !(state.axes.getD e.port false)).toNat)) := by
  dsimp only [endpointSegments]
  simp only [List.take_succ_cons, List.take_zero, vertical_mem]
  rfl

private theorem upper_axis_row (p : Scales.Parameters) (state : SignalState) (e : Endpoint)
    (he : e.side = .upper) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles ((endpointSegments (coordinates p) state e).take 1)) : q.2 < p.D := by
  have hmem := (axis_mem p state e q).mp hq
  have hy := readDepth_add_lt_D p e.level
  have hbit := Bool.toNat_le (state.axes.getD e.port false)
  simp only [he, onSide, ite_true] at hmem
  omega

private theorem lower_axis_row (p : Scales.Parameters) (state : SignalState) (e : Endpoint)
    (he : e.side = .lower) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles ((endpointSegments (coordinates p) state e).take 1)) : p.D < q.2 := by
  have hmem := (axis_mem p state e q).mp hq
  have hy := readDepth_add_lt_D p e.level
  have hbit := Bool.toNat_le (!(state.axes.getD e.port false))
  have hH : p.H = 2 * p.D := rfl
  have hside : Side.lower ≠ .upper := by decide
  simp only [he, onSide, hside, ite_false, coordinates] at hmem
  omega

/-- Axis-near holes from opposite pages are separated by the actual central row. -/
private theorem endpointAxes_disjoint (p : Scales.Parameters) (state : SignalState)
    (upper lower : Endpoint) (hu : upper.side = .upper) (hl : lower.side = .lower) :
    Disjoint (pointHoles ((endpointSegments (coordinates p) state upper).take 1))
      (pointHoles ((endpointSegments (coordinates p) state lower).take 1)) := by
  apply Finset.disjoint_left.mpr
  intro q hqu hql
  have hupper := upper_axis_row p state upper hu hqu
  have hlower := lower_axis_row p state lower hl hql
  omega

/-- The actual upper and lower near-axis traces of one ordinary axis contain five holes. -/
theorem endpointAxes_card (p : Scales.Parameters) (state : SignalState) (upper lower : Endpoint)
    (hu : upper.side = .upper) (hl : lower.side = .lower) (hp : upper.port = lower.port)
    (hupper : 1 ≤ upper.level ∧ upper.level ≤ p.levels)
    (hlower : 1 ≤ lower.level ∧ lower.level ≤ p.levels) :
    (pointHoles ((endpointSegments (coordinates p) state upper).take 1 ++
      (endpointSegments (coordinates p) state lower).take 1)).card = 5 := by
  rw [pointHoles_append, Finset.card_union_of_disjoint (endpointAxes_disjoint p state upper lower hu hl),
    endpointSegments_axis_card p state upper hupper.1 hupper.2,
    endpointSegments_axis_card p state lower hlower.1 hlower.2]
  simp only [hu, hl, hp]
  cases state.axes.getD lower.port false <;> decide +kernel

private theorem horizontal_span (p : Scales.Parameters) (state : SignalState) (e : Endpoint)
    {q : ℕ × ℕ} (hq : q ∈ pointHoles ((endpointSegments (coordinates p) state e).drop 1)) :
    p.x e.port - 2 ≤ q.1 ∧ q.1 ≤ p.x e.port + 2 := by
  have hx := readLength_add_lt_x p e.port 0
  have hbit := Bool.toNat_le (if e.inward then state.internal.getD e.internal false
    else !(state.internal.getD e.internal false))
  dsimp only [endpointSegments] at hq
  simp only [List.drop_succ_cons, List.drop_zero, horizontal_mem] at hq
  change readLength p 0 + 64 < (coordinates p).x e.port at hx
  change (coordinates p).x e.port - 2 ≤ q.1 ∧ q.1 ≤ (coordinates p).x e.port + 2
  cases hd : e.inward <;> simp [inward, hd] at hbit hq <;> omega

private theorem axes_separated (p : Scales.Parameters) {i j : ℕ} (hij : i < j) :
    p.x i + 64 < p.x j := by
  have hD := readDepth_add_lt_D p 0
  have hx := Nat.mul_le_mul_right p.D (show i + 1 + 1 ≤ j + 1 by omega)
  simp only [Nat.add_mul, Nat.one_mul] at hx
  simp only [Scales.Parameters.x, Nat.add_mul, Nat.one_mul]
  omega

/-- Horizontal-near holes at distinct declared port indices are disjoint. -/
theorem endpointHorizontals_disjoint (p : Scales.Parameters) (state : SignalState)
    (left right : Endpoint) (hp : left.port < right.port) :
    Disjoint (pointHoles ((endpointSegments (coordinates p) state left).drop 1))
      (pointHoles ((endpointSegments (coordinates p) state right).drop 1)) := by
  apply Finset.disjoint_left.mpr
  intro q hql hqr
  have hl := horizontal_span p state left hql
  have hr := horizontal_span p state right hqr
  have hsep := axes_separated p hp
  omega

/-- The actual complementary endpoints of a WIRE have three horizontal-near holes. -/
theorem endpointHorizontals_card (p : Scales.Parameters) (state : SignalState)
    (left right : Endpoint) (hp : left.port < right.port)
    (hl : left.inward = true) (hr : right.inward = false) (hi : left.internal = right.internal) :
    (pointHoles ((endpointSegments (coordinates p) state left).drop 1 ++
      (endpointSegments (coordinates p) state right).drop 1)).card = 3 := by
  rw [pointHoles_append,
    Finset.card_union_of_disjoint (endpointHorizontals_disjoint p state left right hp),
    endpointSegments_horizontal_card, endpointSegments_horizontal_card]
  simp only [hl, hr, hi, ite_true, Bool.false_eq_true, ite_false]
  cases state.internal.getD right.internal false <;> decide +kernel

private theorem upperLevel_getD_bounds (l : PortLayout) (hl : l.pages.Valid) {i : ℕ}
    (hi : i < l.upperPairs.length) : 1 ≤ l.upperLevel i ∧ l.upperLevel i ≤ l.pages.highest := by
  let j : l.pages.upperPage.Index := ⟨i, by simpa [pages, PageLevels.Pages.upperPage] using hi⟩
  have he : l.upperLevel i = l.pages.upperLevel j := by
    unfold upperLevel
    rw [List.getD_eq_getElem _ _ (by
      change i < (List.ofFn l.pages.upperLevel).length
      rw [List.length_ofFn]
      exact j.isLt)]
    simp only [PageLevels.Pages.levels, List.getElem_ofFn]
    rfl
  rw [he]
  exact ⟨l.pages.upperLevel_pos hl j,
    (Finset.le_sup (f := l.pages.upperLevel) (Finset.mem_univ j)).trans (le_max_left _ _)⟩

private theorem lowerLevel_getD_bounds (l : PortLayout) {i : ℕ} (hi : i < l.lowerGroups.length) :
    1 ≤ l.lowerLevel i ∧ l.lowerLevel i ≤ l.pages.highest := by
  let j : l.pages.lowerPage.Index := ⟨i, by simpa [pages, PageLevels.Pages.lowerPage] using hi⟩
  have he : l.lowerLevel i = l.pages.lowerLevel j := by
    unfold lowerLevel
    rw [List.getD_eq_getElem _ _ (by
      change i < (List.ofFn l.pages.lowerLevel).length
      rw [List.length_ofFn]
      exact j.isLt)]
    simp only [PageLevels.Pages.levels, List.getElem_ofFn]
    rfl
  rw [he]
  constructor
  · cases hg : l.pages.lowerPage.group j <;> simp only [PageLevels.Pages.lowerLevel, hg] <;> omega
  · exact (Finset.le_sup (f := l.pages.lowerLevel) (Finset.mem_univ j)).trans (le_max_right _ _)

private theorem placement_level_bounds (l : PortLayout) (hl : l.pages.Valid) {g : Placement}
    (hg : g ∈ placements l) : 1 ≤ g.level ∧ g.level ≤ l.pages.highest := by
  simp only [placements, List.mem_append, List.mem_map] at hg
  rcases hg with ⟨⟨⟨a, b⟩, i⟩, hi, rfl⟩ | ⟨⟨lower, i⟩, hi, rfl⟩
  · exact upperLevel_getD_bounds l hl (by simpa using List.snd_lt_of_mem_zipIdx hi)
  · have hb := lowerLevel_getD_bounds l (by simpa using List.snd_lt_of_mem_zipIdx hi)
    cases lower <;> simpa only [encLowerGroup_elim, encLowerGroup_toSum,
      Sum.elim_inl, Sum.elim_inr] using hb

/-- Every actual endpoint reads an allocated positive table level on the fixed-level valid domain. -/
theorem endpoints_level_bounds (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) {e : Endpoint} (he : e ∈ l.endpoints) :
    1 ≤ e.level ∧ e.level ≤ p.levels := by
  obtain ⟨g, hg, he⟩ := List.mem_flatMap.mp he
  have hb := placement_level_bounds l hl hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;> exact ⟨hb.1, hb.2.trans hM⟩

end PushPuzzle.PushS.PortLayout
