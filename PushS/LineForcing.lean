/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.OrderedSlots

/-! Exact one-step mark motion and the player position required to move a train boundary. -/

public section
namespace PushPuzzle.PushS.RowLabels


open PushFS

variable {w h : ℕ} {ι : Type} [Fintype ι] {B : Board w h} {cap : Option ℕ}
  {axis d : Direction} {lane : ℕ} {S T : LineState ι w h axis lane}

/-- Each actual occupancy mark either stays put or moves one cell in the push direction. -/
theorem LineMove.position_cases (hm : LineMove B cap d S T) (i : ι) :
    T.position i = S.position i ∨ Adjacent d (S.position i) (T.position i) := by
  cases hm with
  | stable _ _ hpos => exact Or.inl (congrFun hpos i)
  | push _ ray hpos =>
    have he : T.position i = Labels.shiftMap ray.run (S.position i) := congrFun hpos i
    rcases Labels.shiftMap_cases ray.run (S.position i) with hf | ⟨j, hj, hdest⟩
    · exact Or.inl (he.trans hf)
    · rw [he, hdest, hj]
      exact Or.inr (ray.run.adjacent ⟨j.val + 1, by omega⟩)

/-- Moving any mark requires the player on the same rail. -/
theorem LineMove.player_lane_of_changed (hm : LineMove B cap d S T) (i : ι)
    (hchanged : T.position i ≠ S.position i) : axis.lane S.state.player = lane := by
  cases hm with
  | stable _ _ hpos => exact False.elim (hchanged (congrFun hpos i))
  | push _ ray _ => simpa only [ray.run.start] using ray.on_line 0

/-- One actual move changes each marked coordinate by at most one. -/
theorem LineMove.coordinate_bounds (hm : LineMove B cap d S T) (i : ι) :
    axis.position (S.position i) - 1 ≤ axis.position (T.position i) ∧
      axis.position (T.position i) ≤ axis.position (S.position i) + 1 := by
  rcases hm.position_cases i with he | ha
  · rw [he]
    omega
  · cases axis <;> cases d <;> simp only [Adjacent, Direction.position] at ha ⊢ <;> omega

/-- A strictly increasing mark coordinate identifies the forward rail direction. -/
theorem LineMove.direction_of_increase (hm : LineMove B cap d S T) (i : ι)
    (hi : axis.position (S.position i) < axis.position (T.position i)) : d = axis := by
  rcases hm.position_cases i with he | ha
  · rw [he] at hi
    exact False.elim (lt_irrefl _ hi)
  · have hl := (T.position_lane i).trans (S.position_lane i).symm
    cases axis <;> cases d <;> simp_all [Adjacent, Direction.position, Direction.lane] <;> omega

/-- A strictly decreasing mark coordinate identifies the backward rail direction. -/
theorem LineMove.direction_of_decrease (hm : LineMove B cap d S T) (i : ι)
    (hi : axis.position (T.position i) < axis.position (S.position i)) : d = axis.opposite := by
  rcases hm.position_cases i with he | ha
  · rw [he] at hi
    exact False.elim (lt_irrefl _ hi)
  · have hl := (T.position_lane i).trans (S.position_lane i).symm
    cases axis <;> cases d <;>
      simp_all [Adjacent, Direction.position, Direction.lane, Direction.opposite] <;> omega

/-- A missing preceding coordinate leaves the forward-facing side of a mark empty. -/
theorem LineState.no_box_behind_coordinate (S : LineState ι w h axis lane) (i : ι)
    (hhole : axis.position (S.position i) - 1 ∉ (lineBoxes axis lane S.state).image axis.position) :
    ∀ q, Adjacent axis q (S.position i) → q ∉ S.state.boxes := by
  intro q ha hbox
  have hq : q ∈ lineBoxes axis lane S.state := Finset.mem_filter.mpr
    ⟨hbox, ha.lane.symm.trans (S.position_lane i)⟩
  have hx : axis.position q = axis.position (S.position i) - 1 := by have h := ha.position; omega
  exact hhole (hx ▸ Finset.mem_image.mpr ⟨q, hq, rfl⟩)

/-- A missing following coordinate leaves the backward-facing side of a mark empty. -/
theorem LineState.no_box_ahead_coordinate (S : LineState ι w h axis lane) (i : ι)
    (hhole : axis.position (S.position i) + 1 ∉ (lineBoxes axis lane S.state).image axis.position) :
    ∀ q, Adjacent axis.opposite q (S.position i) → q ∉ S.state.boxes := by
  intro q ha hbox
  have ha' : Adjacent axis (S.position i) q := by simpa only [Direction.opposite_opposite] using ha.reverse
  have hq : q ∈ lineBoxes axis lane S.state := Finset.mem_filter.mpr ⟨hbox, ha'.lane.trans (S.position_lane i)⟩
  exact hhole (ha'.position ▸ Finset.mem_image.mpr ⟨q, hq, rfl⟩)

/-- Moving a mark with no box immediately behind it requires the player at that preceding cell. -/
theorem LineMove.force_of_no_box_behind (hm : LineMove B cap d S T) (i : ι)
    (hchanged : T.position i ≠ S.position i)
    (hfree : ∀ q, Adjacent d q (S.position i) → q ∉ S.state.boxes) :
    Adjacent d S.state.player (S.position i) := by
  cases hm with
  | stable _ _ hpos => exact False.elim (hchanged (congrFun hpos i))
  | push _ ray hpos =>
    have he : T.position i = Labels.shiftMap ray.run (S.position i) := congrFun hpos i
    rcases Labels.shiftMap_cases ray.run (S.position i) with hf | ⟨j, hj, _⟩
    · exact False.elim (hchanged (he.trans hf))
    · by_cases hj0 : j.val = 0
      · have hidx : (⟨j.val + 1, by omega⟩ : Fin (ray.length + 2)) = 1 := by
          apply Fin.ext
          simp only [Fin.val_one]
          omega
        have hp : S.position i = ray.run.cell 1 := hj.trans (congrArg ray.run.cell hidx)
        have ha := ray.run.adjacent 0
        change Adjacent d (ray.run.cell 0) (ray.run.cell 1) at ha
        rw [ray.run.start, ← hp] at ha
        exact ha
      · let q := ray.run.cell ⟨j.val, by have h := j.isLt; omega⟩
        have hq : q ∈ S.state.boxes := ray.run.occupied_at _ (by change 0 < j.val; omega)
          (by change j.val ≤ ray.length; have h := j.isLt; omega)
        have ha := ray.run.adjacent ⟨j.val, by have h := j.isLt; omega⟩
        change Adjacent d q (ray.run.cell ⟨j.val + 1, by omega⟩) at ha
        exact False.elim (hfree q (hj ▸ ha) hq)

/-- An increasing exposed train boundary can be pushed only from its immediately preceding gap. -/
theorem LineMove.force_along (hm : LineMove B cap d S T) (i : ι)
    (hi : axis.position (S.position i) < axis.position (T.position i))
    (hfree : ∀ q, Adjacent axis q (S.position i) → q ∉ S.state.boxes) :
    Adjacent axis S.state.player (S.position i) := by
  have hd := hm.direction_of_increase i hi
  subst d
  exact hm.force_of_no_box_behind i (fun he => by rw [he] at hi; exact lt_irrefl _ hi) hfree

/-- A decreasing exposed train boundary can be pushed only from its immediately following gap. -/
theorem LineMove.force_against (hm : LineMove B cap d S T) (i : ι)
    (hi : axis.position (T.position i) < axis.position (S.position i))
    (hfree : ∀ q, Adjacent axis.opposite q (S.position i) → q ∉ S.state.boxes) :
    Adjacent axis.opposite S.state.player (S.position i) := by
  have hd := hm.direction_of_decrease i hi
  subst d
  exact hm.force_of_no_box_behind i (fun he => by rw [he] at hi; exact lt_irrefl _ hi) hfree

/-- Moving any mark in a real step requires the player on the same rail. -/
theorem LineStep.player_lane_of_changed (hm : LineStep B cap S T) (i : ι)
    (hchanged : T.position i ≠ S.position i) : axis.lane S.state.player = lane := hm.choose_spec.player_lane_of_changed i hchanged

/-- One actual step changes each marked coordinate by at most one. -/
theorem LineStep.coordinate_bounds (hm : LineStep B cap S T) (i : ι) :
    axis.position (S.position i) - 1 ≤ axis.position (T.position i) ∧
      axis.position (T.position i) ≤ axis.position (S.position i) + 1 := hm.choose_spec.coordinate_bounds i

/-- Increasing an exposed train boundary forces the player into the preceding gap. -/
theorem LineStep.force_along (hm : LineStep B cap S T) (i : ι)
    (hi : axis.position (S.position i) < axis.position (T.position i))
    (hfree : ∀ q, Adjacent axis q (S.position i) → q ∉ S.state.boxes) :
    Adjacent axis S.state.player (S.position i) := hm.choose_spec.force_along i hi hfree

/-- Decreasing an exposed train boundary forces the player into the following gap. -/
theorem LineStep.force_against (hm : LineStep B cap S T) (i : ι)
    (hi : axis.position (T.position i) < axis.position (S.position i))
    (hfree : ∀ q, Adjacent axis.opposite q (S.position i) → q ∉ S.state.boxes) :
    Adjacent axis.opposite S.state.player (S.position i) := hm.choose_spec.force_against i hi hfree

/-- A forward-moving exposed coordinate fixes the player's coordinate at the preceding gap cell. -/
theorem LineStep.force_along_coordinate (hm : LineStep B cap S T) (i : ι) {x y : ℤ}
    (hx : axis.position (S.position i) = x) (hy : axis.position (T.position i) = y) (hi : x < y)
    (hhole : x - 1 ∉ (lineBoxes axis lane S.state).image axis.position) : axis.position S.state.player = x - 1 := by
  have hg : axis.position (S.position i) - 1 ∉ (lineBoxes axis lane S.state).image axis.position := by
    simpa only [hx] using hhole
  have ha := hm.force_along i (by rw [hx, hy]; exact hi) (S.no_box_behind_coordinate i hg)
  have hp := ha.position
  rw [hx] at hp
  omega

/-- A backward-moving exposed coordinate fixes the player's coordinate at the following gap cell. -/
theorem LineStep.force_against_coordinate (hm : LineStep B cap S T) (i : ι) {x y : ℤ}
    (hx : axis.position (S.position i) = x) (hy : axis.position (T.position i) = y) (hi : y < x)
    (hhole : x + 1 ∉ (lineBoxes axis lane S.state).image axis.position) : axis.position S.state.player = x + 1 := by
  have hg : axis.position (S.position i) + 1 ∉ (lineBoxes axis lane S.state).image axis.position := by
    simpa only [hx] using hhole
  have ha := hm.force_against i (by rw [hx, hy]; exact hi) (S.no_box_ahead_coordinate i hg)
  have ha' : Adjacent axis (S.position i) S.state.player := by simpa only [Direction.opposite_opposite] using ha.reverse
  simpa only [hx] using ha'.position

/-- Lift a successful prefix, one actual step, and the suffix with one consistent set of occupancy marks. -/
theorem OrderedLineState.lift_step_at {n : ℕ} (S U : OrderedLineState n w h axis lane) {u v t : State w h}
    (hpre : Relation.ReflTransGen (LineAdmissible B cap axis lane) S.state u)
    (hstep : LineAdmissible B cap axis lane u v)
    (hpost : Relation.ReflTransGen (LineAdmissible B cap axis lane) v t)
    (hsol : lineBoxes axis lane t = lineBoxes axis lane U.state) :
    ∃ M N V : LineState (Fin n) w h axis lane,
      M.state = u ∧ N.state = v ∧ V.state = t ∧ LineReachable B cap S.toLineState M ∧
        LineStep B cap M N ∧ LineReachable B cap N V ∧ V.position = U.position := by
  obtain ⟨M, hM, hSM⟩ := lift_reachable S.toLineState hpre
  obtain ⟨N, hN, hMN⟩ := lift_step M (hM ▸ hstep)
  obtain ⟨V, hV, hNV⟩ := lift_reachable N (hN ▸ hpost)
  exact ⟨M, N, V, hM, hN, hV, hSM, hMN, hNV,
    OrderedLineState.matches_target ((hSM.tail hMN).trans hNV) (hV ▸ hsol)⟩

end PushPuzzle.PushS.RowLabels
