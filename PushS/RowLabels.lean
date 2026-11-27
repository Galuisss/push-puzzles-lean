/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.TrainAdjacency

/-! Occupancy labels on one straight rail, retaining its full surrounding puzzle state. -/

@[expose] public section
namespace PushPuzzle.PushS.RowLabels

open PushFS

variable {w h : ℕ}

/-- Boxes currently occupying the specified row or column. -/
def lineBoxes (axis : Direction) (lane : ℕ) (s : State w h) : Finset (Cell w h) :=
  s.boxes.filter fun p => axis.lane p = lane

/-- A complete ray whose player, boxes, and first empty destination lie on one rail. -/
structure PushOnLine (B : Board w h) (d axis : Direction) (lane : ℕ)
    (s t : State w h) where
  length : ℕ
  positive : 0 < length
  run : Run B d s length
  player : t.player = run.cell 1
  boxes : t.boxes = insert (run.cell ⟨length + 1, by omega⟩) (s.boxes.erase (run.cell 1))
  on_line : ∀ i, axis.lane (run.cell i) = lane

namespace PushOnLine
variable {B : Board w h} {d axis : Direction} {lane : ℕ} {s t : State w h}

private theorem shift_line (r : PushOnLine B d axis lane s t) (p : Cell w h) :
    axis.lane (Labels.shiftMap r.run p) = lane ↔ axis.lane p = lane := by
  rcases Labels.shiftMap_cases r.run p with he | ⟨i, hp, hdest⟩
  · simp only [he]
  · rw [hdest, hp]
    simp only [r.on_line]

/-- The actual complete push transports exactly the line's occupied set. -/
private theorem image_lineBoxes (r : PushOnLine B d axis lane s t) :
    (lineBoxes axis lane s).image (Labels.shiftMap r.run) = lineBoxes axis lane t := by
  change (s.boxes.filter _).image _ = t.boxes.filter _
  rw [r.boxes, ← Labels.image_shiftMap r.run r.positive]
  ext p
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨q, ⟨hq, hline⟩, he⟩
    exact ⟨⟨q, hq, he⟩, he ▸ (r.shift_line q).mpr hline⟩
  · rintro ⟨⟨q, hq, he⟩, hline⟩
    exact ⟨q, ⟨hq, (r.shift_line q).mp (he.symm ▸ hline)⟩, he⟩

end PushOnLine

/-- A real move either leaves this rail's occupancy unchanged or pushes a full ray on it. -/
def LineAdmissible (B : Board w h) (cap : Option ℕ) (axis : Direction) (lane : ℕ)
    (s t : State w h) : Prop :=
  ∃ d, Move B cap d s t ∧
    (lineBoxes axis lane t = lineBoxes axis lane s ∨
      Nonempty (PushOnLine B d axis lane s t))

/-- Line-local occupancy labels with the exact unlabelled state of the whole board. -/
structure LineState (ι : Type) [Fintype ι] (w h : ℕ) (axis : Direction) (lane : ℕ) where
  state : State w h
  position : ι → Cell w h
  injective : Function.Injective position
  boxes_image : Finset.univ.image position = lineBoxes axis lane state

namespace LineState
variable {ι : Type} [Fintype ι] {axis : Direction} {lane : ℕ}

theorem position_mem (S : LineState ι w h axis lane) (i : ι) :
    S.position i ∈ lineBoxes axis lane S.state := by
  rw [← S.boxes_image]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

private theorem position_box (S : LineState ι w h axis lane) (i : ι) :
    S.position i ∈ S.state.boxes := (Finset.mem_filter.mp (S.position_mem i)).1

theorem position_lane (S : LineState ι w h axis lane) (i : ι) :
    axis.lane (S.position i) = lane := (Finset.mem_filter.mp (S.position_mem i)).2

/-- The initial occupied cells of the rail give its complete label set. -/
def initial (s : State w h) (axis : Direction) (lane : ℕ) :
    LineState {p // p ∈ lineBoxes axis lane s} w h axis lane where
  state := s
  position := Subtype.val
  injective := Subtype.val_injective
  boxes_image := by ext p; simp

end LineState

variable {ι : Type} [Fintype ι] {B : Board w h} {cap : Option ℕ}
  {axis d : Direction} {lane : ℕ} {S T : LineState ι w h axis lane}

/-- A rail-occupancy update preserves labels when transverse pushes preserve the occupied set. -/
inductive LineMove (B : Board w h) (cap : Option ℕ) (d : Direction)
    (S T : LineState ι w h axis lane) : Prop
  | stable (move : Move B cap d S.state T.state)
      (boxes : lineBoxes axis lane T.state = lineBoxes axis lane S.state)
      (positions : T.position = S.position) : LineMove B cap d S T
  | push (move : Move B cap d S.state T.state)
      (ray : PushOnLine B d axis lane S.state T.state)
      (positions : T.position = Labels.shiftMap ray.run ∘ S.position) : LineMove B cap d S T

/-- One actual board move with its line-local occupancy update. -/
def LineStep (B : Board w h) (cap : Option ℕ)
    (S T : LineState ι w h axis lane) : Prop := ∃ d, LineMove B cap d S T

/-- A complete exact-state trajectory with the rail's occupancy labels. -/
abbrev LineReachable (B : Board w h) (cap : Option ℕ) :=
  Relation.ReflTransGen (LineStep (ι := ι) (axis := axis) (lane := lane) B cap)

/-- Every admissible real move lifts without changing any player or box state. -/
theorem lift_step (S : LineState ι w h axis lane) {t : State w h}
    (hm : LineAdmissible B cap axis lane S.state t) :
    ∃ T : LineState ι w h axis lane, T.state = t ∧ LineStep B cap S T := by
  classical
  obtain ⟨d, hmove, hcase⟩ := hm
  rcases hcase with hstable | hpush
  · let T : LineState ι w h axis lane :=
      ⟨t, S.position, S.injective, S.boxes_image.trans hstable.symm⟩
    exact ⟨T, rfl, d, .stable hmove hstable rfl⟩
  · obtain ⟨ray⟩ := hpush
    have hinj : Function.Injective (Labels.shiftMap ray.run ∘ S.position) := by
      intro i j he
      exact S.injective (Labels.shiftMap_injOn ray.run (S.position_box i) (S.position_box j) he)
    have himage : Finset.univ.image (Labels.shiftMap ray.run ∘ S.position) =
        lineBoxes axis lane t := by
      rw [← Finset.image_image, S.boxes_image, ray.image_lineBoxes]
    let T : LineState ι w h axis lane := ⟨t, _, hinj, himage⟩
    exact ⟨T, rfl, d, .push hmove ray rfl⟩

/-- The full original trajectory lifts once its rail-admissibility is established. -/
theorem lift_reachable (S : LineState ι w h axis lane) {t : State w h}
    (hr : Relation.ReflTransGen (LineAdmissible B cap axis lane) S.state t) :
    ∃ T : LineState ι w h axis lane, T.state = t ∧ LineReachable B cap S T := by
  induction hr with
  | refl => exact ⟨S, rfl, .refl⟩
  | tail _ hm ih =>
    obtain ⟨U, hu, hprefix⟩ := ih
    obtain ⟨V, hv, hstep⟩ := lift_step U (hu ▸ hm)
    exact ⟨V, hv, hprefix.tail hstep⟩

/-- A row-local update preserves neighboring marks, including through identity-swapping crossings. -/
private theorem LineMove.adjacent (hm : LineMove B cap d S T) (i j : ι)
    (ha : Adjacent axis (S.position i) (S.position j)) :
    Adjacent axis (T.position i) (T.position j) := by
  cases hm with
  | stable _ _ hpos => simpa only [hpos] using ha
  | push hmove ray hpos =>
    have hi : axis.lane (Labels.shiftMap ray.run (S.position i)) = axis.lane (S.position i) := by
      rw [← Function.comp_apply (f := Labels.shiftMap ray.run) (g := S.position), ← hpos]
      exact (T.position_lane i).trans (S.position_lane i).symm
    have hj : axis.lane (Labels.shiftMap ray.run (S.position j)) = axis.lane (S.position j) := by
      rw [← Function.comp_apply (f := Labels.shiftMap ray.run) (g := S.position), ← hpos]
      exact (T.position_lane j).trans (S.position_lane j).symm
    simp only [hpos, Function.comp_apply]
    exact TrainAdjacency.shift_adjacent ray.run hmove.valid_source
      (S.position_box i) (S.position_box j) ha hi hj

theorem LineStep.adjacent (hm : LineStep B cap S T) (i j : ι)
    (ha : Adjacent axis (S.position i) (S.position j)) :
    Adjacent axis (T.position i) (T.position j) :=
  hm.choose_spec.adjacent i j ha

/-- Once two rail-local marks become adjacent, they remain adjacent on the entire suffix. -/
theorem LineReachable.adjacent (hr : LineReachable B cap S T) (i j : ι)
    (ha : Adjacent axis (S.position i) (S.position j)) :
    Adjacent axis (T.position i) (T.position j) := by
  induction hr with
  | refl => exact ha
  | tail _ hm ih => exact hm.adjacent i j ih

end PushPuzzle.PushS.RowLabels
