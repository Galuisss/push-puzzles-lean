/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.RowLabels
import Mathlib.Order.Hom.Set
import Mathlib.Order.Preorder.Finite

/-! Rail-local occupancy marks retain their order and match ordered canonical target slots. -/

@[expose] public section
namespace PushPuzzle.PushS.RowLabels

open PushFS

variable {w h : ℕ}

private def offset (axis d : Direction) : ℤ :=
  if d = axis then 1 else if d = axis.opposite then -1 else 0

private theorem offset_bounds (axis d : Direction) :
    -1 ≤ offset axis d ∧ offset axis d ≤ 1 := by
  unfold offset
  split_ifs <;> omega

private theorem adjacent_offset {axis d : Direction} {p q : Cell w h}
    (ha : Adjacent d p q) : axis.position q = axis.position p + offset axis d := by
  cases axis <;> cases d <;>
    simp [offset, Direction.opposite, Adjacent, Direction.position] at * <;> omega

private theorem shift_offset {B : Board w h} {d axis : Direction} {s : State w h} {n : ℕ}
    (r : Run B d s n) (p : Cell w h) :
    axis.position (Labels.shiftMap r p) = axis.position p ∨
      axis.position (Labels.shiftMap r p) = axis.position p + offset axis d := by
  rcases Labels.shiftMap_cases r p with he | ⟨i, hp, hdest⟩
  · exact Or.inl (congrArg axis.position he)
  · right
    rw [hdest, hp]
    exact adjacent_offset (r.adjacent ⟨i.val + 1, by omega⟩)

variable {ι : Type} [Fintype ι] {B : Board w h} {cap : Option ℕ}
  {axis d : Direction} {lane : ℕ} {S T : LineState ι w h axis lane}

/-- One rail-local update preserves the strict order of any two occupancy marks. -/
private theorem LineMove.order (hm : LineMove B cap d S T) (i j : ι)
    (hij : axis.position (S.position i) < axis.position (S.position j)) :
    axis.position (T.position i) < axis.position (T.position j) := by
  have hneij : i ≠ j := by intro he; subst j; omega
  have hne : axis.position (T.position i) ≠ axis.position (T.position j) := by
    intro he
    exact hneij (T.injective (axis.cell_ext
      ((T.position_lane i).trans (T.position_lane j).symm) he))
  cases hm with
  | stable _ _ hpos => simpa only [hpos] using hij
  | push _ ray hpos =>
    have hi := shift_offset (axis := axis) ray.run (S.position i)
    have hj := shift_offset (axis := axis) ray.run (S.position j)
    have hb := offset_bounds axis d
    simp only [hpos, Function.comp_apply] at hne ⊢
    omega

/-- A real step with its line-local update cannot make two marks overtake. -/
theorem LineStep.order (hm : LineStep B cap S T) (i j : ι)
    (hij : axis.position (S.position i) < axis.position (S.position j)) :
    axis.position (T.position i) < axis.position (T.position j) :=
  hm.choose_spec.order i j hij

/-- The original order of line-local marks is retained throughout the entire trajectory. -/
private theorem LineReachable.order (hr : LineReachable B cap S T) (i j : ι)
    (hij : axis.position (S.position i) < axis.position (S.position j)) :
    axis.position (T.position i) < axis.position (T.position j) := by
  induction hr with
  | refl => exact hij
  | tail _ hm ih => exact hm.order i j ih

/-- A finite increasing source enumeration stays increasing on the actual path. -/
theorem LineReachable.strictMono {n : ℕ} {S T : LineState (Fin n) w h axis lane}
    (hr : LineReachable B cap S T)
    (hS : StrictMono (fun i => axis.position (S.position i))) :
    StrictMono (fun i => axis.position (T.position i)) :=
  fun i j hij => hr.order i j (hS hij)

/-- A full rail inventory enumerated in strict order for canonical source or target slots. -/
structure OrderedLineState (n w h : ℕ) (axis : Direction) (lane : ℕ)
    extends LineState (Fin n) w h axis lane where
  ordered : StrictMono (fun i => axis.position (position i))

namespace OrderedLineState
variable {n : ℕ} {S U : OrderedLineState n w h axis lane}
  {T : LineState (Fin n) w h axis lane}

/-- Equal final rail occupancy uniquely matches the prescribed increasing target slots. -/
theorem matches_target (hr : LineReachable B cap S.toLineState T)
    (hsol : lineBoxes axis lane T.state = lineBoxes axis lane U.state) :
    T.position = U.position := by
  have hT := hr.strictMono S.ordered
  have hrange : Set.range (fun i => axis.position (T.position i)) =
      Set.range (fun i => axis.position (U.position i)) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      have hp : T.position i ∈ lineBoxes axis lane U.state := by
        rw [← hsol]
        exact T.position_mem i
      rw [← U.boxes_image] at hp
      obtain ⟨j, _, he⟩ := Finset.mem_image.mp hp
      exact ⟨j, congrArg axis.position he⟩
    · rintro ⟨i, rfl⟩
      have hp : U.position i ∈ lineBoxes axis lane T.state := by
        rw [hsol]
        exact U.toLineState.position_mem i
      rw [← T.boxes_image] at hp
      obtain ⟨j, _, he⟩ := Finset.mem_image.mp hp
      exact ⟨j, congrArg axis.position he⟩
  have heq := (hT.range_inj_of_wellFoundedLT U.ordered).mp hrange
  funext i
  exact axis.cell_ext ((T.position_lane i).trans (U.toLineState.position_lane i).symm)
    (congrFun heq i)

/-- Marks separated in the canonical target were never adjacent on a successful prefix. -/
theorem nonadjacent_at {M V : LineState (Fin n) w h axis lane}
    (hSM : LineReachable B cap S.toLineState M) (hMV : LineReachable B cap M V)
    (hsol : lineBoxes axis lane V.state = lineBoxes axis lane U.state) (i j : Fin n)
    (hsep : ¬ Adjacent axis (U.position i) (U.position j)) :
    ¬ Adjacent axis (M.position i) (M.position j) := by
  have hpos := matches_target (hSM.trans hMV) hsol
  intro ha
  exact hsep (by simpa only [hpos] using hMV.adjacent i j ha)

end OrderedLineState
end PushPuzzle.PushS.RowLabels
