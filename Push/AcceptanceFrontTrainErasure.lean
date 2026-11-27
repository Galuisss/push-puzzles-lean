/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceFrontTrain

/-! A first train also survives removal of a box beyond its complete occupied span. -/

public section
namespace PushPuzzle.Push.AcceptanceFrontTrain

open PushFS PushS.RowLabels

/-- A real line update may additionally erase a cell farther than the first train's full length below its occupied cut. -/
structure EditingStep {w h : ℕ} (B : Board w h) (cap : Option ℕ)
    (axis : Direction) (lane length : ℕ) (cut : ℤ) (s t : State w h) : Prop where
  cut_box : ∃ q ∈ lineBoxes axis lane s, axis.position q ≤ cut
  update : LineAdmissible B cap axis lane s t ∨
    (∃ q, cut ≤ axis.position q ∧ lineBoxes axis lane t = insert q (lineBoxes axis lane s)) ∨
    (∃ q, cut + length ≤ axis.position q ∧ lineBoxes axis lane t = (lineBoxes axis lane s).erase q)

variable {w h length : ℕ} {axis : Direction} {lane : ℕ} {s t : State w h}

/-- A deletion beyond the whole first train preserves all its occupied marks and its first position. -/
theorem FrontTrain.edit {B : Board w h} {cap : Option ℕ} {cut : ℤ}
    (train : FrontTrain axis lane length s) (positive : 0 < length)
    (step : EditingStep B cap axis lane length cut s t) : Nonempty (FrontTrain axis lane length t) := by
  rcases step.update with hline | hinsert | ⟨q, hfar, hboxes⟩
  · exact train.step (B := B) (cap := cap) positive ⟨step.cut_box, Or.inl hline⟩
  · exact train.step (B := B) (cap := cap) positive ⟨step.cut_box, Or.inr hinsert⟩
  · obtain ⟨z, hz, hzcut⟩ := step.cut_box
    have hfirst := (train.least z hz).trans hzcut
    refine ⟨⟨train.first, train.position, ?_, train.coordinates, ?_⟩⟩
    · intro i
      rw [hboxes]
      apply Finset.mem_erase.mpr
      refine ⟨?_, train.occupied i⟩
      intro he
      have hi := i.isLt
      have hc := train.coordinates i
      rw [he] at hc
      omega
    · intro r hr
      rw [hboxes] at hr
      exact train.least r (Finset.mem_of_mem_erase hr)

/-- Admissible line motions, lower insertions and sufficiently distant erasures preserve the original first train. -/
theorem FrontTrain.editing_reachable {B : Board w h} {cap : Option ℕ} {cut : ℤ}
    (train : FrontTrain axis lane length s) (positive : 0 < length)
    (run : Relation.ReflTransGen (EditingStep B cap axis lane length cut) s t) :
    Nonempty (FrontTrain axis lane length t) := by
  induction run with
  | refl => exact ⟨train⟩
  | tail _ step ih =>
    obtain ⟨u⟩ := ih
    exact u.edit positive step

end PushPuzzle.Push.AcceptanceFrontTrain
