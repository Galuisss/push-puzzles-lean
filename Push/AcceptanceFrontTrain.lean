/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceTrainBlocks
public import PushS.RowOrder

/-! The first consecutive occupancy train survives line pushes and new boxes inserted below a persistent cut. -/

public section
namespace PushPuzzle.Push.AcceptanceFrontTrain

open PushFS PushS.RowLabels

/-- A consecutive train containing the first occupied coordinates of an actual line. -/
structure FrontTrain {w h : ℕ} (axis : Direction) (lane length : ℕ) (s : State w h) where
  first : ℤ
  position : Fin length → Cell w h
  occupied : ∀ i, position i ∈ lineBoxes axis lane s
  coordinates : ∀ i, axis.position (position i) = first + i.val
  least : ∀ q ∈ lineBoxes axis lane s, first ≤ axis.position q

/-- A line may evolve admissibly or receive a new box beyond an occupied cut. -/
structure GrowingStep {w h : ℕ} (B : Board w h) (cap : Option ℕ)
    (axis : Direction) (lane : ℕ) (cut : ℤ) (s t : State w h) : Prop where
  cut_box : ∃ q ∈ lineBoxes axis lane s, axis.position q ≤ cut
  update : LineAdmissible B cap axis lane s t ∨
    ∃ q, cut ≤ axis.position q ∧ lineBoxes axis lane t = insert q (lineBoxes axis lane s)

variable {w h length : ℕ} {axis : Direction} {lane : ℕ} {s t : State w h}

private theorem FrontTrain.admissible {B : Board w h} {cap : Option ℕ}
    (train : FrontTrain axis lane length s) (positive : 0 < length)
    (step : LineAdmissible B cap axis lane s t) :
    Nonempty (FrontTrain axis lane length t) := by
  let S := LineState.initial s axis lane
  obtain ⟨T, ht, hST⟩ := lift_step S step
  let mark (i : Fin length) : {q // q ∈ lineBoxes axis lane s} := ⟨train.position i, train.occupied i⟩
  let firstMark := mark ⟨0, positive⟩
  let first := axis.position (T.position firstMark)
  have offset : ∀ i : Fin length, axis.position (T.position (mark i)) = first + i.val := by
    intro i
    obtain ⟨i, hi⟩ := i
    induction i with
    | zero => simp only [first, firstMark, Int.natCast_zero, Int.add_zero]
    | succ i ih =>
      have hi' : i < length := by omega
      have hadj : Adjacent axis (S.position (mark ⟨i, hi'⟩)) (S.position (mark ⟨i + 1, hi⟩)) := by
        apply (adjacent_iff_coordinates axis _ _).mpr
        refine ⟨(S.position_lane _).trans (S.position_lane _).symm, ?_⟩
        change axis.position (train.position ⟨i + 1, hi⟩) = axis.position (train.position ⟨i, hi'⟩) + 1
        rw [train.coordinates, train.coordinates]
        dsimp only
        omega
      have after := (hST.adjacent _ _ hadj).position
      rw [ih hi'] at after
      dsimp only at after ⊢
      exact after.trans (by omega)
  refine ⟨⟨first, fun i => T.position (mark i), ?_, offset, ?_⟩⟩
  · intro i
    rw [← ht]
    exact T.position_mem _
  · intro q hq
    rw [← ht, ← T.boxes_image] at hq
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hq
    have before := train.least j.val j.property
    have hfirst : axis.position (S.position firstMark) = train.first := by
      simpa only [firstMark, mark, S, LineState.initial, Nat.cast_zero, Int.add_zero] using train.coordinates ⟨0, positive⟩
    rcases lt_or_eq_of_le before with hlt | heq
    · exact (hST.order firstMark j (by rw [hfirst]; exact hlt)).le
    · have he : S.position firstMark = S.position j :=
        axis.cell_ext ((S.position_lane _).trans (S.position_lane _).symm) (hfirst.trans heq)
      have hij := S.injective he
      rw [← hij]

/-- The original first train survives one line update, including an insertion beyond its persistent cut. -/
theorem FrontTrain.step {B : Board w h} {cap : Option ℕ} {cut : ℤ}
    (train : FrontTrain axis lane length s) (positive : 0 < length)
    (step : GrowingStep B cap axis lane cut s t) : Nonempty (FrontTrain axis lane length t) := by
  rcases step.update with hline | ⟨q, hcut, hboxes⟩
  · exact train.admissible positive hline
  · obtain ⟨z, hz, hzcut⟩ := step.cut_box
    have hfirst := (train.least z hz).trans (hzcut.trans hcut)
    refine ⟨⟨train.first, train.position, ?_, train.coordinates, ?_⟩⟩
    · intro i
      rw [hboxes]
      exact Finset.mem_insert_of_mem (train.occupied i)
    · intro r hr
      rw [hboxes] at hr
      exact (Finset.mem_insert.mp hr).elim (fun he => he ▸ hfirst) (train.least r)

/-- Every trajectory of admissible updates and cut-bounded insertions retains the same first train length. -/
theorem FrontTrain.reachable {B : Board w h} {cap : Option ℕ} {cut : ℤ}
    (train : FrontTrain axis lane length s) (positive : 0 < length)
    (run : Relation.ReflTransGen (GrowingStep B cap axis lane cut) s t) :
    Nonempty (FrontTrain axis lane length t) := by
  induction run with
  | refl => exact ⟨train⟩
  | tail _ step ih =>
    obtain ⟨u⟩ := ih
    exact u.step positive step

/-- The first interval of a separated literal three-block layout supplies a front train. -/
noncomputable def FrontTrain.ofThreeSlots {b : ThreeBlocks} (hb : b.Separated)
    (source : (lineBoxes axis lane s).image axis.position = b.slots) :
    FrontTrain axis lane b.firstLength s := by
  classical
  have hex (i : Fin b.firstLength) : ∃ q ∈ lineBoxes axis lane s, axis.position q = b.first + i.val := by
    apply Finset.mem_image.mp
    rw [source, ThreeBlocks.mem_slots]
    exact Or.inl ⟨by omega, by have hi := i.isLt; omega⟩
  refine ⟨b.first, fun i => Classical.choose (hex i), fun i => (Classical.choose_spec (hex i)).1,
    fun i => (Classical.choose_spec (hex i)).2, ?_⟩
  intro q hq
  exact (b.slots_bounds hb (source ▸ Finset.mem_image.mpr ⟨q, hq, rfl⟩)).1

/-- Every line coordinate covered by the preserved first train is occupied. -/
theorem FrontTrain.box_of_bounds (train : FrontTrain axis lane length s)
    (q : Cell w h) (hq : axis.lane q = lane)
    (lower : train.first ≤ axis.position q) (upper : axis.position q < train.first + length) :
    q ∈ s.boxes := by
  let i := (axis.position q - train.first).toNat
  have hi : (i : ℤ) = axis.position q - train.first := Int.toNat_of_nonneg (by omega)
  have hib : i < length := by omega
  have hp := train.occupied ⟨i, hib⟩
  have hcoord := train.coordinates ⟨i, hib⟩
  dsimp only at hcoord
  have he : train.position ⟨i, hib⟩ = q :=
    axis.cell_ext (((Finset.mem_filter.mp hp).2).trans hq.symm) (by omega)
  exact he ▸ (Finset.mem_filter.mp hp).1

end PushPuzzle.Push.AcceptanceFrontTrain
