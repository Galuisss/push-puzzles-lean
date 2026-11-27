/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramPrivateStockTarget
import all PushS.PortStreetEnumeration
import all PushS.PortSegments
import all PushS.PortLayoutCoordinates
import all PushS.PortWalkBudget

/-! The real first private read has four distinct surviving canonical holes in every selected column. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS PushS.PortLayout

private def fourDepth (p : Scales.Parameters) (i : Fin 4) : ℕ :=
  if i.val = 0 then p.Y 1 / 2 else if i.val = 1 then p.Y 1 else if i.val = 2 then p.Y 1 + 1 else p.Y 1 + 2

private theorem fourDepth_mem (p : Scales.Parameters) (i : Fin 4) :
    fourDepth p i ∈ ({p.Y 1 / 2, p.Y 1, p.Y 1 + 1, p.Y 1 + 2} : Finset ℕ) := by
  fin_cases i <;> simp [fourDepth]

private theorem fourDepth_bounds (p : Scales.Parameters) (i : Fin 4) :
    p.Y 1 / 2 ≤ fourDepth p i ∧ fourDepth p i ≤ p.Y 1 + 2 := by
  fin_cases i <;> simp only [fourDepth, Nat.reduceEqDiff, ite_true, ite_false] <;> omega

/-- Four distinct literal target holes survive in every actual private-column cap front at R9. -/
theorem private_front_card_ge_four (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (target : List Bool) (x : ℕ) (hx : x ∈ privateColumns l p) :
    4 ≤ (((emit ((schedule l p (targetHoles l p target \ Boundary.frame).card).take 9)
      (targetHoles l p target)).remaining).filter fun q =>
        q.1.val = x ∧ prefixRank .south q < p.Y 1 + 3).card := by
  obtain ⟨middle, hm, hxm⟩ := privateColumn_gate l p hx
  have hcol := column_inside p (center_port l p hl haxes hm)
    (center_columns_span p middle (show x ∈ centerColumns p middle from by
      rw [hxm]
      simp [centerColumns, specialColumns, coordinates, Coordinates.x, Scales.Parameters.x]))
  have hY := p.Y_ge 1
  have hD := readDepth_add_lt_D p 1
  rw [readDepth_eq p le_rfl p.levels_pos] at hD
  have hh : p.H = 2 * p.D := rfl
  let f (i : Fin 4) : Cell (p.W + 1) (p.H + 1) :=
    (⟨x, by omega⟩, ⟨p.H - fourDepth p i, by have := fourDepth_bounds p i; omega⟩)
  have hinj : Function.Injective f := by
    intro i j he
    have he := congrArg (fun q => q.2.val) he
    change p.H - fourDepth p i = p.H - fourDepth p j at he
    have hi := fourDepth_bounds p i
    have hj := fourDepth_bounds p j
    have hd : fourDepth p i = fourDepth p j := by omega
    fin_cases i <;> fin_cases j <;> simp [fourDepth] at hd ⊢ <;> omega
  have hsub : Finset.univ.image f ⊆
      ((emit ((schedule l p (targetHoles l p target \ Boundary.frame).card).take 9)
        (targetHoles l p target)).remaining).filter fun q =>
          q.1.val = x ∧ prefixRank .south q < p.Y 1 + 3 := by
    intro q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    have hi := fourDepth_bounds p i
    have hdepth : pageDepth p .lower (f i) = fourDepth p i := by
      change p.H - (p.H - fourDepth p i) = fourDepth p i
      omega
    apply Finset.mem_filter.mpr
    refine ⟨?_, rfl, ?_⟩
    · apply private_window_before_private l p hl hM haxes target
        (private_four_target l p target hx (fourDepth_mem p i) rfl) hx
      · rw [hdepth]
        exact hi.1
      · rw [hdepth]
        exact hi.2
    · change p.H + 1 - 1 - (p.H - fourDepth p i) < p.Y 1 + 3
      omega
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at hc
  exact hc

end PushPuzzle.Push.AcceptanceProgram
