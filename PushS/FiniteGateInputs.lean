/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateOutputs
import Mathlib.Tactic.FinCases

/-! Full OR input propagation, including every left-tail box and the prepared A trigger. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGateInputs

open PushFS FiniteGeometry FiniteGateCore FiniteGateMacros FiniteGatePrepared FiniteLineMacros

attribute [local irreducible] side

/-- The OR left tail, ordered from its outermost box toward D. -/
def orInputLine (w : ℕ) : Line (side w) (side w) where
  count := w+5
  base := origin w-2*w-8
  base_pos := by unfold origin; omega
  fits := by unfold origin side; omega
  row := (point w 1 0).2
  lane := (point w 1 1).2
  entry := .south
  crossing := by intro x; dsimp [Adjacent, point]; unfold origin; omega
  hub := (point w 1 1).1

private def reverseIndex (w : ℕ) (i : Fin (w+5)) : Fin (w+5) :=
  ⟨w+4-i.val, by have := i.isLt; omega⟩

private theorem reverseIndex_reverse (w : ℕ) (i : Fin (w+5)) :
    reverseIndex w (reverseIndex w i) = i := by
  apply Fin.ext
  have := i.isLt
  dsimp [reverseIndex]
  omega

def orInputKeep {w : ℕ} : OrLabel w → Bool
  | .left _ => false
  | _ => true

def orInputFixed (w : ℕ) (b c : Bool) : Finset (Cell (side w) (side w)) :=
  (Finset.univ.filter fun l => orInputKeep l).image (orCell w false b c)

/-- The left tail has phase `q`; A retains its closed slot. -/
def orInputCell (w : ℕ) (b c q : Bool) (l : OrLabel w) : Cell (side w) (side w) :=
  match l with
  | .left _ => orCell w q b c l
  | _ => orCell w false b c l

def orInputBoxes (w : ℕ) (b c q : Bool) : Finset (Cell (side w) (side w)) :=
  Finset.univ.image (orInputCell w b c q)

private theorem orInputCell_kept (w : ℕ) (b c q : Bool) (l : OrLabel w)
    (hl : orInputKeep l = true) : orInputCell w b c q l = orCell w false b c l := by
  cases l <;> try rfl
  exact False.elim (Bool.noConfusion hl)

private theorem orInputFixed_free (w : ℕ) (b c : Bool)
    (goals : Finset (Cell (side w) (side w))) (p : Cell (side w) (side w))
    (hx : p.1.val ≤ origin w+2) (hy : p.2.val ≤ origin w) :
    Free (orBoard w goals) (orInputFixed w b c) p := by
  constructor
  · intro hp
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
    have hi' := ((orRectangle w i).mem_cells _ _ _).mp hi
    fin_cases i <;> simp [orRectangle, origin] at hi' hx hy <;> omega
  · intro hp
    obtain ⟨l, hl, he⟩ := Finset.mem_image.mp hp
    have hkeep := (Finset.mem_filter.mp hl).2
    have hpx := congrArg (fun p => p.1.val) he
    have hb := Bool.toNat_le b
    have hc := Bool.toNat_le c
    cases l <;> dsimp only [orInputKeep] at hkeep
    · exact Bool.noConfusion hkeep
    all_goals simp only [orCell, orPoint, origin, Bool.toNat_false] at hpx hx; omega

/-- The entire OR tail uses the exposed upper lane, with A and both other branches fixed. -/
theorem orInputFrame (w : ℕ) (hw : 2 ≤ w) (b c : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    (orInputLine w).Frame (orBoard w goals) (orInputFixed w b c) := by
  constructor
  · apply (orBoxes_disjoint_walls w hw false b c).mono_left
    intro p hp
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_image.mpr ⟨l, Finset.mem_univ _, rfl⟩
  · intro x hx
    apply orInputFixed_free w b c goals
    all_goals dsimp [orInputLine, Line.track, point] at *; unfold origin at *; omega
  · intro x hx
    apply orInputFixed_free w b c goals
    all_goals dsimp [orInputLine, Line.laneSegment, point] at *; unfold origin at *; omega

private theorem orInputLine_position (w : ℕ) (b c q : Bool) (i : Fin (w+5)) :
    (orInputLine w).position (if q then w+5 else 0) i =
      orInputCell w b c q (.left (reverseIndex w i)) := by
  have hbound := i.isLt
  cases q <;> apply Prod.ext <;> apply Fin.ext <;>
    simp [orInputLine, Line.position, point, orInputCell, orCell, orPoint, reverseIndex, hbound, origin]
  all_goals omega

theorem orInputLine_boxes (w : ℕ) (b c q : Bool) :
    (orInputLine w).boxes (orInputFixed w b c) (if q then w+5 else 0) =
      orInputBoxes w b c q := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_image.mpr ⟨l, Finset.mem_univ _,
        orInputCell_kept w b c q l (Finset.mem_filter.mp hl).2⟩
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_image.mpr ⟨.left (reverseIndex w i), Finset.mem_univ _,
        (orInputLine_position w b c q i).symm⟩
  · intro hp
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hp
    by_cases hkeep : orInputKeep l = true
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkeep⟩,
        (orInputCell_kept w b c q l hkeep).symm⟩
    · cases l <;> try exact False.elim (hkeep rfl)
      rename_i i
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨reverseIndex w i, Finset.mem_univ _, by
        rw [orInputLine_position, reverseIndex_reverse]⟩

theorem orInputBoxes_false (w : ℕ) (b c : Bool) :
    orInputBoxes w b c false = orBoxes w false b c := by
  unfold orInputBoxes orBoxes
  congr 1
  funext l
  cases l <;> rfl

/-- The updated left tail leaves precisely A's old slot as the final prepared trigger. -/
theorem orInputBoxes_true (w : ℕ) (hw : 2 ≤ w) (b c : Bool) :
    insert (point w 3 0) ((orBoxes w true b c).erase (point w 2 0)) = orInputBoxes w b c true := by
  have he := Line.image_relocate (orCell w true b c) (orInputCell w b c true)
    (orCell_injective w hw true b c) .triggerA (by
      intro l hl
      cases l <;> first | rfl | exact False.elim (hl rfl))
  have hlow : orCell w true b c .triggerA = point w 2 0 := by
    apply Prod.ext <;> apply Fin.ext <;> dsimp [orCell, orPoint, point]
  have hhigh : orInputCell w b c true .triggerA = point w 3 0 := by
    apply Prod.ext <;> apply Fin.ext <;> dsimp [orInputCell, orCell, orPoint, point]
  simpa only [orBoxes, orInputBoxes, hlow, hhigh] using he

/-- Move all left-tail boxes into their new slots, leaving A prepared. -/
theorem or_A_tail_forward (w : ℕ) (hw : 2 ≤ w) (b c : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (orBoard w goals) (some 1)
      ⟨point w 1 1, orBoxes w false b c⟩ ⟨point w 1 1, orInputBoxes w b c true⟩ := by
  have hr := (orInputFrame w hw b c goals).forward
  have hzero := orInputLine_boxes w b c false
  change (orInputLine w).boxes (orInputFixed w b c) 0 = orInputBoxes w b c false at hzero
  have hfull := orInputLine_boxes w b c true
  change (orInputLine w).boxes (orInputFixed w b c) (w+5) = orInputBoxes w b c true at hfull
  change Reachable (orBoard w goals) (some 1)
    ⟨point w 1 1, (orInputLine w).boxes (orInputFixed w b c) 0⟩
    ⟨point w 1 1, (orInputLine w).boxes (orInputFixed w b c) (w+5)⟩ at hr
  rw [hzero, hfull, orInputBoxes_false] at hr
  exact hr

/-- Release A first and propagate the complete OR left tail backward. -/
theorem or_A_backward (w : ℕ) (hw : 2 ≤ w) (b c : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (orBoard w goals) (some 1)
      ⟨point w 1 1, orBoxes w true b c⟩ ⟨point w 1 1, orBoxes w false b c⟩ := by
  have hfirst := or_A_right w hw b c goals
  rw [orInputBoxes_true w hw b c] at hfirst
  have hr := (orInputFrame w hw b c goals).backward
  have hzero := orInputLine_boxes w b c false
  change (orInputLine w).boxes (orInputFixed w b c) 0 = orInputBoxes w b c false at hzero
  have hfull := orInputLine_boxes w b c true
  change (orInputLine w).boxes (orInputFixed w b c) (w+5) = orInputBoxes w b c true at hfull
  change Reachable (orBoard w goals) (some 1)
    ⟨point w 1 1, (orInputLine w).boxes (orInputFixed w b c) (w+5)⟩
    ⟨point w 1 1, (orInputLine w).boxes (orInputFixed w b c) 0⟩ at hr
  rw [hfull, hzero, orInputBoxes_false] at hr
  exact hfirst.trans hr

/-- With the output retracted, finish A from the right-mouth entrance. -/
theorem or_A_forward (w : ℕ) (hw : 2 ≤ w) (b : Bool)
    (goals : Finset (Cell (side w) (side w)))
    (hconnect : Reachable (orBoard w goals) (some 1)
      ⟨point w 1 1, orInputBoxes w b false true⟩
      ⟨point w (w+5) 1, orInputBoxes w b false true⟩) :
    Reachable (orBoard w goals) (some 1)
      ⟨point w 1 1, orBoxes w false b false⟩
      ⟨point w (w+5) 1, orBoxes w true b false⟩ := by
  have hfinish := or_A_left_prepared w hw b goals
  have hp : orPreparedBoxes w b = orInputBoxes w b false true := by
    unfold orPreparedBoxes
    have hl : orCell w false b false .triggerA = point w 3 0 := by
      apply Prod.ext <;> apply Fin.ext <;> dsimp [orCell, orPoint, point]
    have hn : orCell w true b false .triggerA = point w 2 0 := by
      apply Prod.ext <;> apply Fin.ext <;> dsimp [orCell, orPoint, point]
    rw [hl, hn]
    exact orInputBoxes_true w hw b false
  rw [hp] at hfinish
  exact (or_A_tail_forward w hw b false goals).trans (hconnect.trans hfinish)

/-- Relocating a row box preserves every free cell off that row. -/
private theorem free_relocated {W H : ℕ} {B : Board W H} {boxes : Finset (Cell W H)}
    {old next p : Cell W H} (hp : Free B boxes p) (hrow : p.2 ≠ next.2) :
    Free B (insert next (boxes.erase old)) p := by
  refine ⟨hp.1, ?_⟩
  intro hm
  rcases Finset.mem_insert.mp hm with he | he
  · exact hrow (congrArg Prod.snd he)
  · exact hp.2 (Finset.mem_of_mem_erase he)

private theorem orInput_above_B (w : ℕ) (hw : 2 ≤ w) (c : Bool)
    (goals : Finset (Cell (side w) (side w))) (p : Cell (side w) (side w))
    (hy : p.2.val+1 = origin w) (hx : origin w+1 ≤ p.1.val) (hx' : p.1.val ≤ origin w+4) :
    Free (orBoard w goals) (orInputBoxes w true c true) p := by
  rw [← orInputBoxes_true w hw true c]
  apply free_relocated
  · apply or_above_free w hw true true c goals p hy (by omega) (Or.inl hx') (Or.inr rfl)
  · intro he
    have he' := congrArg Fin.val he
    dsimp [point] at he'
    omega

/-- When B is open, the prepared A trigger is reached along the actual upper row. -/
theorem or_A_connect_B (w : ℕ) (hw : 2 ≤ w) (c : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (orBoard w goals) (some 1)
      ⟨point w 1 1, orInputBoxes w true c true⟩
      ⟨point w 4 1, orInputBoxes w true c true⟩ := by
  have hfull := orInputLine_boxes w true c true
  change (orInputLine w).boxes (orInputFixed w true c) (w+5) = orInputBoxes w true c true at hfull
  have hboxes : Disjoint (orInputBoxes w true c true) (orBoard w goals).walls := by
    rw [← hfull]
    exact (orInputFrame w hw true c goals).boxes_floor _
  apply walk_horizontal hboxes (point w 1 1).1 (point w 4 1).1 (point w 1 1).2
  intro x hx hx'
  apply orInput_above_B w hw c goals
  all_goals dsimp [point] at *; unfold origin at *; omega

/-- Finish the prepared OR A trigger through the open B entrance. -/
private theorem or_A_finish_B (w : ℕ) (hw : 2 ≤ w) (c : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (orBoard w goals) (some 1)
      ⟨point w 4 1, orInputBoxes w true c true⟩
      ⟨point w 4 1, orBoxes w true true c⟩ := by
  rw [← orInputBoxes_true w hw true c]
  have hnormal : point w 2 0 ∈ orBoxes w true true c := by
    have he : orCell w true true c .triggerA = point w 2 0 := by
      apply Prod.ext <;> apply Fin.ext <;> dsimp [orCell, orPoint, point]
    rw [← he]
    exact Finset.mem_image.mpr ⟨.triggerA, Finset.mem_univ _, rfl⟩
  refine finish_left_via_mouth (orBoxes_disjoint_walls w hw true true c)
    (point w 4 1).1 (point w 4 0).1 (point w 3 0).1 (point w 2 0).1
    (point w 4 1).2 (point w 4 0).2 ?_ ?_ ?_ ?_ ?_ hnormal ?_ ?_ ?_
  · dsimp [Adjacent, point]; unfold origin; omega
  · dsimp [Adjacent, point]; unfold origin; omega
  · dsimp [Adjacent, point]; omega
  · dsimp [Adjacent, point]; omega
  · dsimp [point]; omega
  · apply or_row_free w hw true true c goals
    all_goals simp only [point, Bool.toNat_true]; have hc := Bool.toNat_le c; omega
  · apply or_above_free w hw true true c goals
    all_goals dsimp only [point]
    all_goals first | exact Or.inr rfl | (unfold origin; omega)
  · intro x hx hx'
    apply or_row_free w hw true true c goals
    all_goals simp only [point, Bool.toNat_true] at *; have hc := Bool.toNat_le c; omega

/-- Update every OR left-tail box and A through the available B entrance. -/
theorem or_A_forward_B (w : ℕ) (hw : 2 ≤ w) (c : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (orBoard w goals) (some 1)
      ⟨point w 1 1, orBoxes w false true c⟩
      ⟨point w 4 1, orBoxes w true true c⟩ :=
  (or_A_tail_forward w hw true c goals).trans
    ((or_A_connect_B w hw c goals).trans (or_A_finish_B w hw c goals))

end PushPuzzle.PushS.FiniteGateInputs
