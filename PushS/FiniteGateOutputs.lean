/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGatePrepared
public import PushS.FiniteLineMacros

/-! Complete output-branch propagation through every normal stock box. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGateOutputs

open PushFS FiniteGeometry FiniteGateCore FiniteGateMacros FiniteLineMacros

attribute [local irreducible] side

/-- The output tail after its first trigger, with its exposed upper walking lane. -/
def outputLine (w shift : ℕ) (hs : shift ≤ 8 := by omega) : Line (side w) (side w) where
  count := w+4
  base := origin w+w+shift
  base_pos := by unfold origin; omega
  fits := by unfold origin side; omega
  row := (point w (w+shift) 0).2
  lane := (point w (w+shift) 1).2
  entry := .south
  crossing := by intro x; dsimp [Adjacent, point]; unfold origin; omega
  hub := (point w (w+shift) 1).1

def andOutputKeep {w : ℕ} : AndLabel w → Bool
  | .branchC i => decide (i = 0)
  | _ => true

def andOutputFixed (w : ℕ) (a b : Bool) : Finset (Cell (side w) (side w)) :=
  (Finset.univ.filter fun l => andOutputKeep l).image (andCell w a b true)

/-- C is already contracted; the rest of its output branch has phase `q`. -/
def andOutputCell (w : ℕ) (a b q : Bool) (l : AndLabel w) : Cell (side w) (side w) :=
  match l with
  | .branchC i => andCell w a b (if i = 0 then true else q) l
  | _ => andCell w a b true l

def andOutputBoxes (w : ℕ) (a b q : Bool) : Finset (Cell (side w) (side w)) :=
  Finset.univ.image (andOutputCell w a b q)

private theorem andOutputCell_kept (w : ℕ) (a b q : Bool) (l : AndLabel w)
    (hl : andOutputKeep l = true) : andOutputCell w a b q l = andCell w a b true l := by
  cases l <;> try rfl
  rename_i i
  have hi : i = 0 := by simpa only [andOutputKeep, decide_eq_true_eq] using hl
  subst i
  rfl

private theorem andOutputFixed_free (w : ℕ) (hw : 2 ≤ w) (a b : Bool)
    (goals : Finset (Cell (side w) (side w))) (p : Cell (side w) (side w))
    (hx : origin w+w+5 ≤ p.1.val) (hy : p.2.val ≤ origin w)
    (hopen : p.2.val = origin w ∨ origin w+w+4 ≤ p.1.val) :
    Free (andBoard w goals) (andOutputFixed w a b) p := by
  refine ⟨and_core_floor w hw p (by omega) hy (hopen.imp id Or.inr), ?_⟩
  intro hp
  obtain ⟨l, hl, he⟩ := Finset.mem_image.mp hp
  have hkeep := (Finset.mem_filter.mp hl).2
  have hpx := congrArg (fun p => p.1.val) he
  have hpy := congrArg (fun p => p.2.val) he
  have ha := Bool.toNat_le a
  have hb := Bool.toNat_le b
  cases l <;> dsimp only [andCell, andPoint, origin] at hpx hpy hx hy
  all_goals try omega
  rename_i i
  have hi : i = 0 := by simpa only [andOutputKeep, decide_eq_true_eq] using hkeep
  subst i
  simp only [Fin.val_zero, Bool.toNat_true] at hpx
  omega

/-- All unrelated boxes and virtual walls satisfy the complete output-tail frame. -/
theorem andOutputFrame (w : ℕ) (hw : 2 ≤ w) (a b : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    (outputLine w 6).Frame (andBoard w goals) (andOutputFixed w a b) := by
  constructor
  · apply (andBoxes_disjoint_walls w hw a b true).mono_left
    intro p hp
    obtain ⟨l, hluniv, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_image.mpr ⟨l, Finset.mem_univ _, rfl⟩
  · intro x hx
    apply andOutputFixed_free w hw a b goals
    all_goals dsimp [Line.track, outputLine, point] at *; unfold origin at *; omega
  · intro x hx
    apply andOutputFixed_free w hw a b goals
    all_goals dsimp [Line.laneSegment, outputLine, point] at *; unfold origin at *; omega

private theorem andOutputLine_position (w : ℕ) (a b q : Bool) (i : Fin (w+4)) :
    (outputLine w 6).position (if q then w+4 else 0) i =
      andOutputCell w a b q (.branchC i.succ) := by
  have hi : i.succ ≠ (0 : Fin (w+5)) := by
    intro he
    have he' := congrArg Fin.val he
    dsimp at he'
    omega
  have hbound := i.isLt
  cases q <;> apply Prod.ext <;> apply Fin.ext <;>
    simp [outputLine, Line.position, point, andOutputCell, andCell, andPoint, hi, hbound, origin]
  all_goals omega

/-- The line frontier endpoints exactly enumerate the complete mixed gate inventory. -/
theorem andOutputLine_boxes (w : ℕ) (a b q : Bool) :
    (outputLine w 6).boxes (andOutputFixed w a b) (if q then w+4 else 0) =
      andOutputBoxes w a b q := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hp
      have hkeep := (Finset.mem_filter.mp hl).2
      exact Finset.mem_image.mpr ⟨l, Finset.mem_univ _, andOutputCell_kept w a b q l hkeep⟩
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_image.mpr ⟨.branchC i.succ, Finset.mem_univ _,
        (andOutputLine_position w a b q i).symm⟩
  · intro hp
    obtain ⟨l, hluniv, rfl⟩ := Finset.mem_image.mp hp
    by_cases hkeep : andOutputKeep l = true
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkeep⟩,
        (andOutputCell_kept w a b q l hkeep).symm⟩
    · cases l <;> try exact False.elim (hkeep rfl)
      rename_i i
      have hi : i ≠ 0 := by
        intro he
        subst i
        exact hkeep (by rfl)
      let j : Fin (w+4) := ⟨i.val-1, by have := i.isLt; omega⟩
      have hival := Fin.val_ne_of_ne hi
      simp only [Fin.val_zero] at hival
      have hj : j.succ = i := by apply Fin.ext; dsimp [j]; omega
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, by
        rw [andOutputLine_position, hj]⟩

theorem andOutputBoxes_true (w : ℕ) (a b : Bool) :
    andOutputBoxes w a b true = andBoxes w a b true := by
  unfold andOutputBoxes andBoxes
  congr 1
  funext l
  cases l <;> simp [andOutputCell]

/-- The initial C contraction creates precisely the propagation frontier with its tail old. -/
theorem andOutputBoxes_initial (w : ℕ) (hw : 2 ≤ w) (a b : Bool) :
    insert (point w (w+4) 0) ((andBoxes w a b false).erase (point w (w+5) 0)) =
      andOutputBoxes w a b false := by
  have he := Line.image_relocate (andCell w a b false) (andOutputCell w a b false)
    (andCell_injective w hw a b false) (.branchC 0) (by
      intro l hl
      cases l <;> try rfl
      rename_i i
      have hi : i ≠ 0 := fun h => hl (by rw [h])
      simp only [andOutputCell, hi, ite_false])
  have hlow : andOutputCell w a b false (.branchC 0) = point w (w+4) 0 := by
    apply Prod.ext <;> apply Fin.ext <;> dsimp [andOutputCell, andCell, andPoint, point]; omega
  have hhigh : andCell w a b false (.branchC 0) = point w (w+5) 0 := by
    apply Prod.ext <;> apply Fin.ext <;> dsimp [andCell, andPoint, point]; omega
  simpa only [andBoxes, andOutputBoxes, hlow, hhigh] using he

/-- Contract the complete AND output branch, updating every stock box by single pushes. -/
theorem and_C_forward (w : ℕ) (hw : 2 ≤ w) (a b : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (andBoard w goals) (some 1)
      ⟨point w (w+6) 1, andBoxes w a b false⟩
      ⟨point w (w+6) 1, andBoxes w a b true⟩ := by
  have hfirst := and_C_left w hw a b goals
  rw [andOutputBoxes_initial w hw a b] at hfirst
  have htail := (andOutputFrame w hw a b goals).forward
  have hzero := andOutputLine_boxes w a b false
  change (outputLine w 6).boxes (andOutputFixed w a b) 0 = andOutputBoxes w a b false at hzero
  have hfull := andOutputLine_boxes w a b true
  change (outputLine w 6).boxes (andOutputFixed w a b) (w+4) = andOutputBoxes w a b true at hfull
  change Reachable (andBoard w goals) (some 1)
    ⟨point w (w+6) 1, (outputLine w 6).boxes (andOutputFixed w a b) 0⟩
    ⟨point w (w+6) 1, (outputLine w 6).boxes (andOutputFixed w a b) (w+4)⟩ at htail
  rw [hzero, hfull, andOutputBoxes_true] at htail
  exact hfirst.trans htail

def orOutputKeep {w : ℕ} : OrLabel w → Bool
  | .branchC i => decide (i = 0)
  | _ => true

def orOutputFixed (w : ℕ) (a b : Bool) : Finset (Cell (side w) (side w)) :=
  (Finset.univ.filter fun l => orOutputKeep l).image (orCell w a b true)

/-- C is already contracted; the rest of its output branch has phase `q`. -/
def orOutputCell (w : ℕ) (a b q : Bool) (l : OrLabel w) : Cell (side w) (side w) :=
  match l with
  | .branchC i => orCell w a b (if i = 0 then true else q) l
  | _ => orCell w a b true l

def orOutputBoxes (w : ℕ) (a b q : Bool) : Finset (Cell (side w) (side w)) :=
  Finset.univ.image (orOutputCell w a b q)

private theorem orOutputCell_kept (w : ℕ) (a b q : Bool) (l : OrLabel w)
    (hl : orOutputKeep l = true) : orOutputCell w a b q l = orCell w a b true l := by
  cases l <;> try rfl
  rename_i i
  have hi : i = 0 := by simpa only [orOutputKeep, decide_eq_true_eq] using hl
  subst i
  rfl

private theorem orOutputFixed_free (w : ℕ) (hw : 2 ≤ w) (a b : Bool)
    (goals : Finset (Cell (side w) (side w))) (p : Cell (side w) (side w))
    (hx : origin w+w+6 ≤ p.1.val) (hy : p.2.val ≤ origin w)
    (hopen : p.2.val = origin w ∨ origin w+w+5 ≤ p.1.val) :
    Free (orBoard w goals) (orOutputFixed w a b) p := by
  refine ⟨or_core_floor w hw p (by omega) hy (hopen.imp id Or.inr), ?_⟩
  intro hp
  obtain ⟨l, hl, he⟩ := Finset.mem_image.mp hp
  have hkeep := (Finset.mem_filter.mp hl).2
  have hpx := congrArg (fun p => p.1.val) he
  have hpy := congrArg (fun p => p.2.val) he
  have ha := Bool.toNat_le a
  have hb := Bool.toNat_le b
  cases l <;> dsimp only [orCell, orPoint, origin] at hpx hpy hx hy
  all_goals try omega
  rename_i i
  have hi : i = 0 := by simpa only [orOutputKeep, decide_eq_true_eq] using hkeep
  subst i
  simp only [Fin.val_zero, Bool.toNat_true] at hpx
  omega

/-- All unrelated boxes and virtual walls satisfy the complete output-tail frame. -/
theorem orOutputFrame (w : ℕ) (hw : 2 ≤ w) (a b : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    (outputLine w 7).Frame (orBoard w goals) (orOutputFixed w a b) := by
  constructor
  · apply (orBoxes_disjoint_walls w hw a b true).mono_left
    intro p hp
    obtain ⟨l, hluniv, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_image.mpr ⟨l, Finset.mem_univ _, rfl⟩
  · intro x hx
    apply orOutputFixed_free w hw a b goals
    all_goals dsimp [Line.track, outputLine, point] at *; unfold origin at *; omega
  · intro x hx
    apply orOutputFixed_free w hw a b goals
    all_goals dsimp [Line.laneSegment, outputLine, point] at *; unfold origin at *; omega

private theorem orOutputLine_position (w : ℕ) (a b q : Bool) (i : Fin (w+4)) :
    (outputLine w 7).position (if q then w+4 else 0) i =
      orOutputCell w a b q (.branchC i.succ) := by
  have hi : i.succ ≠ (0 : Fin (w+5)) := by
    intro he
    have he' := congrArg Fin.val he
    dsimp at he'
    omega
  have hbound := i.isLt
  cases q <;> apply Prod.ext <;> apply Fin.ext <;>
    simp [outputLine, Line.position, point, orOutputCell, orCell, orPoint, hi, hbound, origin]
  all_goals omega

/-- The line frontier endpoints exactly enumerate the complete mixed gate inventory. -/
theorem orOutputLine_boxes (w : ℕ) (a b q : Bool) :
    (outputLine w 7).boxes (orOutputFixed w a b) (if q then w+4 else 0) =
      orOutputBoxes w a b q := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hp
      have hkeep := (Finset.mem_filter.mp hl).2
      exact Finset.mem_image.mpr ⟨l, Finset.mem_univ _, orOutputCell_kept w a b q l hkeep⟩
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_image.mpr ⟨.branchC i.succ, Finset.mem_univ _,
        (orOutputLine_position w a b q i).symm⟩
  · intro hp
    obtain ⟨l, hluniv, rfl⟩ := Finset.mem_image.mp hp
    by_cases hkeep : orOutputKeep l = true
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkeep⟩,
        (orOutputCell_kept w a b q l hkeep).symm⟩
    · cases l <;> try exact False.elim (hkeep rfl)
      rename_i i
      have hi : i ≠ 0 := by
        intro he
        subst i
        exact hkeep (by rfl)
      let j : Fin (w+4) := ⟨i.val-1, by have := i.isLt; omega⟩
      have hival := Fin.val_ne_of_ne hi
      simp only [Fin.val_zero] at hival
      have hj : j.succ = i := by apply Fin.ext; dsimp [j]; omega
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, by
        rw [orOutputLine_position, hj]⟩

theorem orOutputBoxes_true (w : ℕ) (a b : Bool) :
    orOutputBoxes w a b true = orBoxes w a b true := by
  unfold orOutputBoxes orBoxes
  congr 1
  funext l
  cases l <;> simp [orOutputCell]

/-- The initial C contraction creates precisely the propagation frontier with its tail old. -/
theorem orOutputBoxes_initial (w : ℕ) (hw : 2 ≤ w) (a b : Bool) :
    insert (point w (w+5) 0) ((orBoxes w a b false).erase (point w (w+6) 0)) =
      orOutputBoxes w a b false := by
  have he := Line.image_relocate (orCell w a b false) (orOutputCell w a b false)
    (orCell_injective w hw a b false) (.branchC 0) (by
      intro l hl
      cases l <;> try rfl
      rename_i i
      have hi : i ≠ 0 := fun h => hl (by rw [h])
      simp only [orOutputCell, hi, ite_false])
  have hlow : orOutputCell w a b false (.branchC 0) = point w (w+5) 0 := by
    apply Prod.ext <;> apply Fin.ext <;> dsimp [orOutputCell, orCell, orPoint, point]; omega
  have hhigh : orCell w a b false (.branchC 0) = point w (w+6) 0 := by
    apply Prod.ext <;> apply Fin.ext <;> dsimp [orCell, orPoint, point]; omega
  simpa only [orBoxes, orOutputBoxes, hlow, hhigh] using he

/-- Contract the complete OR output branch, updating every stock box by single pushes. -/
theorem or_C_forward (w : ℕ) (hw : 2 ≤ w) (a b : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (orBoard w goals) (some 1)
      ⟨point w (w+7) 1, orBoxes w a b false⟩
      ⟨point w (w+7) 1, orBoxes w a b true⟩ := by
  have hfirst := or_C_left w hw a b goals
  rw [orOutputBoxes_initial w hw a b] at hfirst
  have htail := (orOutputFrame w hw a b goals).forward
  have hzero := orOutputLine_boxes w a b false
  change (outputLine w 7).boxes (orOutputFixed w a b) 0 = orOutputBoxes w a b false at hzero
  have hfull := orOutputLine_boxes w a b true
  change (outputLine w 7).boxes (orOutputFixed w a b) (w+4) = orOutputBoxes w a b true at hfull
  change Reachable (orBoard w goals) (some 1)
    ⟨point w (w+7) 1, (outputLine w 7).boxes (orOutputFixed w a b) 0⟩
    ⟨point w (w+7) 1, (outputLine w 7).boxes (orOutputFixed w a b) (w+4)⟩ at htail
  rw [hzero, hfull, orOutputBoxes_true] at htail
  exact hfirst.trans htail

end PushPuzzle.PushS.FiniteGateOutputs
