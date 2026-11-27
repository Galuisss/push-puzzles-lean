/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateMacros

/-! Complete the input branch by pushing its final prepared trigger into its normal slot. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGatePrepared

open PushFS FiniteGeometry FiniteGateCore FiniteGateMacros

attribute [local irreducible] side

/-- Fill a missing normal slot by pushing the prepared boundary from the right mouth. -/
theorem finish_left_via_mouth {W H : ℕ} {B : Board W H} {boxes : Finset (Cell W H)}
    (hboxes : Disjoint boxes B.walls) (mouth support old normal : Fin W) (u y : Fin H)
    (hentry : Adjacent .south (mouth, u) (mouth, y))
    (hexit : Adjacent .north (mouth, y) (mouth, u))
    (hax : Adjacent .west (support, y) (old, y))
    (hxn : Adjacent .west (old, y) (normal, y)) (hmouth : support.val ≤ mouth.val)
    (hnormal : (normal, y) ∈ boxes) (hold : Free B boxes (old, y))
    (hupper : Free B boxes (mouth, u))
    (hrow : ∀ x : Fin W, old.val < x.val → x.val ≤ mouth.val → Free B boxes (x, y)) :
    Reachable B (some 1) ⟨(mouth, u), insert (old, y) (boxes.erase (normal, y))⟩
      ⟨(mouth, u), boxes⟩ := by
  have hprepared : Disjoint (insert (old, y) (boxes.erase (normal, y))) B.walls :=
    Finset.disjoint_insert_left.mpr ⟨hold.1, hboxes.mono_left (Finset.erase_subset _ _)⟩
  have hrestore : insert (normal, y)
      ((insert (old, y) (boxes.erase (normal, y))).erase (old, y)) = boxes := by
    rw [Finset.erase_insert (fun hm => hold.2 (Finset.mem_of_mem_erase hm))]
    exact Finset.insert_erase hnormal
  have hnew : Free B (insert (old, y) (boxes.erase (normal, y))) (normal, y) := by
    refine ⟨fun hw => Finset.disjoint_left.mp hboxes hnormal hw, ?_⟩
    intro hm
    rcases Finset.mem_insert.mp hm with he | he
    · exact hxn.ne he.symm
    · exact (Finset.mem_erase.mp he).1 rfl
  have hupper' : Free B (insert (old, y) (boxes.erase (normal, y))) (mouth, u) := by
    refine ⟨hupper.1, ?_⟩
    intro hm
    rcases Finset.mem_insert.mp hm with he | he
    · have hrowne : u ≠ y := fun hu => hentry.ne (by rw [hu])
      exact hrowne (congrArg Prod.snd he)
    · exact hupper.2 (Finset.mem_of_mem_erase he)
  have hrow' : ∀ x : Fin W, old.val < x.val → x.val ≤ mouth.val →
      Free B (insert (old, y) (boxes.erase (normal, y))) (x, y) := by
    intro x hx hx'
    have hf := hrow x hx hx'
    refine ⟨hf.1, ?_⟩
    intro hm
    rcases Finset.mem_insert.mp hm with he | he
    · have hxe : x.val = old.val := congrArg (fun p : Cell W H => p.1.val) he
      omega
    · exact hf.2 (Finset.mem_of_mem_erase he)
  have hr := push_left_via_mouth hprepared mouth support old normal u y
    hentry hexit hax hxn hmouth (Finset.mem_insert_self _ _) hnew hupper' hrow'
  simpa only [hrestore] using hr

/-- All AND input auxiliary boxes are updated; A retains its old slot. -/
def andPreparedBoxes (w : ℕ) (b : Bool) : Finset (Cell (side w) (side w)) :=
  insert (andCell w false b false .triggerA)
    ((andBoxes w true b false).erase (andCell w true b false .triggerA))

/-- All OR left-tail boxes are updated; A retains its old slot. -/
def orPreparedBoxes (w : ℕ) (b : Bool) : Finset (Cell (side w) (side w)) :=
  insert (orCell w false b false .triggerA)
    ((orBoxes w true b false).erase (orCell w true b false .triggerA))

/-- The final AND input push restores the complete new normal inventory. -/
theorem and_A_left_prepared (w : ℕ) (hw : 2 ≤ w) (b : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (andBoard w goals) (some 1)
      ⟨point w (w+4) 1, andPreparedBoxes w b⟩
      ⟨point w (w+4) 1, andBoxes w true b false⟩ := by
  have hold : andCell w false b false .triggerA = point w 3 0 := by
    apply Prod.ext <;> apply Fin.ext <;> dsimp [andCell, andPoint, point]
  have hnormal : andCell w true b false .triggerA = point w 2 0 := by
    apply Prod.ext <;> apply Fin.ext <;> dsimp [andCell, andPoint, point]
  unfold andPreparedBoxes
  rw [hold, hnormal]
  have hmem : point w 2 0 ∈ andBoxes w true b false := by
    rw [← hnormal]
    exact Finset.mem_image.mpr ⟨.triggerA, Finset.mem_univ _, rfl⟩
  refine finish_left_via_mouth (andBoxes_disjoint_walls w hw true b false)
    (point w (w+4) 1).1 (point w 4 0).1 (point w 3 0).1 (point w 2 0).1
    (point w (w+4) 1).2 (point w 4 0).2 ?_ ?_ ?_ ?_ ?_ hmem ?_ ?_ ?_
  · dsimp [Adjacent, point]; unfold origin; omega
  · dsimp [Adjacent, point]; unfold origin; omega
  · dsimp [Adjacent, point]; omega
  · dsimp [Adjacent, point]; omega
  · dsimp [point]; omega
  · apply and_row_free w hw true b false goals
    all_goals simp only [point, Bool.toNat_true, Bool.toNat_false]; omega
  · apply and_above_free w hw true b false goals
    all_goals dsimp only [point]; unfold origin; omega
  · intro x hx hx'
    apply and_row_free w hw true b false goals
    all_goals simp only [point, Bool.toNat_true, Bool.toNat_false] at *; omega

/-- The final OR input push restores the complete new normal inventory. -/
theorem or_A_left_prepared (w : ℕ) (hw : 2 ≤ w) (b : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (orBoard w goals) (some 1)
      ⟨point w (w+5) 1, orPreparedBoxes w b⟩
      ⟨point w (w+5) 1, orBoxes w true b false⟩ := by
  have hold : orCell w false b false .triggerA = point w 3 0 := by
    apply Prod.ext <;> apply Fin.ext <;> dsimp [orCell, orPoint, point]
  have hnormal : orCell w true b false .triggerA = point w 2 0 := by
    apply Prod.ext <;> apply Fin.ext <;> dsimp [orCell, orPoint, point]
  unfold orPreparedBoxes
  rw [hold, hnormal]
  have hmem : point w 2 0 ∈ orBoxes w true b false := by
    rw [← hnormal]
    exact Finset.mem_image.mpr ⟨.triggerA, Finset.mem_univ _, rfl⟩
  refine finish_left_via_mouth (orBoxes_disjoint_walls w hw true b false)
    (point w (w+5) 1).1 (point w 4 0).1 (point w 3 0).1 (point w 2 0).1
    (point w (w+5) 1).2 (point w 4 0).2 ?_ ?_ ?_ ?_ ?_ hmem ?_ ?_ ?_
  · dsimp [Adjacent, point]; unfold origin; omega
  · dsimp [Adjacent, point]; unfold origin; omega
  · dsimp [Adjacent, point]; omega
  · dsimp [Adjacent, point]; omega
  · dsimp [point]; omega
  · apply or_row_free w hw true b false goals
    all_goals simp only [point, Bool.toNat_true, Bool.toNat_false]; omega
  · apply or_above_free w hw true b false goals
    all_goals dsimp only [point]; unfold origin; omega
  · intro x hx hx'
    apply or_row_free w hw true b false goals
    all_goals simp only [point, Bool.toNat_true, Bool.toNat_false] at *; omega

end PushPuzzle.PushS.FiniteGatePrepared
