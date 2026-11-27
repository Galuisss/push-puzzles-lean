/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateCore
public import PushFS.Walking
import Mathlib.Tactic.FinCases

/-! Concrete single-box trigger pushes in the parameterized thick gate cores. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGateMacros

open PushFS FiniteGeometry FiniteGateCore

/-- A cell near the horizontal gate core, with vertical offset measured upward. -/
def point (w x up : ℕ) (hx : x ≤ w + 8 := by omega) (hu : up ≤ 8 := by omega) :
    Cell (side w) (side w) :=
  (⟨origin w + x, by unfold origin side; omega⟩,
   ⟨origin w - up, by unfold origin side; omega⟩)

attribute [local irreducible] side

/-- The horizontal cavity and its exposed upper entrances avoid the AND walls. -/
theorem and_core_floor (w : ℕ) (hw : 2 ≤ w) (p : Cell (side w) (side w))
    (hx : origin w ≤ p.1.val) (hy : p.2.val ≤ origin w)
    (hopen : p.2.val = origin w ∨ p.1.val ≤ origin w + 3 ∨ origin w + w + 4 ≤ p.1.val) :
    p ∉ andWalls w := by
  intro hp
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
  have hi' := ((andRectangle w i).mem_cells _ _ _).mp hi
  fin_cases i <;> simp [andRectangle, origin] at hi' hx hy hopen <;> omega

theorem or_core_floor (w : ℕ) (hw : 2 ≤ w) (p : Cell (side w) (side w))
    (_hx : origin w ≤ p.1.val) (hy : p.2.val ≤ origin w)
    (hopen : p.2.val = origin w ∨ p.1.val ≤ origin w + 4 ∨ origin w + w + 5 ≤ p.1.val) :
    p ∉ orWalls w := by
  intro hp
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
  have hi' := ((orRectangle w i).mem_cells _ _ _).mp hi
  fin_cases i <;> simp [orRectangle, origin] at hi' _hx hy hopen <;> omega

/-- Free row cells between the left stock and first output box. -/
theorem and_row_free (w : ℕ) (hw : 2 ≤ w) (a b c : Bool)
    (goals : Finset (Cell (side w) (side w))) (p : Cell (side w) (side w))
    (hy : p.2.val = origin w) (hx : origin w + 1 ≤ p.1.val)
    (hD : origin w + 1 < p.1.val ∨ a = true)
    (hA : p.1.val + a.toNat ≠ origin w + 3)
    (hC : p.1.val + c.toNat < origin w + w + 5) :
    Free (andBoard w goals) (andBoxes w a b c) p := by
  refine ⟨and_core_floor w hw p (by omega) (by omega) (Or.inl hy), ?_⟩
  intro hp
  obtain ⟨l, _, he⟩ := Finset.mem_image.mp hp
  have hpx := congrArg (fun p => p.1.val) he
  have hpy := congrArg (fun p => p.2.val) he
  have ha := Bool.toNat_le a
  have hb := Bool.toNat_le b
  have hc := Bool.toNat_le c
  have hDnat : origin w + 1 < p.1.val ∨ a.toNat = 1 :=
    hD.imp id (fun h => by simp [h])
  cases l <;> dsimp only [andCell, andPoint, origin] at hpx hpy hx hDnat hA hC hy <;> dsimp only [origin] at * <;> omega

theorem or_row_free (w : ℕ) (hw : 2 ≤ w) (a b c : Bool)
    (goals : Finset (Cell (side w) (side w))) (p : Cell (side w) (side w))
    (hy : p.2.val = origin w) (hx : origin w + 1 ≤ p.1.val)
    (hD : origin w + 1 < p.1.val ∨ a = true)
    (hA : p.1.val + a.toNat ≠ origin w + 3)
    (hC : p.1.val + c.toNat < origin w + w + 6) :
    Free (orBoard w goals) (orBoxes w a b c) p := by
  refine ⟨or_core_floor w hw p (by omega) (by omega) (Or.inl hy), ?_⟩
  intro hp
  obtain ⟨l, _, he⟩ := Finset.mem_image.mp hp
  have hpx := congrArg (fun p => p.1.val) he
  have hpy := congrArg (fun p => p.2.val) he
  have ha := Bool.toNat_le a
  have hb := Bool.toNat_le b
  have hc := Bool.toNat_le c
  have hDnat : origin w + 1 < p.1.val ∨ a.toNat = 1 :=
    hD.imp id (fun h => by simp [h])
  cases l <;> dsimp only [orCell, orPoint, origin] at hpx hpy hx hDnat hA hC hy <;> dsimp only [origin] at * <;> omega

/-- The upper row is open on the exposed side of each AND wall. -/
theorem and_above_free (w : ℕ) (hw : 2 ≤ w) (a b c : Bool)
    (goals : Finset (Cell (side w) (side w))) (p : Cell (side w) (side w))
    (hy : p.2.val + 1 = origin w) (hx : origin w ≤ p.1.val)
    (hwall : p.1.val ≤ origin w + 3 ∨ origin w + w + 4 ≤ p.1.val)
    (hB : p.1.val ≠ origin w + 3 ∨ b = true) :
    Free (andBoard w goals) (andBoxes w a b c) p := by
  refine ⟨and_core_floor w hw p hx (by omega) (Or.inr hwall), ?_⟩
  intro hp
  obtain ⟨l, _, he⟩ := Finset.mem_image.mp hp
  have hpx := congrArg (fun p => p.1.val) he
  have hpy := congrArg (fun p => p.2.val) he
  have ha := Bool.toNat_le a
  have hb := Bool.toNat_le b
  have hc := Bool.toNat_le c
  have hBnat : p.1.val ≠ origin w + 3 ∨ b.toNat = 1 :=
    hB.imp id (fun h => by simp [h])
  cases l <;> dsimp only [andCell, andPoint, origin] at hpx hpy hx hBnat hy <;> dsimp only [origin] at * <;> omega

theorem or_above_free (w : ℕ) (hw : 2 ≤ w) (a b c : Bool)
    (goals : Finset (Cell (side w) (side w))) (p : Cell (side w) (side w))
    (hy : p.2.val + 1 = origin w) (hx : origin w ≤ p.1.val)
    (hwall : p.1.val ≤ origin w + 4 ∨ origin w + w + 5 ≤ p.1.val)
    (hB : p.1.val ≠ origin w + 4 ∨ b = true) :
    Free (orBoard w goals) (orBoxes w a b c) p := by
  refine ⟨or_core_floor w hw p hx (by omega) (Or.inr hwall), ?_⟩
  intro hp
  obtain ⟨l, _, he⟩ := Finset.mem_image.mp hp
  have hpx := congrArg (fun p => p.1.val) he
  have hpy := congrArg (fun p => p.2.val) he
  have ha := Bool.toNat_le a
  have hb := Bool.toNat_le b
  have hc := Bool.toNat_le c
  have hBnat : p.1.val ≠ origin w + 4 ∨ b.toNat = 1 :=
    hB.imp id (fun h => by simp [h])
  cases l <;> dsimp only [orCell, orPoint, origin] at hpx hpy hx hBnat hy <;> dsimp only [origin] at * <;> omega

/-- Empty cells around the first output box, before the next stock box. -/
private theorem and_output_gap_free (w : ℕ) (hw : 2 ≤ w) (a b c : Bool)
    (goals : Finset (Cell (side w) (side w))) (p : Cell (side w) (side w))
    (hy : p.2.val = origin w) (hx : origin w + w + 4 ≤ p.1.val)
    (hC : p.1.val + c.toNat ≠ origin w + w + 5)
    (hR : p.1.val + c.toNat < origin w + w + 7) :
    Free (andBoard w goals) (andBoxes w a b c) p := by
  refine ⟨and_core_floor w hw p (by omega) (by omega) (Or.inl hy), ?_⟩
  intro hp
  obtain ⟨l, _, he⟩ := Finset.mem_image.mp hp
  have hpx := congrArg (fun p => p.1.val) he
  have hpy := congrArg (fun p => p.2.val) he
  have ha := Bool.toNat_le a
  have hb := Bool.toNat_le b
  have hc := Bool.toNat_le c
  cases l <;> dsimp only [andCell, andPoint, origin] at hpx hpy hx hC hR hy <;> omega

/-- Empty cells around the first output box, before the next stock box. -/
private theorem or_output_gap_free (w : ℕ) (hw : 2 ≤ w) (a b c : Bool)
    (goals : Finset (Cell (side w) (side w))) (p : Cell (side w) (side w))
    (hy : p.2.val = origin w) (hx : origin w + w + 5 ≤ p.1.val)
    (hC : p.1.val + c.toNat ≠ origin w + w + 6)
    (hR : p.1.val + c.toNat < origin w + w + 8) :
    Free (orBoard w goals) (orBoxes w a b c) p := by
  refine ⟨or_core_floor w hw p (by omega) (by omega) (Or.inl hy), ?_⟩
  intro hp
  obtain ⟨l, _, he⟩ := Finset.mem_image.mp hp
  have hpx := congrArg (fun p => p.1.val) he
  have hpy := congrArg (fun p => p.2.val) he
  have ha := Bool.toNat_le a
  have hb := Bool.toNat_le b
  have hc := Bool.toNat_le c
  cases l <;> dsimp only [orCell, orPoint, origin] at hpx hpy hx hC hR hy <;> omega

/-- Enter a roofed horizontal cavity through its right mouth, push its left
boundary left, and walk back to the same mouth. -/
theorem push_left_via_mouth {W H : ℕ} {B : Board W H} {boxes : Finset (Cell W H)}
    (hboxes : Disjoint boxes B.walls) (mouth support src dst : Fin W) (u y : Fin H)
    (hentry : Adjacent .south (mouth, u) (mouth, y))
    (hexit : Adjacent .north (mouth, y) (mouth, u))
    (hax : Adjacent .west (support, y) (src, y))
    (hxd : Adjacent .west (src, y) (dst, y)) (hmouth : support.val ≤ mouth.val)
    (hsource : (src, y) ∈ boxes) (hdest : Free B boxes (dst, y))
    (hupper : Free B boxes (mouth, u))
    (hrow : ∀ x : Fin W, src.val < x.val → x.val ≤ mouth.val → Free B boxes (x, y)) :
    Reachable B (some 1) ⟨(mouth, u), boxes⟩
      ⟨(mouth, u), insert (dst, y) (boxes.erase (src, y))⟩ := by
  have hax' := hax
  have hxd' := hxd
  simp only [Adjacent] at hax' hxd'
  have hmouthfree := hrow mouth (by omega) (by omega)
  have hsupport := hrow support (by omega) hmouth
  have hdown : SingleMoveView B .south (⟨(mouth, u), boxes⟩ : State W H) ⟨(mouth, y), boxes⟩ :=
    SingleMoveView.walk ⟨hupper.1, hboxes, hupper.2⟩ hentry hmouthfree.1 hmouthfree.2
  have hin := walk_horizontal hboxes mouth support y (by
    intro x hx hx'
    apply hrow x <;> omega)
  have hpush : SingleMoveView B .west (⟨(support, y), boxes⟩ : State W H)
      ⟨(src, y), insert (dst, y) (boxes.erase (src, y))⟩ :=
    SingleMoveView.push ⟨hsupport.1, hboxes, hsupport.2⟩ hax hsource hxd hdest.1 hdest.2
  have hnewrow : ∀ x : Fin W, src.val ≤ x.val → x.val ≤ mouth.val →
      Free B (insert (dst, y) (boxes.erase (src, y))) (x, y) := by
    intro x hx hx'
    by_cases he : x = src
    · subst x
      refine ⟨fun hw => Finset.disjoint_left.mp hboxes hsource hw, ?_⟩
      intro hm
      rcases Finset.mem_insert.mp hm with he | he
      · have hxval : src.val = dst.val := congrArg (fun p : Cell W H => p.1.val) he
        omega
      · exact (Finset.mem_erase.mp he).1 rfl
    · have hf := hrow x (by have := Fin.val_ne_of_ne he; omega) hx'
      refine ⟨hf.1, ?_⟩
      intro hmem
      rcases Finset.mem_insert.mp hmem with he' | he'
      · have hxval : x.val = dst.val := congrArg (fun p : Cell W H => p.1.val) he'
        omega
      · exact hf.2 (Finset.mem_of_mem_erase he')
  have hout := walk_horizontal hpush.valid_target.2.1 src mouth y (by
    intro x hx hx'
    apply hnewrow x <;> omega)
  have hu_ne : u ≠ y := by
    intro he
    exact hentry.ne (by rw [he])
  have hupper' : Free B (insert (dst, y) (boxes.erase (src, y))) (mouth, u) := by
    refine ⟨hupper.1, ?_⟩
    intro hm
    rcases Finset.mem_insert.mp hm with he | he
    · exact hu_ne (congrArg Prod.snd he)
    · exact hupper.2 (Finset.mem_of_mem_erase he)
  have hup : SingleMoveView B .north
      (⟨(mouth, y), insert (dst, y) (boxes.erase (src, y))⟩ : State W H)
      ⟨(mouth, u), insert (dst, y) (boxes.erase (src, y))⟩ := SingleMoveView.walk
    ⟨(hnewrow mouth (by omega) (by omega)).1, hpush.valid_target.2.1,
      (hnewrow mouth (by omega) (by omega)).2⟩ hexit hupper'.1 hupper'.2
  exact (((Relation.ReflTransGen.single ⟨.south, Move.single_iff.mpr hdown⟩).trans hin).tail
    ⟨.west, Move.single_iff.mpr hpush⟩).trans (hout.tail ⟨.north, Move.single_iff.mpr hup⟩)

/-- Push A from its open slot to its closed slot and return above the left entrance. -/
theorem and_A_right (w : ℕ) (hw : 2 ≤ w) (b c : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (andBoard w goals) (some 1)
      ⟨point w 1 1, andBoxes w true b c⟩
      ⟨point w 1 1, insert (point w 3 0) ((andBoxes w true b c).erase (point w 2 0))⟩ := by
  have hsource : point w 2 0 ∈ andBoxes w true b c := by
    have he : andCell w true b c .triggerA = point w 2 0 := by
      apply Prod.ext <;> apply Fin.ext <;> dsimp [andCell, andPoint, point]
    rw [← he]
    exact Finset.mem_image.mpr ⟨.triggerA, Finset.mem_univ _, rfl⟩
  refine push_via_parallel_row (andBoxes_disjoint_walls w hw true b c)
    (point w 1 1).1 (point w 1 0).1 (point w 2 0).1 (point w 3 0).1
    (point w 1 1).2 (point w 1 0).2 .south .east ?_ ?_ ?_ ?_ ?_ hsource ?_ ?_ ?_
  · dsimp [Adjacent, point]; unfold origin; omega
  · dsimp [Adjacent, Direction.opposite, point]; unfold origin; omega
  · dsimp [Adjacent, point]; omega
  · dsimp [Adjacent, point]; omega
  · apply and_row_free w hw true b c goals
    all_goals simp only [point, Bool.toNat_true]
    all_goals first | exact Or.inr True.intro | (have hc := Bool.toNat_le c; unfold origin; omega)
  · apply and_row_free w hw true b c goals
    all_goals simp only [point, Bool.toNat_true]
    all_goals first | exact Or.inr True.intro | (have hc := Bool.toNat_le c; unfold origin; omega)
  · intro z hlo hhi
    apply and_above_free w hw true b c goals
    all_goals dsimp only [point] at *; unfold origin at *; omega
  · intro z hlo hhi
    apply and_above_free w hw true b c goals
    all_goals dsimp only [point] at *; unfold origin at *; omega

/-- Push A from its open slot to its closed slot and return above the left entrance. -/
theorem or_A_right (w : ℕ) (hw : 2 ≤ w) (b c : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (orBoard w goals) (some 1)
      ⟨point w 1 1, orBoxes w true b c⟩
      ⟨point w 1 1, insert (point w 3 0) ((orBoxes w true b c).erase (point w 2 0))⟩ := by
  have hsource : point w 2 0 ∈ orBoxes w true b c := by
    have he : orCell w true b c .triggerA = point w 2 0 := by
      apply Prod.ext <;> apply Fin.ext <;> dsimp [orCell, orPoint, point]
    rw [← he]
    exact Finset.mem_image.mpr ⟨.triggerA, Finset.mem_univ _, rfl⟩
  refine push_via_parallel_row (orBoxes_disjoint_walls w hw true b c)
    (point w 1 1).1 (point w 1 0).1 (point w 2 0).1 (point w 3 0).1
    (point w 1 1).2 (point w 1 0).2 .south .east ?_ ?_ ?_ ?_ ?_ hsource ?_ ?_ ?_
  · dsimp [Adjacent, point]; unfold origin; omega
  · dsimp [Adjacent, Direction.opposite, point]; unfold origin; omega
  · dsimp [Adjacent, point]; omega
  · dsimp [Adjacent, point]; omega
  · apply or_row_free w hw true b c goals
    all_goals simp only [point, Bool.toNat_true]
    all_goals first | exact Or.inr True.intro | (have hc := Bool.toNat_le c; unfold origin; omega)
  · apply or_row_free w hw true b c goals
    all_goals simp only [point, Bool.toNat_true]
    all_goals first | exact Or.inr True.intro | (have hc := Bool.toNat_le c; unfold origin; omega)
  · intro z hlo hhi
    apply or_above_free w hw true b c goals
    all_goals dsimp only [point] at *; unfold origin at *; omega
  · intro z hlo hhi
    apply or_above_free w hw true b c goals
    all_goals dsimp only [point] at *; unfold origin at *; omega

/-- Enter through the open right mouth, push A left, and return through that mouth. -/
theorem and_A_left (w : ℕ) (hw : 2 ≤ w) (b : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (andBoard w goals) (some 1)
      ⟨point w (w+4) 1, andBoxes w false b false⟩
      ⟨point w (w+4) 1,
        insert (point w 2 0) ((andBoxes w false b false).erase (point w 3 0))⟩ := by
  have hsource : point w 3 0 ∈ andBoxes w false b false := by
    have he : andCell w false b false .triggerA = point w 3 0 := by
      apply Prod.ext <;> apply Fin.ext <;> dsimp [andCell, andPoint, point]
    rw [← he]
    exact Finset.mem_image.mpr ⟨.triggerA, Finset.mem_univ _, rfl⟩
  refine push_left_via_mouth (andBoxes_disjoint_walls w hw false b false)
    (point w (w+4) 1).1 (point w 4 0).1 (point w 3 0).1 (point w 2 0).1
    (point w (w+4) 1).2 (point w 4 0).2 ?_ ?_ ?_ ?_ ?_ hsource ?_ ?_ ?_
  · dsimp [Adjacent, point]; unfold origin; omega
  · dsimp [Adjacent, point]; unfold origin; omega
  · dsimp [Adjacent, point]; omega
  · dsimp [Adjacent, point]; omega
  · dsimp [point]; omega
  · apply and_row_free w hw false b false goals
    all_goals simp only [point, Bool.toNat_false]; omega
  · apply and_above_free w hw false b false goals
    all_goals dsimp only [point]; unfold origin; omega
  · intro x hx hx'
    apply and_row_free w hw false b false goals
    all_goals simp only [point, Bool.toNat_false] at *; omega

/-- Enter through the open right mouth, push A left, and return through that mouth. -/
theorem or_A_left (w : ℕ) (hw : 2 ≤ w) (b : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (orBoard w goals) (some 1)
      ⟨point w (w+5) 1, orBoxes w false b false⟩
      ⟨point w (w+5) 1,
        insert (point w 2 0) ((orBoxes w false b false).erase (point w 3 0))⟩ := by
  have hsource : point w 3 0 ∈ orBoxes w false b false := by
    have he : orCell w false b false .triggerA = point w 3 0 := by
      apply Prod.ext <;> apply Fin.ext <;> dsimp [orCell, orPoint, point]
    rw [← he]
    exact Finset.mem_image.mpr ⟨.triggerA, Finset.mem_univ _, rfl⟩
  refine push_left_via_mouth (orBoxes_disjoint_walls w hw false b false)
    (point w (w+5) 1).1 (point w 4 0).1 (point w 3 0).1 (point w 2 0).1
    (point w (w+5) 1).2 (point w 4 0).2 ?_ ?_ ?_ ?_ ?_ hsource ?_ ?_ ?_
  · dsimp [Adjacent, point]; unfold origin; omega
  · dsimp [Adjacent, point]; unfold origin; omega
  · dsimp [Adjacent, point]; omega
  · dsimp [Adjacent, point]; omega
  · dsimp [point]; omega
  · apply or_row_free w hw false b false goals
    all_goals simp only [point, Bool.toNat_false]; omega
  · apply or_above_free w hw false b false goals
    all_goals dsimp only [point]; unfold origin; omega
  · intro x hx hx'
    apply or_row_free w hw false b false goals
    all_goals simp only [point, Bool.toNat_false] at *; omega

/-- With B open, the OR upper entrance directly supplies A's leftward push. -/
theorem or_A_left_via_B (w : ℕ) (hw : 2 ≤ w) (c : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (orBoard w goals) (some 1)
      ⟨point w 4 1, orBoxes w false true c⟩
      ⟨point w 4 1, insert (point w 2 0) ((orBoxes w false true c).erase (point w 3 0))⟩ := by
  have hsource : point w 3 0 ∈ orBoxes w false true c := by
    have he : orCell w false true c .triggerA = point w 3 0 := by
      apply Prod.ext <;> apply Fin.ext <;> dsimp [orCell, orPoint, point]
    rw [← he]
    exact Finset.mem_image.mpr ⟨.triggerA, Finset.mem_univ _, rfl⟩
  refine push_via_parallel_row (orBoxes_disjoint_walls w hw false true c)
    (point w 4 1).1 (point w 4 0).1 (point w 3 0).1 (point w 2 0).1
    (point w 4 1).2 (point w 4 0).2 .south .west ?_ ?_ ?_ ?_ ?_ hsource ?_ ?_ ?_
  · dsimp [Adjacent, point]; unfold origin; omega
  · dsimp [Adjacent, Direction.opposite, point]; unfold origin; omega
  · dsimp [Adjacent, point]; omega
  · dsimp [Adjacent, point]; omega
  · apply or_row_free w hw false true c goals
    all_goals simp only [point, Bool.toNat_false]; have hc := Bool.toNat_le c; omega
  · apply or_row_free w hw false true c goals
    all_goals simp only [point, Bool.toNat_false]; have hc := Bool.toNat_le c; omega
  · intro z hlo hhi
    apply or_above_free w hw false true c goals
    all_goals dsimp only [point] at *; unfold origin at *
    all_goals first | exact Or.inr rfl | omega
  · intro z hlo hhi
    apply or_above_free w hw false true c goals
    all_goals dsimp only [point] at *; unfold origin at *
    all_goals first | exact Or.inr rfl | omega

/-- Contract the output box by one cell and return to the exposed upper lane. -/
theorem and_C_left (w : ℕ) (hw : 2 ≤ w) (a b : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (andBoard w goals) (some 1)
      ⟨point w (w+6) 1, andBoxes w a b false⟩
      ⟨point w (w+6) 1,
        insert (point w (w+4) 0)
          ((andBoxes w a b false).erase (point w (w+5) 0))⟩ := by
  have hsource : point w (w+5) 0 ∈ andBoxes w a b false := by
    have he : andCell w a b false (.branchC 0) = point w (w+5) 0 := by
      apply Prod.ext <;> apply Fin.ext <;> dsimp [andCell, andPoint, point]; omega
    rw [← he]
    exact Finset.mem_image.mpr ⟨.branchC 0, Finset.mem_univ _, rfl⟩
  refine push_via_parallel_row (andBoxes_disjoint_walls w hw a b false)
    (point w (w+6) 1).1 (point w (w+6) 0).1
    (point w (w+5) 0).1 (point w (w+4) 0).1
    (point w (w+6) 1).2 (point w (w+6) 0).2 .south .west
    ?_ ?_ ?_ ?_ ?_ hsource ?_ ?_ ?_
  · dsimp [Adjacent, point]; unfold origin; omega
  · dsimp [Adjacent, Direction.opposite, point]; unfold origin; omega
  · dsimp [Adjacent, point]; omega
  · dsimp [Adjacent, point]; omega
  · apply and_output_gap_free w hw a b false goals
    all_goals simp only [point, Bool.toNat_false]; omega
  · apply and_output_gap_free w hw a b false goals
    all_goals simp only [point, Bool.toNat_false]; omega
  · intro z hlo hhi
    apply and_above_free w hw a b false goals
    all_goals dsimp only [point] at *; unfold origin at *; omega
  · intro z hlo hhi
    apply and_above_free w hw a b false goals
    all_goals dsimp only [point] at *; unfold origin at *; omega

/-- Contract the output box by one cell and return to the exposed upper lane. -/
theorem or_C_left (w : ℕ) (hw : 2 ≤ w) (a b : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (orBoard w goals) (some 1)
      ⟨point w (w+7) 1, orBoxes w a b false⟩
      ⟨point w (w+7) 1,
        insert (point w (w+5) 0)
          ((orBoxes w a b false).erase (point w (w+6) 0))⟩ := by
  have hsource : point w (w+6) 0 ∈ orBoxes w a b false := by
    have he : orCell w a b false (.branchC 0) = point w (w+6) 0 := by
      apply Prod.ext <;> apply Fin.ext <;> dsimp [orCell, orPoint, point]; omega
    rw [← he]
    exact Finset.mem_image.mpr ⟨.branchC 0, Finset.mem_univ _, rfl⟩
  refine push_via_parallel_row (orBoxes_disjoint_walls w hw a b false)
    (point w (w+7) 1).1 (point w (w+7) 0).1
    (point w (w+6) 0).1 (point w (w+5) 0).1
    (point w (w+7) 1).2 (point w (w+7) 0).2 .south .west
    ?_ ?_ ?_ ?_ ?_ hsource ?_ ?_ ?_
  · dsimp [Adjacent, point]; unfold origin; omega
  · dsimp [Adjacent, Direction.opposite, point]; unfold origin; omega
  · dsimp [Adjacent, point]; omega
  · dsimp [Adjacent, point]; omega
  · apply or_output_gap_free w hw a b false goals
    all_goals simp only [point, Bool.toNat_false]; omega
  · apply or_output_gap_free w hw a b false goals
    all_goals simp only [point, Bool.toNat_false]; omega
  · intro z hlo hhi
    apply or_above_free w hw a b false goals
    all_goals dsimp only [point] at *; unfold origin at *; omega
  · intro z hlo hhi
    apply or_above_free w hw a b false goals
    all_goals dsimp only [point] at *; unfold origin at *; omega

end PushPuzzle.PushS.FiniteGateMacros
