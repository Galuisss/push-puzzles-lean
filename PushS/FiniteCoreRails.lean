/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateTracks
import Mathlib.Tactic.FinCases

/-! Explicit complete floor lines connect all normal boxes on each thick gate rail. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteCoreRails

open PushFS FiniteGeometry FiniteGateCore

attribute [local irreducible] side

/-- The four straight working rails of the complete AND core. -/
inductive AndRail | west | input | main | branchB
  deriving DecidableEq

def andRail {w : ℕ} : AndLabel w → AndRail
  | .west _ => .west
  | .upper _ | .middle | .lower _ => .input
  | .guard _ | .triggerA | .branchC _ => .main
  | .branchB _ => .branchB

def AndRail.count (w : ℕ) : AndRail → ℕ
  | .west => 2*w+10
  | .input => 6*w+22
  | .main => 9*w+24
  | .branchB => 8*w+34

def AndRail.vertical : AndRail → Bool
  | .input | .branchB => true
  | _ => false

def AndRail.point (w : ℕ) (r : AndRail) (i : Fin (r.count w)) : ℕ × ℕ :=
  match r with
  | .west => (origin w-8*w-18+i.val, origin w-6*w-21)
  | .input => (origin w-6*w-9, origin w-6*w-21+i.val)
  | .main => (origin w-6*w-9+i.val, origin w)
  | .branchB => (origin w+3, origin w-8*w-33+i.val)

theorem andRail_bounds (w : ℕ) (r : AndRail) (i : Fin (r.count w)) :
    (r.point w i).1 < side w ∧ (r.point w i).2 < side w := by
  have hi := i.isLt
  cases r <;> dsimp [AndRail.point, AndRail.count, origin] at *
  all_goals unfold side; omega

def AndRail.cell (w : ℕ) (r : AndRail) (i : Fin (r.count w)) : Cell (side w) (side w) :=
  (⟨(r.point w i).1, (andRail_bounds w r i).1⟩,
   ⟨(r.point w i).2, (andRail_bounds w r i).2⟩)

private def andIndex {w : ℕ} (a b c : Bool) : AndLabel w → ℕ
  | .west j => 2*w+8-2*j.val-a.toNat
  | .upper j => 2+2*j.val-a.toNat
  | .middle => 3*w+12-3*a.toNat
  | .lower j => 4*w+12+2*j.val-a.toNat
  | .guard j => 2+2*j.val-a.toNat
  | .triggerA => 6*w+12-a.toNat
  | .branchB j => 8*w+32-2*j.val-b.toNat
  | .branchC j => 7*w+14+2*j.val-c.toNat

/-- Every actual normal AND slot is strictly inside its complete floor line. -/
private theorem andCell_on_rail (w : ℕ) (a b c : Bool) (l : AndLabel w) :
    ∃ i : Fin ((andRail l).count w), 0 < i.val ∧ i.val+1 < (andRail l).count w ∧
      (andRail l).cell w i = andCell w a b c l := by
  have ha := Bool.toNat_le a
  have hb := Bool.toNat_le b
  have hc := Bool.toNat_le c
  have hi : 0 < andIndex a b c l ∧ andIndex a b c l+1 < (andRail l).count w := by
    cases l <;> dsimp [andIndex, andRail, AndRail.count] <;> omega
  refine ⟨⟨andIndex a b c l, by omega⟩, hi.1, hi.2, ?_⟩
  apply Prod.ext <;> apply Fin.ext
  all_goals cases l <;>
    dsimp [AndRail.cell, AndRail.point, andRail, andIndex, andCell, andPoint, origin] <;> omega

theorem andRail_floor (w : ℕ) (hw : 2 ≤ w) (r : AndRail) (i : Fin (r.count w)) :
    r.cell w i ∉ andWalls w := by
  intro hp
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hp
  have hh := ((andRectangle w j).mem_cells _ _ _).mp hj
  have hi := i.isLt
  fin_cases j <;> cases r <;>
    simp [andRectangle, AndRail.cell, AndRail.point, AndRail.count, origin] at hi hh <;> omega

private theorem andRail_adjacent (w : ℕ) (r : AndRail) (i : Fin (r.count w-1)) :
    Adjacent (if r.vertical then .south else .east)
      (r.cell w ⟨i.val, by cases r <;> dsimp [AndRail.count] at * <;> omega⟩)
      (r.cell w ⟨i.val+1, by cases r <;> dsimp [AndRail.count] at * <;> omega⟩) := by
  cases r <;> simp [AndRail.cell, AndRail.point, AndRail.vertical, Adjacent, Nat.add_assoc]

/-- The complete AND line remains a single SCC under any placement with those cells free. -/
private theorem andRail_connected {W H : ℕ} (w : ℕ) (r : AndRail)
    (e : GridEmbedding (side w) (side w) W H) (B : Board W H)
    (hf : ∀ i, e.cells (r.cell w i) ∉ B.walls)
    (a b : Fin (r.count w)) (ha : 0 < a.val ∧ a.val+1 < r.count w)
    (hb : 0 < b.val ∧ b.val+1 < r.count w) :
    SameComponent B (e.cells (r.cell w a)) (e.cells (r.cell w b)) := by
  exact sameComponent_segment (by cases r <;> simp [AndRail.count])
    (fun i => e.cells (r.cell w i)) hf
    (fun i => e.adjacent _ _ _ (andRail_adjacent w r i)) a b ha hb

/-- Two normal AND boxes on one rail retain explicit bidirectional placed paths. -/
theorem andCells_connected {W H : ℕ} (w : ℕ) (a b c : Bool) (l m : AndLabel w)
    (hr : andRail l = andRail m) (e : GridEmbedding (side w) (side w) W H) (B : Board W H)
    (hf : ∀ i, e.cells ((andRail l).cell w i) ∉ B.walls) :
    SameComponent B (e.cells (andCell w a b c l)) (e.cells (andCell w a b c m)) := by
  obtain ⟨i, hi, hi', he⟩ := andCell_on_rail w a b c l
  have hm : ∃ j : Fin ((andRail l).count w), 0 < j.val ∧ j.val+1 < (andRail l).count w ∧
      (andRail l).cell w j = andCell w a b c m := by
    exact (congrArg (fun r : AndRail => ∃ j : Fin (r.count w),
      0 < j.val ∧ j.val+1 < r.count w ∧ r.cell w j = andCell w a b c m) hr).mpr
      (andCell_on_rail w a b c m)
  obtain ⟨j, hj, hj', he'⟩ := hm
  rw [← he, ← he']
  exact andRail_connected w _ e B hf i j ⟨hi, hi'⟩ ⟨hj, hj'⟩

/-- The complete OR core has one main row and one vertical input rail. -/
inductive OrRail | main | branchB
  deriving DecidableEq

def orRail {w : ℕ} : OrLabel w → OrRail
  | .branchB _ => .branchB
  | _ => .main

def OrRail.count (w : ℕ) : OrRail → ℕ
  | .main => 5*w+25
  | .branchB => 2*w+16

private def OrRail.vertical : OrRail → Bool
  | .main => false
  | .branchB => true

def OrRail.point (w : ℕ) (r : OrRail) (i : Fin (r.count w)) : ℕ × ℕ :=
  match r with
  | .main => (origin w-2*w-9+i.val, origin w)
  | .branchB => (origin w+4, origin w-2*w-15+i.val)

theorem orRail_bounds (w : ℕ) (r : OrRail) (i : Fin (r.count w)) :
    (r.point w i).1 < side w ∧ (r.point w i).2 < side w := by
  have hi := i.isLt
  cases r <;> dsimp [OrRail.point, OrRail.count, origin] at *
  all_goals unfold side; omega

def OrRail.cell (w : ℕ) (r : OrRail) (i : Fin (r.count w)) : Cell (side w) (side w) :=
  (⟨(r.point w i).1, (orRail_bounds w r i).1⟩,
   ⟨(r.point w i).2, (orRail_bounds w r i).2⟩)

private def orIndex {w : ℕ} (a b c : Bool) : OrLabel w → ℕ
  | .left j => 2*w+10-2*j.val-a.toNat
  | .triggerA => 2*w+12-a.toNat
  | .branchB j => 2*w+14-2*j.val-b.toNat
  | .branchC j => 3*w+15+2*j.val-c.toNat

private theorem orCell_on_rail (w : ℕ) (a b c : Bool) (l : OrLabel w) :
    ∃ i : Fin ((orRail l).count w), 0 < i.val ∧ i.val+1 < (orRail l).count w ∧
      (orRail l).cell w i = orCell w a b c l := by
  have ha := Bool.toNat_le a
  have hb := Bool.toNat_le b
  have hc := Bool.toNat_le c
  have hi : 0 < orIndex a b c l ∧ orIndex a b c l+1 < (orRail l).count w := by
    cases l <;> dsimp [orIndex, orRail, OrRail.count] <;> omega
  refine ⟨⟨orIndex a b c l, by omega⟩, hi.1, hi.2, ?_⟩
  apply Prod.ext <;> apply Fin.ext
  all_goals cases l <;> dsimp [OrRail.cell, OrRail.point, orRail, orIndex, orCell, orPoint, origin] <;> omega

theorem orRail_floor (w : ℕ) (hw : 2 ≤ w) (r : OrRail) (i : Fin (r.count w)) :
    r.cell w i ∉ orWalls w := by
  intro hp
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hp
  have hh := ((orRectangle w j).mem_cells _ _ _).mp hj
  have hi := i.isLt
  fin_cases j <;> cases r <;>
    simp [orRectangle, OrRail.cell, OrRail.point, OrRail.count, origin] at hi hh <;> omega

private theorem orRail_adjacent (w : ℕ) (r : OrRail) (i : Fin (r.count w-1)) :
    Adjacent (if r.vertical then .south else .east)
      (r.cell w ⟨i.val, by cases r <;> dsimp [OrRail.count] at * <;> omega⟩)
      (r.cell w ⟨i.val+1, by cases r <;> dsimp [OrRail.count] at * <;> omega⟩) := by
  cases r <;> simp [OrRail.cell, OrRail.point, OrRail.vertical, Adjacent, Nat.add_assoc]

theorem orRail_connected {W H : ℕ} (w : ℕ) (r : OrRail)
    (e : GridEmbedding (side w) (side w) W H) (B : Board W H)
    (hf : ∀ i, e.cells (r.cell w i) ∉ B.walls)
    (a b : Fin (r.count w)) (ha : 0 < a.val ∧ a.val+1 < r.count w)
    (hb : 0 < b.val ∧ b.val+1 < r.count w) :
    SameComponent B (e.cells (r.cell w a)) (e.cells (r.cell w b)) := by
  exact sameComponent_segment (by cases r <;> simp [OrRail.count])
    (fun i => e.cells (r.cell w i)) hf
    (fun i => e.adjacent _ _ _ (orRail_adjacent w r i)) a b ha hb

theorem orCells_connected {W H : ℕ} (w : ℕ) (a b c : Bool) (l m : OrLabel w)
    (hr : orRail l = orRail m) (e : GridEmbedding (side w) (side w) W H) (B : Board W H)
    (hf : ∀ i, e.cells ((orRail l).cell w i) ∉ B.walls) :
    SameComponent B (e.cells (orCell w a b c l)) (e.cells (orCell w a b c m)) := by
  obtain ⟨i, hi, hi', he⟩ := orCell_on_rail w a b c l
  have hm : ∃ j : Fin ((orRail l).count w), 0 < j.val ∧ j.val+1 < (orRail l).count w ∧
      (orRail l).cell w j = orCell w a b c m := by
    exact (congrArg (fun r : OrRail => ∃ j : Fin (r.count w),
      0 < j.val ∧ j.val+1 < r.count w ∧ r.cell w j = orCell w a b c m) hr).mpr
      (orCell_on_rail w a b c m)
  obtain ⟨j, hj, hj', he'⟩ := hm
  rw [← he, ← he']
  exact orRail_connected w _ e B hf i j ⟨hi, hi'⟩ ⟨hj, hj'⟩

end PushPuzzle.PushS.FiniteCoreRails
