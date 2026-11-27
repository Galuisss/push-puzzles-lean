/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGatePlacedContract
public import PushS.FiniteRoutingOuterPorts
import Mathlib.Tactic.FinCases

/-! The two literal narrow gate corridors meeting the first B-line's exposed start faces. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGateFaceGeometry

open PushFS FiniteGeometry FiniteGateCore FiniteGateState FiniteGateTools
open FiniteGateMacros

variable {W H : ℕ}

attribute [local irreducible] FiniteGeometry.side

def column (kind : Bool) : ℕ := if kind then 3 else 4

def upperDepth (w : ℕ) (kind : Bool) : ℕ := if kind then 8*w+32 else 2*w+14

def leftX (w : ℕ) (kind : Bool) : ℕ := origin w+column kind-(w+1)

def rightX (w : ℕ) (kind : Bool) : ℕ := origin w+column kind+(w+1)

/-- The start-face hub of the actual outward B-line, expressed in core coordinates. -/
def dock (w : ℕ) (kind north : Bool) : Cell (side w) (side w) :=
  (⟨if north then leftX w kind else rightX w kind, by
    unfold leftX rightX column origin FiniteGeometry.side
    split <;> split <;> omega⟩,
   ⟨origin w-upperDepth w kind, by unfold upperDepth origin FiniteGeometry.side; split <;> omega⟩)

/-- Exposed space left of the B rail, extending exactly to its first line's outer hub. -/
def leftStrip (w : ℕ) (kind : Bool) : Finset (Cell (side w) (side w)) :=
  Finset.univ.filter fun p => leftX w kind ≤ p.1.val ∧ p.1.val < origin w+column kind ∧
    origin w-upperDepth w kind ≤ p.2.val ∧ p.2.val < origin w

/-- The two-column right C-mouth corridor meeting the opposite B-line face. -/
def rightStrip (w : ℕ) (kind : Bool) : Finset (Cell (side w) (side w)) :=
  Finset.univ.filter fun p => rightX w kind ≤ p.1.val ∧ p.1.val ≤ rightX w kind+2 ∧
    origin w-upperDepth w kind ≤ p.2.val ∧ p.2.val < origin w

@[simp] theorem mem_leftStrip (w : ℕ) (kind : Bool) (p : Cell (side w) (side w)) :
    p ∈ leftStrip w kind ↔ leftX w kind ≤ p.1.val ∧ p.1.val < origin w+column kind ∧
      origin w-upperDepth w kind ≤ p.2.val ∧ p.2.val < origin w := by
  simp only [leftStrip,Finset.mem_filter,Finset.mem_univ,true_and]

@[simp] theorem mem_rightStrip (w : ℕ) (kind : Bool) (p : Cell (side w) (side w)) :
    p ∈ rightStrip w kind ↔ rightX w kind ≤ p.1.val ∧ p.1.val ≤ rightX w kind+2 ∧
      origin w-upperDepth w kind ≤ p.2.val ∧ p.2.val < origin w := by
  simp only [rightStrip,Finset.mem_filter,Finset.mem_univ,true_and]

set_option maxHeartbeats 800000 in
/-- Every independent AND mixed phase leaves the complete left approach corridor free. -/
theorem and_left_free (w : ℕ) (hw : 2 ≤ w) (X : AndPhases w)
    (goals : Finset (Cell (side w) (side w))) (p : Cell (side w) (side w))
    (hp : p ∈ leftStrip w true) : Free (andBoard w goals) (andMixedBoxes w X) p := by
  obtain ⟨hx,hx',hy,hy'⟩ := (mem_leftStrip w true p).mp hp
  dsimp [leftX,column,upperDepth] at hx hx' hy hy'
  constructor
  · intro hm
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hm
    have hi' := ((andRectangle w i).mem_cells _ _ _).mp hi
    fin_cases i <;> simp [andRectangle,origin] at hi' hx hx' hy hy' <;> omega
  · intro hm
    obtain ⟨l,_,he⟩ := Finset.mem_image.mp hm
    have hpx := congrArg (fun p => p.1.val) he
    have hpy := congrArg (fun p => p.2.val) he
    cases l with
    | west i =>
      have hb := Bool.toNat_le (X.west i)
      simp only [andMixedCell,andCell,andPoint] at hpx hpy
      unfold origin at *
      omega
    | branchC i =>
      have hb := Bool.toNat_le (X.branchC i)
      simp only [andMixedCell,andCell,andPoint] at hpx hpy
      unfold origin at *
      omega
    | _ =>
      simp only [andMixedCell,andCell,andPoint] at hpx hpy
      unfold origin at *
      omega

set_option maxHeartbeats 800000 in
/-- Every independent AND mixed phase leaves the complete right mouth corridor free. -/
theorem and_right_free (w : ℕ) (hw : 2 ≤ w) (X : AndPhases w)
    (goals : Finset (Cell (side w) (side w))) (p : Cell (side w) (side w))
    (hp : p ∈ rightStrip w true) : Free (andBoard w goals) (andMixedBoxes w X) p := by
  obtain ⟨hx,hx',hy,hy'⟩ := (mem_rightStrip w true p).mp hp
  dsimp [rightX,column,upperDepth] at hx hx' hy hy'
  constructor
  · intro hm
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hm
    have hi' := ((andRectangle w i).mem_cells _ _ _).mp hi
    fin_cases i <;> simp [andRectangle,origin] at hi' hx hx' hy hy' <;> omega
  · intro hm
    obtain ⟨l,_,he⟩ := Finset.mem_image.mp hm
    have hpx := congrArg (fun p => p.1.val) he
    have hpy := congrArg (fun p => p.2.val) he
    cases l with
    | west i =>
      have hb := Bool.toNat_le (X.west i)
      simp only [andMixedCell,andCell,andPoint] at hpx hpy
      unfold origin at *
      omega
    | _ =>
      simp only [andMixedCell,andCell,andPoint] at hpx hpy
      unfold origin at *
      omega

set_option maxHeartbeats 800000 in
/-- Every independent OR mixed phase leaves the complete left approach corridor free. -/
theorem or_left_free (w : ℕ) (_hw : 2 ≤ w) (X : OrPhases w)
    (goals : Finset (Cell (side w) (side w))) (p : Cell (side w) (side w))
    (hp : p ∈ leftStrip w false) : Free (orBoard w goals) (orMixedBoxes w X) p := by
  obtain ⟨hx,hx',hy,hy'⟩ := (mem_leftStrip w false p).mp hp
  dsimp [leftX,column,upperDepth] at hx hx' hy hy'
  constructor
  · intro hm
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hm
    have hi' := ((orRectangle w i).mem_cells _ _ _).mp hi
    fin_cases i <;> simp [orRectangle,origin] at hi' hx hx' hy hy' <;> omega
  · intro hm
    obtain ⟨l,_,he⟩ := Finset.mem_image.mp hm
    have hpx := congrArg (fun p => p.1.val) he
    have hpy := congrArg (fun p => p.2.val) he
    cases l with
    | branchC i =>
      have hb := Bool.toNat_le (X.branchC i)
      simp only [orMixedCell,orCell,orPoint] at hpx hpy
      unfold origin at *
      omega
    | _ =>
      simp only [orMixedCell,orCell,orPoint] at hpx hpy
      unfold origin at *
      omega

set_option maxHeartbeats 800000 in
/-- Every independent OR mixed phase leaves the complete right mouth corridor free. -/
theorem or_right_free (w : ℕ) (hw : 2 ≤ w) (X : OrPhases w)
    (goals : Finset (Cell (side w) (side w))) (p : Cell (side w) (side w))
    (hp : p ∈ rightStrip w false) : Free (orBoard w goals) (orMixedBoxes w X) p := by
  obtain ⟨hx,hx',hy,hy'⟩ := (mem_rightStrip w false p).mp hp
  dsimp [rightX,column,upperDepth] at hx hx' hy hy'
  constructor
  · intro hm
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hm
    have hi' := ((orRectangle w i).mem_cells _ _ _).mp hi
    fin_cases i <;> simp [orRectangle,origin] at hi' hx hx' hy hy' <;> omega
  · intro hm
    obtain ⟨l,_,he⟩ := Finset.mem_image.mp hm
    have hpx := congrArg (fun p => p.1.val) he
    have hpy := congrArg (fun p => p.2.val) he
    cases l <;> simp only [orMixedCell,orCell,orPoint] at hpx hpy <;>
      unfold origin at * <;> omega

theorem dock_left_mem (w : ℕ) (kind : Bool) : dock w kind true ∈ leftStrip w kind := by
  simp only [mem_leftStrip]
  cases kind <;> dsimp [dock,leftX,column,upperDepth]
  all_goals unfold origin; omega

theorem dock_right_mem (w : ℕ) (kind : Bool) : dock w kind false ∈ rightStrip w kind := by
  simp only [mem_rightStrip]
  cases kind <;> dsimp [dock,rightX,column,upperDepth]
  all_goals unfold origin; omega

/-- All left A/B supports lie in the same literal exposed corridor. -/
theorem point_left_mem (w : ℕ) (hw : 2 ≤ w) (kind : Bool) (x up : ℕ)
    (hx : 1 ≤ x ∧ x < column kind) (hu : 1 ≤ up ∧ up ≤ 2) :
    point w x up (by cases kind <;> dsimp [column] at hx <;> omega) (by omega) ∈ leftStrip w kind := by
  simp only [mem_leftStrip]
  cases kind <;> dsimp [point,leftX,column,upperDepth] at *
  all_goals dsimp [column] at hx; unfold origin; omega

/-- Both right C interfaces lie in the same literal exposed corridor. -/
theorem point_right_mem (w : ℕ) (hw : 2 ≤ w) (kind : Bool) (x : ℕ)
    (hx : w+column kind+1 ≤ x ∧ x ≤ w+column kind+3) :
    point w x 1 (by cases kind <;> dsimp [column] at hx <;> omega) ∈ rightStrip w kind := by
  simp only [mem_rightStrip]
  cases kind <;> dsimp [point,rightX,column,upperDepth] at *
  all_goals dsimp [column] at hx; unfold origin; omega

/-- Any two actual cells of the left exposed corridor are connected without moving a box. -/
theorem left_walk_ambient (w : ℕ) (kind : Bool)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H} {stock : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (leftStrip w kind) e B stock)
    (p q : Cell (side w) (side w)) (hp : p ∈ leftStrip w kind) (hq : q ∈ leftStrip w kind) :
    Reachable B (some 1) ⟨e.cells p,stock⟩ ⟨e.cells q,stock⟩ := by
  apply FiniteAtomFrames.walk_ambient p q e
  apply F.mono_active
  intro r hr
  have hp' := (mem_leftStrip _ _ _).mp hp
  have hq' := (mem_leftStrip _ _ _).mp hq
  have hr' := (FiniteAtomFrames.mem_walkActive _ _ _).mp hr
  apply (mem_leftStrip _ _ _).mpr
  omega

/-- Any two actual cells of the right mouth corridor are connected without moving a box. -/
theorem right_walk_ambient (w : ℕ) (kind : Bool)
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H} {stock : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (rightStrip w kind) e B stock)
    (p q : Cell (side w) (side w)) (hp : p ∈ rightStrip w kind) (hq : q ∈ rightStrip w kind) :
    Reachable B (some 1) ⟨e.cells p,stock⟩ ⟨e.cells q,stock⟩ := by
  apply FiniteAtomFrames.walk_ambient p q e
  apply F.mono_active
  intro r hr
  have hp' := (mem_rightStrip _ _ _).mp hp
  have hq' := (mem_rightStrip _ _ _).mp hq
  have hr' := (FiniteAtomFrames.mem_walkActive _ _ _).mp hr
  apply (mem_rightStrip _ _ _).mpr
  omega

end PushPuzzle.PushS.FiniteGateFaceGeometry
