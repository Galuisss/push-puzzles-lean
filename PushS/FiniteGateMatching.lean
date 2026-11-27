/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateCore
public import PushFS.StaticLine
public import PushFS.StaticTracks
import Mathlib.Tactic.FinCases

/-! Static paths for every physical box in the parameterized gate inventories. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGateMatching

open PushFS PushFS.Gadgets FiniteGeometry FiniteGateCore

attribute [local irreducible] side

/-- The actual working axis of each AND box family. -/
def andVertical {w : ℕ} : AndLabel w → Bool
  | .upper _ | .middle | .lower _ | .branchB _ => true
  | _ => false

/-- The full normal travel distance of each AND box, including the three-step middle box. -/
def andTravel {w : ℕ} : AndLabel w → ℕ
  | .middle => 3
  | _ => 1

/-- The normal phase controlling each actual AND box. -/
def andFlag {w : ℕ} (a b c : Bool) : AndLabel w → Bool
  | .branchB _ => b
  | .branchC _ => c
  | _ => a

/-- Literal support-to-support rail coordinates for one actual AND box. -/
def andLinePoint (w : ℕ) (l : AndLabel w) (i : Fin (andTravel l+3)) : ℕ × ℕ :=
  let p := andPoint w false false false l
  if andVertical l then (p.1, p.2-andTravel l-1+i.val)
  else (p.1-andTravel l-1+i.val, p.2)

/-- Every AND normal-slot rail and both supports fit the finite core board. -/
theorem andLinePoint_bounds (w : ℕ) (l : AndLabel w) (i : Fin (andTravel l+3)) :
    (andLinePoint w l i).1 < side w ∧ (andLinePoint w l i).2 < side w := by
  have hi := i.isLt
  cases l <;> dsimp [andLinePoint, andVertical, andTravel, andPoint, origin] at *
  all_goals unfold side; omega

/-- The complete bounded normal-slot rail and both supports of an actual AND box. -/
def andLine (w : ℕ) (l : AndLabel w) (i : Fin (andTravel l+3)) :
    Cell (side w) (side w) :=
  (⟨(andLinePoint w l i).1, (andLinePoint_bounds w l i).1⟩,
   ⟨(andLinePoint w l i).2, (andLinePoint_bounds w l i).2⟩)

-- The eight box families meet seven rectangles; each branch is linear coordinate arithmetic.
set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
/-- Every cell of an actual AND normal-slot rail and both supports is literal floor. -/
theorem andLine_floor (w : ℕ) (hw : 2 ≤ w) (l : AndLabel w)
    (i : Fin (andTravel l+3)) : andLine w l i ∉ andWalls w := by
  intro hp
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hp
  have hj' := ((andRectangle w j).mem_cells _ _ _).mp hj
  have hi := i.isLt
  fin_cases j <;> cases l <;>
    simp [andRectangle, andLine, andLinePoint, andPoint, andVertical, andTravel, origin] at hj' hi <;>
    omega

/-- Successive actual AND rail cells are physically adjacent. -/
theorem andLine_adjacent (w : ℕ) (l : AndLabel w) (i : Fin (andTravel l+2)) :
    Adjacent (if andVertical l then .south else .east)
      (andLine w l i.castSucc) (andLine w l i.succ) := by
  have hi := i.isLt
  cases l <;> simp [andLine, andLinePoint, andVertical, andTravel, andPoint, Adjacent, origin,
      Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ] at * <;>
    omega

/-- The normal AND box slot inside its complete physical support rail. -/
def andSlotIndex {w : ℕ} (l : AndLabel w) (a b c : Bool) : Fin (andTravel l+3) :=
  ⟨if andFlag a b c l then 1 else andTravel l+1, by split <;> omega⟩

/-- Each actual normal AND position is its designated physical rail cell. -/
theorem andLine_slot (w : ℕ) (l : AndLabel w) (a b c : Bool) :
    andLine w l (andSlotIndex l a b c) = andCell w a b c l := by
  apply Prod.ext <;> apply Fin.ext
  all_goals cases l <;> cases a <;> cases b <;> cases c <;>
    simp [andLine, andLinePoint, andSlotIndex, andFlag, andVertical, andTravel,
      andCell, andPoint, origin] <;> omega

/-- Each named AND box has its two normal slots in one actual wall-only SCC. -/
theorem andCell_connected (w : ℕ) (hw : 2 ≤ w) (a b c a' b' c' : Bool)
    (goals : Finset (Cell (side w) (side w))) (l : AndLabel w) :
    SameComponent (andBoard w goals) (andCell w a b c l) (andCell w a' b' c' l) := by
  have hh := sameComponent_line (B := andBoard w goals) (andLine w l)
    (andLine_floor w hw l) (andLine_adjacent w l)
    (andSlotIndex l a b c) (andSlotIndex l a' b' c')
    (by dsimp [andSlotIndex]; split <;> cases l <;> simp [andTravel])
    (by dsimp [andSlotIndex]; split <;> cases l <;> simp [andTravel])
  simpa only [andLine_slot] using hh

/-- The actual working axis of each OR box family. -/
def orVertical {w : ℕ} : OrLabel w → Bool
  | .branchB _ => true
  | _ => false

/-- The normal phase controlling each actual OR box. -/
def orFlag {w : ℕ} (a b c : Bool) : OrLabel w → Bool
  | .branchB _ => b
  | .branchC _ => c
  | _ => a

/-- Literal support-to-support rail coordinates for one actual OR box. -/
def orLinePoint (w : ℕ) (l : OrLabel w) (i : Fin 4) : ℕ × ℕ :=
  let p := orPoint w false false false l
  if orVertical l then (p.1, p.2-2+i.val) else (p.1-2+i.val, p.2)

/-- Every OR normal-slot rail and both supports fit the finite core board. -/
theorem orLinePoint_bounds (w : ℕ) (l : OrLabel w) (i : Fin 4) :
    (orLinePoint w l i).1 < side w ∧ (orLinePoint w l i).2 < side w := by
  have hi := i.isLt
  cases l <;> dsimp [orLinePoint, orVertical, orPoint, origin] at *
  all_goals unfold side; omega

/-- The complete bounded normal-slot rail and both supports of an actual OR box. -/
def orLine (w : ℕ) (l : OrLabel w) (i : Fin 4) : Cell (side w) (side w) :=
  (⟨(orLinePoint w l i).1, (orLinePoint_bounds w l i).1⟩,
   ⟨(orLinePoint w l i).2, (orLinePoint_bounds w l i).2⟩)

/-- Every cell of an actual OR normal-slot rail and both supports is literal floor. -/
theorem orLine_floor (w : ℕ) (hw : 2 ≤ w) (l : OrLabel w) (i : Fin 4) :
    orLine w l i ∉ orWalls w := by
  intro hp
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hp
  have hj' := ((orRectangle w j).mem_cells _ _ _).mp hj
  have hi := i.isLt
  fin_cases j <;> cases l <;>
    simp [orRectangle, orLine, orLinePoint, orPoint, orVertical, origin] at hj' <;> omega

/-- Successive actual OR rail cells are physically adjacent. -/
theorem orLine_adjacent (w : ℕ) (l : OrLabel w) (i : Fin 3) :
    Adjacent (if orVertical l then .south else .east) (orLine w l i.castSucc) (orLine w l i.succ) := by
  have hi := i.isLt
  cases l <;> simp [orLine, orLinePoint, orVertical, orPoint, Adjacent, origin,
    Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ] at * <;> omega

/-- The normal OR box slot inside its complete physical support rail. -/
def orSlotIndex {w : ℕ} (l : OrLabel w) (a b c : Bool) : Fin 4 :=
  if orFlag a b c l then 1 else 2

/-- Each actual normal OR position is its designated physical rail cell. -/
theorem orLine_slot (w : ℕ) (l : OrLabel w) (a b c : Bool) :
    orLine w l (orSlotIndex l a b c) = orCell w a b c l := by
  apply Prod.ext <;> apply Fin.ext
  all_goals cases l <;> cases a <;> cases b <;> cases c <;>
    simp [orLine, orLinePoint, orSlotIndex, orFlag, orVertical, orCell, orPoint, origin] <;> omega

theorem orCell_connected (w : ℕ) (hw : 2 ≤ w) (a b c a' b' c' : Bool)
    (goals : Finset (Cell (side w) (side w))) (l : OrLabel w) :
    SameComponent (orBoard w goals) (orCell w a b c l) (orCell w a' b' c' l) := by
  have hh := sameComponent_line (B := orBoard w goals) (orLine w l)
    (orLine_floor w hw l) (orLine_adjacent w l) (orSlotIndex l a b c) (orSlotIndex l a' b' c')
    (by dsimp [orSlotIndex]; split <;> decide) (by dsimp [orSlotIndex]; split <;> decide)
  simpa only [orLine_slot] using hh

/-- A complete physical source-to-target matching for every AND normal pair. -/
def andMatching (w : ℕ) (hw : 2 ≤ w) (initial target : Gates.Signals) :
    SlotMatching (andInstance w hw initial target) (AndLabel w) where
  source := ⟨andCell w initial.left initial.upper initial.right,
    andCell_injective w hw _ _ _⟩
  target := ⟨andCell w target.left target.upper target.right,
    andCell_injective w hw _ _ _⟩
  source_image := Finset.map_eq_image _ _
  target_image := Finset.map_eq_image _ _
  connected := andCell_connected w hw _ _ _ _ _ _ _

def orMatching (w : ℕ) (hw : 2 ≤ w) (initial target : Gates.Signals) :
    SlotMatching (orInstance w hw initial target) (OrLabel w) where
  source := ⟨orCell w initial.left initial.upper initial.right,
    orCell_injective w hw _ _ _⟩
  target := ⟨orCell w target.left target.upper target.right,
    orCell_injective w hw _ _ _⟩
  source_image := Finset.map_eq_image _ _
  target_image := Finset.map_eq_image _ _
  connected := orCell_connected w hw _ _ _ _ _ _ _

end PushPuzzle.PushS.FiniteGateMatching
