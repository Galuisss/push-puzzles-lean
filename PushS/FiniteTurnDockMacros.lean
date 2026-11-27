/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteTurnMacros

/-! Complete normal turn updates start and finish at one actual dock in the free concave quadrant. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteTools

open PushFS

def turnDock (w : ℕ) : Cell (side w) (side w) :=
  (⟨radius w-3,by unfold side radius; omega⟩,⟨radius w+3,by unfold side radius; omega⟩)

inductive TurnBridge
  | fAcross | fUp | fCorner | fExitDown | fExitAcross
  | bAcross | bUp | bToward | bCorner | bExitAcross | bExitDown

def TurnBridge.phase : TurnBridge → Bool
  | .fAcross | .fUp | .fCorner | .bExitAcross | .bExitDown => false
  | _ => true

def TurnBridge.points (w : ℕ) : TurnBridge → (ℕ × ℕ) × (ℕ × ℕ)
  | .fAcross | .bAcross => ((radius w-3,radius w+3),(radius w-1,radius w+3))
  | .fUp => ((radius w-1,radius w+3),(radius w-1,radius w))
  | .fCorner => ((radius w-1,radius w),(radius w,radius w))
  | .fExitDown => ((radius w-2,radius w),(radius w-2,radius w+3))
  | .fExitAcross => ((radius w-2,radius w+3),(radius w-3,radius w+3))
  | .bUp => ((radius w-1,radius w+3),(radius w-1,radius w+1))
  | .bToward => ((radius w-1,radius w+1),(radius w,radius w+1))
  | .bCorner => ((radius w,radius w+1),(radius w,radius w))
  | .bExitAcross => ((radius w,radius w+2),(radius w-3,radius w+2))
  | .bExitDown => ((radius w-3,radius w+2),(radius w-3,radius w+3))

def TurnBridge.start (w : ℕ) (s : TurnBridge) : Cell (side w) (side w) :=
  (⟨(s.points w).1.1,by cases s <;> dsimp [TurnBridge.points,radius,side] <;> omega⟩,
   ⟨(s.points w).1.2,by cases s <;> dsimp [TurnBridge.points,radius,side] <;> omega⟩)

def TurnBridge.finish (w : ℕ) (s : TurnBridge) : Cell (side w) (side w) :=
  (⟨(s.points w).2.1,by cases s <;> dsimp [TurnBridge.points,radius,side] <;> omega⟩,
   ⟨(s.points w).2.2,by cases s <;> dsimp [TurnBridge.points,radius,side] <;> omega⟩)

set_option maxHeartbeats 1000000 in
private theorem turn_bridge_free (w : ℕ) (s : TurnBridge) (p : Cell (side w) (side w))
    (hx : min (s.start w).1.val (s.finish w).1.val ≤ p.1.val)
    (hx' : p.1.val ≤ max (s.start w).1.val (s.finish w).1.val)
    (hy : min (s.start w).2.val (s.finish w).2.val ≤ p.2.val)
    (hy' : p.2.val ≤ max (s.start w).2.val (s.finish w).2.val) :
    Free (turnMacroBoard w) (turnBoxes w s.phase) p := by
  constructor
  · apply (FiniteWireFrame.floor_iff _ _ _).mpr
    rw [turnActive,FiniteGeometry.Rectangle.mem_cells]
    cases s <;> simp [TurnBridge.start,TurnBridge.finish,TurnBridge.points,radius] at hx hx' hy hy' ⊢ <;> omega
  · intro hp
    obtain ⟨l,_,he⟩ := Finset.mem_image.mp hp
    have hxe := congrArg (fun p : Cell (side w) (side w) => p.1.val) he
    have hye := congrArg (fun p : Cell (side w) (side w) => p.2.val) he
    cases s <;> cases l <;>
      simp [TurnBridge.start,TurnBridge.finish,TurnBridge.points,TurnBridge.phase,turnMixedCell,turnMixedPoint,radius]
        at hxe hye hx hx' hy hy' <;> omega

private theorem turn_bridge_walk (w : ℕ) (s : TurnBridge) :
    Reachable (turnMacroBoard w) (some 1) ⟨s.start w,turnBoxes w s.phase⟩ ⟨s.finish w,turnBoxes w s.phase⟩ :=
  FiniteWireFrame.walk_rectangle (turnMixedBoxes_floor w _ _) _ _ (turn_bridge_free w s)

/-- The full F/G update includes the actual support walks from and back to the common free dock. -/
private theorem turn_dock_forward (w : ℕ) :
    Reachable (turnMacroBoard w) (some 1) ⟨turnDock w,turnBoxes w false⟩ ⟨turnDock w,turnBoxes w true⟩ :=
  (turn_bridge_walk w .fAcross).trans ((turn_bridge_walk w .fUp).trans ((turn_bridge_walk w .fCorner).trans
    ((turn_forward w).trans ((turn_bridge_walk w .fExitDown).trans (turn_bridge_walk w .fExitAcross)))))

private theorem turn_dock_backward (w : ℕ) :
    Reachable (turnMacroBoard w) (some 1) ⟨turnDock w,turnBoxes w true⟩ ⟨turnDock w,turnBoxes w false⟩ :=
  (turn_bridge_walk w .bAcross).trans ((turn_bridge_walk w .bUp).trans ((turn_bridge_walk w .bToward).trans
    ((turn_bridge_walk w .bCorner).trans ((turn_backward w).trans
      ((turn_bridge_walk w .bExitAcross).trans (turn_bridge_walk w .bExitDown))))))

theorem turn_dock_forward_placed (w : ℕ) {W H : ℕ}
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H} {fixed : Finset (Cell W H)}
    (frame : FiniteWireFrame.Frame (turnActive w) e B fixed) :
    Reachable B (some 1) (e.extend fixed ⟨turnDock w,turnBoxes w false⟩)
      (e.extend fixed ⟨turnDock w,turnBoxes w true⟩) := frame.replay (turn_dock_forward w)

theorem turn_dock_backward_placed (w : ℕ) {W H : ℕ}
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H} {fixed : Finset (Cell W H)}
    (frame : FiniteWireFrame.Frame (turnActive w) e B fixed) :
    Reachable B (some 1) (e.extend fixed ⟨turnDock w,turnBoxes w true⟩)
      (e.extend fixed ⟨turnDock w,turnBoxes w false⟩) := frame.replay (turn_dock_backward w)

end PushPuzzle.PushS.FiniteTools
