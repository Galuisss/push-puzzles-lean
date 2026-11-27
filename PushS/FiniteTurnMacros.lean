/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteTurn

/-! Complete concave-turn phase changes with real player walks and exact exterior inventory. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteTools

open PushFS

inductive TurnSegment
  | forwardAcross | forwardUp | backwardDown | backwardAcross

def turnSegmentEnds : TurnSegment → TurnNode × TurnNode
  | .forwardAcross => (.vertical0, .horizontalOuter)
  | .forwardUp => (.horizontalOuter, .horizontalSupport)
  | .backwardDown => (.horizontal1, .verticalOuter)
  | .backwardAcross => (.verticalOuter, .verticalSupport)

private theorem turn_segment_free (w : ℕ) (s : TurnSegment) (p : Cell (side w) (side w))
    (hx : min (turnNode w (turnSegmentEnds s).1).1.val (turnNode w (turnSegmentEnds s).2).1.val ≤ p.1.val)
    (hx' : p.1.val ≤ max (turnNode w (turnSegmentEnds s).1).1.val (turnNode w (turnSegmentEnds s).2).1.val)
    (hy : min (turnNode w (turnSegmentEnds s).1).2.val (turnNode w (turnSegmentEnds s).2).2.val ≤ p.2.val)
    (hy' : p.2.val ≤ max (turnNode w (turnSegmentEnds s).1).2.val (turnNode w (turnSegmentEnds s).2).2.val) :
    Free (turnMacroBoard w) (turnMixedBoxes w false true) p := by
  constructor
  · apply (FiniteWireFrame.floor_iff _ _ _).mpr
    rw [turnActive, FiniteGeometry.Rectangle.mem_cells]
    cases s <;> simp [turnSegmentEnds, turnNode, turnNodePoint, radius] at hx hx' hy hy' ⊢ <;> omega
  · intro hp
    obtain ⟨l, _, he⟩ := Finset.mem_image.mp hp
    have heX := congrArg (fun z : Cell (side w) (side w) => z.1.val) he
    have heY := congrArg (fun z : Cell (side w) (side w) => z.2.val) he
    cases s <;> cases l <;>
      simp [turnMixedCell, turnMixedPoint, turnSegmentEnds, turnNode, turnNodePoint, radius]
        at heX heY hx hx' hy hy' <;> omega

private theorem turn_segment_walk (w : ℕ) (s : TurnSegment) :
    Reachable (turnMacroBoard w) (some 1)
      ⟨turnNode w (turnSegmentEnds s).1, turnMixedBoxes w false true⟩
      ⟨turnNode w (turnSegmentEnds s).2, turnMixedBoxes w false true⟩ :=
  FiniteWireFrame.walk_rectangle (turnMixedBoxes_floor w false true) _ _ (turn_segment_free w s)

inductive TurnPush
  | forwardDown | forwardRight | backwardLeft | backwardUp

def TurnPush.before : TurnPush → Bool × Bool
  | .forwardDown => (false, false)
  | .forwardRight | .backwardUp => (false, true)
  | .backwardLeft => (true, true)

def TurnPush.after : TurnPush → Bool × Bool
  | .forwardDown | .backwardLeft => (false, true)
  | .forwardRight => (true, true)
  | .backwardUp => (false, false)

def TurnPush.label : TurnPush → TurnLabel
  | .forwardDown | .backwardUp => .vertical
  | _ => .horizontal

def TurnPush.support : TurnPush → TurnNode
  | .forwardDown | .backwardLeft => .corner
  | .forwardRight => .horizontalSupport
  | .backwardUp => .verticalSupport

def TurnPush.player : TurnPush → TurnNode
  | .forwardDown => .vertical0
  | .forwardRight => .horizontal0
  | .backwardLeft => .horizontal1
  | .backwardUp => .vertical1

def TurnPush.direction : TurnPush → Direction
  | .forwardDown => .south
  | .forwardRight => .east
  | .backwardLeft => .west
  | .backwardUp => .north

theorem TurnPush.player_eq (w : ℕ) (p : TurnPush) :
    turnMixedCell w p.before.1 p.before.2 p.label = turnNode w p.player := by
  cases p <;> apply Prod.ext <;> apply Fin.ext <;>
    dsimp [TurnPush.before, TurnPush.label, TurnPush.player,
      turnMixedCell, turnMixedPoint, turnNode, turnNodePoint, radius]; omega

private theorem turn_push_support_empty (w : ℕ) (p : TurnPush) :
    turnNode w p.support ∉ turnMixedBoxes w p.before.1 p.before.2 := by
  intro hp
  obtain ⟨l, _, he⟩ := Finset.mem_image.mp hp
  have hx := congrArg (fun z : Cell (side w) (side w) => z.1.val) he
  have hy := congrArg (fun z : Cell (side w) (side w) => z.2.val) he
  cases p <;> cases l <;>
    simp [TurnPush.before, TurnPush.support, turnMixedCell, turnMixedPoint,
      turnNode, turnNodePoint, radius] at hx hy

private theorem turn_push_destination_empty (w : ℕ) (p : TurnPush) :
    turnMixedCell w p.after.1 p.after.2 p.label ∉ turnMixedBoxes w p.before.1 p.before.2 := by
  intro hp
  obtain ⟨l, _, he⟩ := Finset.mem_image.mp hp
  have hx := congrArg (fun z : Cell (side w) (side w) => z.1.val) he
  have hy := congrArg (fun z : Cell (side w) (side w) => z.2.val) he
  cases p <;> cases l <;>
    simp [TurnPush.before, TurnPush.after, TurnPush.label, turnMixedCell, turnMixedPoint, radius]
      at hx hy

/-- Every actual turn push preserves all other named boxes, including both exterior neighbors. -/
theorem turn_push (w : ℕ) (p : TurnPush) :
    Move (turnMacroBoard w) (some 1) p.direction
      ⟨turnNode w p.support, turnMixedBoxes w p.before.1 p.before.2⟩
      ⟨turnNode w p.player, turnMixedBoxes w p.after.1 p.after.2⟩ := by
  have hrest : ∀ l, l ≠ p.label →
      turnMixedCell w p.after.1 p.after.2 l = turnMixedCell w p.before.1 p.before.2 l := by
    intro l hl
    cases p <;> cases l <;>
      simp [TurnPush.label, TurnPush.before, TurnPush.after, turnMixedCell, turnMixedPoint] at hl ⊢
  have hv : (⟨turnNode w p.support, turnMixedBoxes w p.before.1 p.before.2⟩ :
      State (side w) (side w)).Valid (turnMacroBoard w) :=
    ⟨(FiniteWireFrame.floor_iff _ _ _).mpr (turnNode_active w _),
      turnMixedBoxes_floor w _ _, turn_push_support_empty w p⟩
  have ha : Adjacent p.direction (turnNode w p.support)
      (turnMixedCell w p.before.1 p.before.2 p.label) := by
    cases p <;> simp [Adjacent, TurnPush.direction, TurnPush.before, TurnPush.support,
      TurnPush.label, turnMixedCell, turnMixedPoint, turnNode, turnNodePoint, radius]
  have hb : Adjacent p.direction (turnMixedCell w p.before.1 p.before.2 p.label)
      (turnMixedCell w p.after.1 p.after.2 p.label) := by
    cases p <;> simp [Adjacent, TurnPush.direction, TurnPush.before, TurnPush.after,
      TurnPush.label, turnMixedCell, turnMixedPoint, radius]
  have hh := FiniteWireFrame.push_named (B := turnMacroBoard w)
    (support := turnNode w p.support) (d := p.direction)
    (turnMixedCell w p.before.1 p.before.2) (turnMixedCell w p.after.1 p.after.2)
    (turnMixedCell_injective w _ _) p.label hrest hv ha hb
    ((FiniteWireFrame.floor_iff _ _ _).mpr (turnMixedCell_active w _ _ _))
    (turn_push_destination_empty w p)
  rw [p.player_eq w] at hh
  exact hh

/-- The forward corner macro moves the vertical box, walks continuously, then moves the horizontal box. -/
theorem turn_forward (w : ℕ) :
    Reachable (turnMacroBoard w) (some 1)
      ⟨turnNode w .corner, turnBoxes w false⟩
      ⟨turnNode w .horizontal0, turnBoxes w true⟩ := by
  have h0 : Reachable (turnMacroBoard w) (some 1)
      ⟨turnNode w .corner, turnMixedBoxes w false false⟩
      ⟨turnNode w .vertical0, turnMixedBoxes w false true⟩ :=
    .single ⟨.south, turn_push w .forwardDown⟩
  have h1 := h0.trans (turn_segment_walk w .forwardAcross)
  have h2 := h1.trans (turn_segment_walk w .forwardUp)
  exact h2.tail ⟨.east, turn_push w .forwardRight⟩

/-- The reverse corner macro walks from the old horizontal box to the vertical support. -/
theorem turn_backward (w : ℕ) :
    Reachable (turnMacroBoard w) (some 1)
      ⟨turnNode w .corner, turnBoxes w true⟩
      ⟨turnNode w .vertical1, turnBoxes w false⟩ := by
  have h0 : Reachable (turnMacroBoard w) (some 1)
      ⟨turnNode w .corner, turnMixedBoxes w true true⟩
      ⟨turnNode w .horizontal1, turnMixedBoxes w false true⟩ :=
    .single ⟨.west, turn_push w .backwardLeft⟩
  have h1 := h0.trans (turn_segment_walk w .backwardDown)
  have h2 := h1.trans (turn_segment_walk w .backwardAcross)
  exact h2.tail ⟨.north, turn_push w .backwardUp⟩

theorem turn_forward_placed (w : ℕ) {W H : ℕ}
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H} {fixed : Finset (Cell W H)}
    (frame : FiniteWireFrame.Frame (turnActive w) e B fixed) :
    Reachable B (some 1)
      (e.extend fixed ⟨turnNode w .corner, turnBoxes w false⟩)
      (e.extend fixed ⟨turnNode w .horizontal0, turnBoxes w true⟩) :=
  frame.replay (turn_forward w)

theorem turn_backward_placed (w : ℕ) {W H : ℕ}
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H} {fixed : Finset (Cell W H)}
    (frame : FiniteWireFrame.Frame (turnActive w) e B fixed) :
    Reachable B (some 1)
      (e.extend fixed ⟨turnNode w .corner, turnBoxes w true⟩)
      (e.extend fixed ⟨turnNode w .vertical1, turnBoxes w false⟩) :=
  frame.replay (turn_backward w)

end PushPuzzle.PushS.FiniteTools
