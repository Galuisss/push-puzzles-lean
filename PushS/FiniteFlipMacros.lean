/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteFlipState
import Mathlib.Tactic.FinCases

/-! Complete thick-flip phase macros on an explicit active floor. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteTools

open PushFS

/-- Every straight walking segment used by either direction of propagation. -/
inductive FlipSegment
  | rightOuter | lowerOuter | lowerMouth | crossing | upperMouth | upperLeft
  | leftOuter | leftGap | upperSupport | leftSupport | rightGap | lowerSupport | rightSupport

def flipSegmentEnds : FlipSegment → FlipNode × FlipNode
  | .rightOuter => (.right0, .lowerRight)
  | .lowerOuter => (.lowerRight, .lowerMouthOuter)
  | .lowerMouth => (.lowerMouthOuter, .lowerMouth)
  | .crossing => (.lowerMouth, .upperMouth)
  | .upperMouth => (.upperMouth, .upperMouthOuter)
  | .upperLeft => (.upperMouthOuter, .left1UpperOuter)
  | .leftOuter => (.left1UpperOuter, .left1)
  | .leftGap => (.left1, .middleSupport)
  | .upperSupport => (.upperMouthOuter, .leftSupportUpperOuter)
  | .leftSupport => (.leftSupportUpperOuter, .leftSupport)
  | .rightGap => (.right0, .middleReverseSupport)
  | .lowerSupport => (.lowerMouthOuter, .rightSupportLowerOuter)
  | .rightSupport => (.rightSupportLowerOuter, .rightReverseSupport)

set_option maxHeartbeats 1000000 in
private theorem flip_segment_free (w : ℕ) (hw : 2 ≤ w) (q : Bool) (s : FlipSegment)
    (p : Cell (side w) (side w))
    (hx : min (flipNode w (flipSegmentEnds s).1).1.val (flipNode w (flipSegmentEnds s).2).1.val ≤ p.1.val)
    (hx' : p.1.val ≤ max (flipNode w (flipSegmentEnds s).1).1.val (flipNode w (flipSegmentEnds s).2).1.val)
    (hy : min (flipNode w (flipSegmentEnds s).1).2.val (flipNode w (flipSegmentEnds s).2).2.val ≤ p.2.val)
    (hy' : p.2.val ≤ max (flipNode w (flipSegmentEnds s).1).2.val (flipNode w (flipSegmentEnds s).2).2.val) :
    Free (flipMacroBoard w) (flipMixedBoxes w false ⟨3*q.toNat, by have := Bool.toNat_le q; omega⟩ true) p := by
  have hq := Bool.toNat_le q
  constructor
  · apply (FiniteWireFrame.floor_iff _ _ _).mpr
    simp only [flipActive, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · cases s <;> simp [flipSegmentEnds, flipNode, flipNodePoint, radius] at hx hx' hy hy' ⊢ <;> omega
    · cases s <;> simp [flipSegmentEnds, flipNode, flipNodePoint, radius] at hx hx' hy hy' ⊢ <;> omega
    · cases s <;> simp [flipSegmentEnds, flipNode, flipNodePoint, radius] at hx hx' hy hy' ⊢ <;> omega
    · cases s <;> simp [flipSegmentEnds, flipNode, flipNodePoint, radius] at hx hx' hy hy' ⊢ <;> omega
    · intro hp
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
      have hi' := ((flipRectangle w i).mem_cells _ _ _).mp hi
      fin_cases i <;> cases s <;>
        simp [flipRectangle, flipSegmentEnds, flipNode, flipNodePoint, radius] at hi' hx hx' hy hy' <;> omega
  · intro hp
    obtain ⟨l, _, he⟩ := Finset.mem_image.mp hp
    have heX := congrArg (fun z : Cell (side w) (side w) => z.1.val) he
    have heY := congrArg (fun z : Cell (side w) (side w) => z.2.val) he
    cases l <;> cases s <;>
      simp [flipMixedCell, flipCell, flipPoint, flipSegmentEnds, flipNode, flipNodePoint, radius]
        at heX heY hx hx' hy hy' <;> omega

private theorem walk_rectangle {W H : ℕ} {B : Board W H} {boxes : Finset (Cell W H)}
    (hd : Disjoint boxes B.walls) (a b : Cell W H)
    (hfree : ∀ p : Cell W H,
      min a.1.val b.1.val ≤ p.1.val → p.1.val ≤ max a.1.val b.1.val →
      min a.2.val b.2.val ≤ p.2.val → p.2.val ≤ max a.2.val b.2.val → Free B boxes p) :
    Reachable B (some 1) ⟨a, boxes⟩ ⟨b, boxes⟩ := by
  have h1 : Reachable B (some 1) ⟨a, boxes⟩ ⟨(b.1, a.2), boxes⟩ := by
    apply walk_horizontal hd
    intro x hx hx'
    exact hfree (x, a.2) hx hx' (by dsimp; omega) (by dsimp; omega)
  have h2 : Reachable B (some 1) ⟨(b.1, a.2), boxes⟩ ⟨b, boxes⟩ := by
    apply walk_vertical hd
    intro y hy hy'
    exact hfree (b.1, y) (by dsimp; omega) (by dsimp; omega) hy hy'
  exact h1.trans h2

/-- Every segment is a real walk in either direction, with all five actual boxes fixed. -/
theorem flip_segment_walk (w : ℕ) (hw : 2 ≤ w) (q : Bool) (s : FlipSegment) :
    Reachable (flipMacroBoard w) (some 1)
      ⟨flipNode w (flipSegmentEnds s).1,
        flipMixedBoxes w false ⟨3*q.toNat, by have := Bool.toNat_le q; omega⟩ true⟩
      ⟨flipNode w (flipSegmentEnds s).2,
        flipMixedBoxes w false ⟨3*q.toNat, by have := Bool.toNat_le q; omega⟩ true⟩ :=
  walk_rectangle (flipMixedBoxes_floor w _ _ _) _ _ (flip_segment_free w hw q s)

/-- Reversing the specified walking segment changes only the player's position. -/
theorem flip_segment_walk_reverse (w : ℕ) (hw : 2 ≤ w) (q : Bool) (s : FlipSegment) :
    Reachable (flipMacroBoard w) (some 1)
      ⟨flipNode w (flipSegmentEnds s).2,
        flipMixedBoxes w false ⟨3*q.toNat, by have := Bool.toNat_le q; omega⟩ true⟩
      ⟨flipNode w (flipSegmentEnds s).1,
        flipMixedBoxes w false ⟨3*q.toNat, by have := Bool.toNat_le q; omega⟩ true⟩ := by
  apply walk_rectangle (flipMixedBoxes_floor w _ _ _)
  intro p hx hx' hy hy'
  apply flip_segment_free w hw q s p <;> omega

/-- A complete intermediate physical phase, including the middle box's literal slot. -/
structure FlipPhase where
  left : Bool
  middle : Fin 4
  right : Bool

def FlipPhase.cell (w : ℕ) (p : FlipPhase) := flipMixedCell w p.left p.middle p.right

def FlipPhase.boxes (w : ℕ) (p : FlipPhase) := flipMixedBoxes w p.left p.middle p.right

/-- The five forward and five reverse single pushes. -/
inductive FlipPush
  | forwardRight | forwardMiddle0 | forwardMiddle1 | forwardMiddle2 | forwardLeft
  | backwardLeft | backwardMiddle3 | backwardMiddle2 | backwardMiddle1 | backwardRight

def FlipPush.before : FlipPush → FlipPhase
  | .forwardRight => ⟨false, 0, false⟩
  | .forwardMiddle0 => ⟨false, 0, true⟩
  | .forwardMiddle1 => ⟨false, 1, true⟩
  | .forwardMiddle2 => ⟨false, 2, true⟩
  | .forwardLeft => ⟨false, 3, true⟩
  | .backwardLeft => ⟨true, 3, true⟩
  | .backwardMiddle3 => ⟨false, 3, true⟩
  | .backwardMiddle2 => ⟨false, 2, true⟩
  | .backwardMiddle1 => ⟨false, 1, true⟩
  | .backwardRight => ⟨false, 0, true⟩

def FlipPush.after : FlipPush → FlipPhase
  | .forwardRight => ⟨false, 0, true⟩
  | .forwardMiddle0 => ⟨false, 1, true⟩
  | .forwardMiddle1 => ⟨false, 2, true⟩
  | .forwardMiddle2 => ⟨false, 3, true⟩
  | .forwardLeft => ⟨true, 3, true⟩
  | .backwardLeft => ⟨false, 3, true⟩
  | .backwardMiddle3 => ⟨false, 2, true⟩
  | .backwardMiddle2 => ⟨false, 1, true⟩
  | .backwardMiddle1 => ⟨false, 0, true⟩
  | .backwardRight => ⟨false, 0, false⟩

def FlipPush.label : FlipPush → FlipLabel
  | .forwardRight | .backwardRight => .right
  | .forwardLeft | .backwardLeft => .left
  | _ => .middle

def FlipPush.support : FlipPush → FlipNode
  | .forwardRight => .rightSupport
  | .forwardMiddle0 => .middleSupport
  | .forwardMiddle1 => .middle0
  | .forwardMiddle2 => .lowerMouth
  | .forwardLeft => .leftSupport
  | .backwardLeft => .leftReverseSupport
  | .backwardMiddle3 => .middleReverseSupport
  | .backwardMiddle2 => .middle3
  | .backwardMiddle1 => .upperMouth
  | .backwardRight => .rightReverseSupport

def FlipPush.player : FlipPush → FlipNode
  | .forwardRight => .right0
  | .forwardMiddle0 => .middle0
  | .forwardMiddle1 => .lowerMouth
  | .forwardMiddle2 => .upperMouth
  | .forwardLeft => .left0
  | .backwardLeft => .left1
  | .backwardMiddle3 => .middle3
  | .backwardMiddle2 => .upperMouth
  | .backwardMiddle1 => .lowerMouth
  | .backwardRight => .right1

def FlipPush.direction : FlipPush → Direction
  | .forwardRight | .forwardMiddle0 | .forwardMiddle1 | .forwardMiddle2 | .forwardLeft => .east
  | _ => .west

theorem FlipPush.player_eq (w : ℕ) (p : FlipPush) :
    p.before.cell w p.label = flipNode w p.player := by
  cases p <;> apply Prod.ext <;> apply Fin.ext <;>
    dsimp [FlipPhase.cell, FlipPush.before, FlipPush.label, FlipPush.player,
      flipMixedCell, flipCell, flipPoint, flipNode, flipNodePoint, radius]; omega

private theorem flip_push_support_empty (w : ℕ) (hw : 2 ≤ w) (p : FlipPush) :
    flipNode w p.support ∉ p.before.boxes w := by
  intro hp
  obtain ⟨l, _, he⟩ := Finset.mem_image.mp hp
  have heX := congrArg (fun z : Cell (side w) (side w) => z.1.val) he
  cases p <;> cases l <;>
    simp [FlipPush.before, FlipPush.support, flipMixedCell,
      flipCell, flipPoint, flipNode, flipNodePoint, radius] at heX <;> omega

private theorem flip_push_destination_empty (w : ℕ) (hw : 2 ≤ w) (p : FlipPush) :
    p.after.cell w p.label ∉ p.before.boxes w := by
  intro hp
  obtain ⟨l, _, he⟩ := Finset.mem_image.mp hp
  have heX := congrArg (fun z : Cell (side w) (side w) => z.1.val) he
  cases p <;> cases l <;>
    simp [FlipPhase.cell, FlipPush.before, FlipPush.after, FlipPush.label,
      flipMixedCell, flipCell, flipPoint, radius] at heX <;> omega

/-- Every named push moves exactly its intended box and preserves the complete remaining inventory. -/
theorem flip_push (w : ℕ) (hw : 2 ≤ w) (p : FlipPush) :
    Move (flipMacroBoard w) (some 1) p.direction
      ⟨flipNode w p.support, p.before.boxes w⟩ ⟨flipNode w p.player, p.after.boxes w⟩ := by
  have hh := FiniteWireFrame.push_named (B := flipMacroBoard w)
    (support := flipNode w p.support) (d := p.direction) (p.before.cell w) (p.after.cell w)
    (flipMixedCell_injective w hw _ _ _) p.label
  have hrest : ∀ l, l ≠ p.label → p.after.cell w l = p.before.cell w l := by
    intro l hl
    cases p <;> cases l <;>
      simp [FlipPush.label, FlipPhase.cell, FlipPush.before, FlipPush.after, flipMixedCell] at hl ⊢
  have hv : (⟨flipNode w p.support, p.before.boxes w⟩ : State (side w) (side w)).Valid
      (flipMacroBoard w) :=
    ⟨(FiniteWireFrame.floor_iff _ _ _).mpr (flipNode_active w _),
      flipMixedBoxes_floor w _ _ _, flip_push_support_empty w hw p⟩
  have ha : Adjacent p.direction (flipNode w p.support) (p.before.cell w p.label) := by
    cases p <;>
      simp [Adjacent, FlipPush.direction, FlipPush.support, FlipPhase.cell, FlipPush.before,
        FlipPush.label, flipNode, flipNodePoint, flipMixedCell, flipCell, flipPoint, radius] <;> omega
  have hb : Adjacent p.direction (p.before.cell w p.label) (p.after.cell w p.label) := by
    cases p <;>
      simp [Adjacent, FlipPush.direction, FlipPhase.cell, FlipPush.before, FlipPush.after,
        FlipPush.label, flipMixedCell, flipCell, flipPoint, radius]
  have hf : p.after.cell w p.label ∉ (flipMacroBoard w).walls :=
    (FiniteWireFrame.floor_iff _ _ _).mpr (flipMixedCell_active w _ _ _ _)
  have hm := hh hrest hv ha hb hf (flip_push_destination_empty w hw p)
  rw [p.player_eq w] at hm
  exact hm

/-- Forward propagation: right box, three consecutive middle pushes, then left box. -/
theorem flip_forward (w : ℕ) (hw : 2 ≤ w) :
    Reachable (flipMacroBoard w) (some 1)
      ⟨flipNode w .rightSupport, flipBoxes w false⟩ ⟨flipNode w .left0, flipBoxes w true⟩ := by
  change Reachable (flipMacroBoard w) (some 1)
    ⟨flipNode w .rightSupport, flipMixedBoxes w false 0 false⟩
    ⟨flipNode w .left0, flipMixedBoxes w true 3 true⟩
  have h0 : Reachable (flipMacroBoard w) (some 1)
      ⟨flipNode w .rightSupport, flipMixedBoxes w false 0 false⟩
      ⟨flipNode w .right0, flipMixedBoxes w false 0 true⟩ :=
    .single ⟨.east, flip_push w hw .forwardRight⟩
  have h1 := h0.trans (flip_segment_walk w hw false .rightOuter)
  have h2 := h1.trans (flip_segment_walk w hw false .lowerOuter)
  have h3 := h2.trans (flip_segment_walk w hw false .lowerMouth)
  have h4 := h3.trans (flip_segment_walk w hw false .crossing)
  have h5 := h4.trans (flip_segment_walk w hw false .upperMouth)
  have h6 := h5.trans (flip_segment_walk w hw false .upperLeft)
  have h7 := h6.trans (flip_segment_walk w hw false .leftOuter)
  have h8 := h7.trans (flip_segment_walk w hw false .leftGap)
  have h9 := h8.tail ⟨.east, flip_push w hw .forwardMiddle0⟩
  have h10 := h9.tail ⟨.east, flip_push w hw .forwardMiddle1⟩
  have h11 := h10.tail ⟨.east, flip_push w hw .forwardMiddle2⟩
  have h12 := h11.trans (flip_segment_walk w hw true .upperMouth)
  have h13 := h12.trans (flip_segment_walk w hw true .upperSupport)
  have h14 := h13.trans (flip_segment_walk w hw true .leftSupport)
  exact h14.tail ⟨.east, flip_push w hw .forwardLeft⟩

/-- Reverse propagation retains both real exterior neighbors and the complete working inventory. -/
theorem flip_backward (w : ℕ) (hw : 2 ≤ w) :
    Reachable (flipMacroBoard w) (some 1)
      ⟨flipNode w .leftReverseSupport, flipBoxes w true⟩
      ⟨flipNode w .right1, flipBoxes w false⟩ := by
  change Reachable (flipMacroBoard w) (some 1)
    ⟨flipNode w .leftReverseSupport, flipMixedBoxes w true 3 true⟩
    ⟨flipNode w .right1, flipMixedBoxes w false 0 false⟩
  have h0 : Reachable (flipMacroBoard w) (some 1)
      ⟨flipNode w .leftReverseSupport, flipMixedBoxes w true 3 true⟩
      ⟨flipNode w .left1, flipMixedBoxes w false 3 true⟩ :=
    .single ⟨.west, flip_push w hw .backwardLeft⟩
  have h1 := h0.trans (flip_segment_walk_reverse w hw true .leftOuter)
  have h2 := h1.trans (flip_segment_walk_reverse w hw true .upperLeft)
  have h3 := h2.trans (flip_segment_walk_reverse w hw true .upperMouth)
  have h4 := h3.trans (flip_segment_walk_reverse w hw true .crossing)
  have h5 := h4.trans (flip_segment_walk_reverse w hw true .lowerMouth)
  have h6 := h5.trans (flip_segment_walk_reverse w hw true .lowerOuter)
  have h7 := h6.trans (flip_segment_walk_reverse w hw true .rightOuter)
  have h8 := h7.trans (flip_segment_walk w hw true .rightGap)
  have h9 := h8.tail ⟨.west, flip_push w hw .backwardMiddle3⟩
  have h10 := h9.tail ⟨.west, flip_push w hw .backwardMiddle2⟩
  have h11 := h10.tail ⟨.west, flip_push w hw .backwardMiddle1⟩
  have h12 := h11.trans (flip_segment_walk_reverse w hw false .lowerMouth)
  have h13 := h12.trans (flip_segment_walk w hw false .lowerSupport)
  have h14 := h13.trans (flip_segment_walk w hw false .rightSupport)
  exact h14.tail ⟨.west, flip_push w hw .backwardRight⟩

/-- The explicit active-floor contract places the whole forward macro in any ambient board. -/
theorem flip_forward_placed (w : ℕ) (hw : 2 ≤ w) {W H : ℕ}
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H} {fixed : Finset (Cell W H)}
    (frame : FiniteWireFrame.Frame (flipActive w) e B fixed) :
    Reachable B (some 1)
      (e.extend fixed ⟨flipNode w .rightSupport, flipBoxes w false⟩)
      (e.extend fixed ⟨flipNode w .left0, flipBoxes w true⟩) :=
  frame.replay (flip_forward w hw)

theorem flip_backward_placed (w : ℕ) (hw : 2 ≤ w) {W H : ℕ}
    (e : GridEmbedding (side w) (side w) W H) {B : Board W H} {fixed : Finset (Cell W H)}
    (frame : FiniteWireFrame.Frame (flipActive w) e B fixed) :
    Reachable B (some 1)
      (e.extend fixed ⟨flipNode w .leftReverseSupport, flipBoxes w true⟩)
      (e.extend fixed ⟨flipNode w .right1, flipBoxes w false⟩) :=
  frame.replay (flip_backward w hw)

end PushPuzzle.PushS.FiniteTools
