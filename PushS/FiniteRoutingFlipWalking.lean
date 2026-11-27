/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingFlipMacros
import Mathlib.Tactic.FinCases

/-! Actual flip access through its normal mouth, followed by exact outer-lane returns. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting.Line.Tool.Flip

open PushFS FiniteTools

inductive Bridge | fVertical | fRow | fExit | bVertical | bRow | bExit

def Bridge.phase : Bridge → Bool
  | .fVertical | .fRow | .bExit => false
  | _ => true

def Bridge.points (w : ℕ) : Bridge → (ℕ × ℕ) × (ℕ × ℕ)
  | .fVertical | .bVertical => ((radius w+2,radius w-w-1),(radius w+2,radius w))
  | .fRow => ((radius w+2,radius w),(radius w+w+1,radius w))
  | .bRow => ((radius w+2,radius w),(radius w+2-w,radius w))
  | .fExit => ((radius w-w,radius w),(radius w-w,radius w-w-1))
  | .bExit => ((radius w+w+3,radius w),(radius w+w+3,radius w+w+1))

def Bridge.start (w : ℕ) (b : Bridge) : Cell (side w) (side w) :=
  (⟨(b.points w).1.1, by cases b <;> dsimp [Bridge.points, radius, side] <;> omega⟩,
   ⟨(b.points w).1.2, by cases b <;> dsimp [Bridge.points, radius, side] <;> omega⟩)

def Bridge.finish (w : ℕ) (b : Bridge) : Cell (side w) (side w) :=
  (⟨(b.points w).2.1, by cases b <;> dsimp [Bridge.points, radius, side] <;> omega⟩,
   ⟨(b.points w).2.2, by cases b <;> dsimp [Bridge.points, radius, side] <;> omega⟩)

set_option maxHeartbeats 1000000 in
private theorem bridge_free (w : ℕ) (hw : 2 ≤ w) (b : Bridge) (p : Cell (side w) (side w))
    (hx : min (b.start w).1.val (b.finish w).1.val ≤ p.1.val)
    (hx' : p.1.val ≤ max (b.start w).1.val (b.finish w).1.val)
    (hy : min (b.start w).2.val (b.finish w).2.val ≤ p.2.val)
    (hy' : p.2.val ≤ max (b.start w).2.val (b.finish w).2.val) :
    Free (flipMacroBoard w) (flipBoxes w b.phase) p := by
  constructor
  · apply (FiniteWireFrame.floor_iff _ _ _).mpr
    simp only [flipActive, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    all_goals try { cases b <;> simp [Bridge.start, Bridge.finish, Bridge.points, radius] at hx hx' hy hy' ⊢ <;> omega }
    intro hp
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
    have hi' := (FiniteGeometry.Rectangle.mem_cells _ _ _ _).mp hi
    fin_cases i <;> cases b <;>
      simp [flipRectangle, Bridge.start, Bridge.finish, Bridge.points, radius] at hi' hx hx' hy hy' <;> omega
  · intro hp
    obtain ⟨l, _, he⟩ := Finset.mem_image.mp hp
    have hxe := congrArg (fun p : Cell (side w) (side w) => p.1.val) he
    have hye := congrArg (fun p : Cell (side w) (side w) => p.2.val) he
    cases b <;> cases l <;>
      simp [Bridge.start, Bridge.finish, Bridge.points, Bridge.phase, flipCell, flipPoint, radius]
        at hxe hye hx hx' hy hy' <;> omega

theorem bridge_walk (w : ℕ) (hw : 2 ≤ w) (b : Bridge) :
    Reachable (flipMacroBoard w) (some 1)
      ⟨b.start w, flipBoxes w b.phase⟩ ⟨b.finish w, flipBoxes w b.phase⟩ := by
  have hd := flipMixedBoxes_floor w b.phase ⟨3*b.phase.toNat, by have := Bool.toNat_le b.phase; omega⟩ b.phase
  change Disjoint (flipBoxes w b.phase) (flipMacroBoard w).walls at hd
  exact FiniteWireFrame.walk_rectangle hd _ _ (bridge_free w hw b)

private theorem bridge_placed (w : ℕ) (hw : 2 ≤ w) (before after : List Atom) (n m : ℕ)
    (hn : buffer w ≤ n) (hm : buffer w ≤ m) (above : Bool) (b : Bridge) :
    Reachable (macroBoard w (before++ .line n:: .flip:: .line m::after) above) (some 1)
      ⟨(place w before after n m above).cells (b.start w),
        cutBoxes w hw (cut w before n b.phase) (before++ .line n:: .flip:: .line m::after)⟩
      ⟨(place w before after n m above).cells (b.finish w),
        cutBoxes w hw (cut w before n b.phase) (before++ .line n:: .flip:: .line m::after)⟩ := by
  have hn' : 0 < n := by unfold buffer at hn; omega
  have hm' : 1 < m := by unfold buffer at hm; omega
  have hh := (frame w hw before after n m hn hm above).replay (bridge_walk w hw b)
  change Reachable _ _ ⟨_, _⟩ ⟨_, _⟩ at hh
  rw [← inventory w hw before after n m hn' hm' above b.phase] at hh
  exact hh

/-- Every macro starts and finishes on a literal exterior lane, with the same complete cut stock. -/
private theorem outer_low_to_high (w : ℕ) (hw : 2 ≤ w) (before after : List Atom) (n m : ℕ)
    (hn : buffer w ≤ n) (hm : buffer w ≤ m) (above : Bool) :
    Reachable (macroBoard w (before++ .line n:: .flip:: .line m::after) above) (some 1)
      ⟨(place w before after n m above).cells (Bridge.fVertical.start w),
        cutBoxes w hw (cut w before n false) (before++ .line n:: .flip:: .line m::after)⟩
      ⟨(place w before after n m above).cells (Bridge.fExit.finish w),
        cutBoxes w hw (cut w before n true) (before++ .line n:: .flip:: .line m::after)⟩ :=
  (bridge_placed w hw before after n m hn hm above .fVertical).trans
    ((bridge_placed w hw before after n m hn hm above .fRow).trans
      ((low_to_high w hw before after n m hn hm above).trans
        (bridge_placed w hw before after n m hn hm above .fExit)))

private theorem outer_high_to_low (w : ℕ) (hw : 2 ≤ w) (before after : List Atom) (n m : ℕ)
    (hn : buffer w ≤ n) (hm : buffer w ≤ m) (above : Bool) :
    Reachable (macroBoard w (before++ .line n:: .flip:: .line m::after) above) (some 1)
      ⟨(place w before after n m above).cells (Bridge.bVertical.start w),
        cutBoxes w hw (cut w before n true) (before++ .line n:: .flip:: .line m::after)⟩
      ⟨(place w before after n m above).cells (Bridge.bExit.finish w),
        cutBoxes w hw (cut w before n false) (before++ .line n:: .flip:: .line m::after)⟩ :=
  (bridge_placed w hw before after n m hn hm above .bVertical).trans
    ((bridge_placed w hw before after n m hn hm above .bRow).trans
      ((high_to_low w hw before after n m hn hm above).trans
        (bridge_placed w hw before after n m hn hm above .bExit)))

private theorem outer_eq (w : ℕ) (before after : List Atom) (n m : ℕ) (above north : Bool)
    (p : Cell (side w) (side w)) (hy : p.2.val = (laneY w north).val) :
    (place w before after n m above).cells p =
      outerCell w _ (if north then !(exitSide above before) else exitSide above before)
        ((place w before after n m above).cells p).1 := by
  apply Prod.ext
  · rfl
  · apply Fin.ext
    change (if exitSide above before then 2*radius w-p.2.val else p.2.val) = _
    rw [hy]
    cases north <;> cases hs : exitSide above before <;>
      simp [outerCell, laneY, radius] <;> omega

private theorem outer_reachable (w : ℕ) (hw : 2 ≤ w) (before after : List Atom) (n m : ℕ)
    (hn : buffer w ≤ n) (hm : buffer w ≤ m) (above north : Bool) (q : Bool)
    (p : Cell (side w) (side w)) (hp : p ∈ flipActive w) (hy : p.2.val = (laneY w north).val) :
    Reachable (macroBoard w (before++ .line n:: .flip:: .line m::after) above) (some 1)
      ⟨outerHub w _, cutBoxes w hw (cut w before n q) (before++ .line n:: .flip:: .line m::after)⟩
      ⟨(place w before after n m above).cells p,
        cutBoxes w hw (cut w before n q) (before++ .line n:: .flip:: .line m::after)⟩ := by
  have hb := (Finset.mem_filter.mp (floor w hw before after n m hn hm above p hp)).2
  rw [outer_eq w before after n m above north p hy]
  exact outer_macro_connected_of_flip w hw _ _
    ⟨before++[.line n], .line m::after, by simp only [List.append_assoc, List.singleton_append]⟩
    above true _ (outerHubX w _) _ (by dsimp [outerHubX]; omega)
    (by dsimp [outerHubX]; omega) hb.1 hb.2.1

private theorem outer_return (w : ℕ) (hw : 2 ≤ w) (before after : List Atom) (n m : ℕ)
    (hn : buffer w ≤ n) (hm : buffer w ≤ m) (above north : Bool) (q : Bool)
    (p : Cell (side w) (side w)) (hp : p ∈ flipActive w) (hy : p.2.val = (laneY w north).val) :
    Reachable (macroBoard w (before++ .line n:: .flip:: .line m::after) above) (some 1)
      ⟨(place w before after n m above).cells p,
        cutBoxes w hw (cut w before n q) (before++ .line n:: .flip:: .line m::after)⟩
      ⟨outerHub w _, cutBoxes w hw (cut w before n q) (before++ .line n:: .flip:: .line m::after)⟩ := by
  have hb := (Finset.mem_filter.mp (floor w hw before after n m hn hm above p hp)).2
  rw [outer_eq w before after n m above north p hy]
  exact outer_macro_connected_of_flip w hw _ _
    ⟨before++[.line n], .line m::after, by simp only [List.append_assoc, List.singleton_append]⟩
    above _ true _ (outerHubX w _) hb.1 hb.2.1
    (by dsimp [outerHubX]; omega) (by dsimp [outerHubX]; omega)

theorem bridge_start_active (w : ℕ) (hw : 2 ≤ w) (b : Bridge) : b.start w ∈ flipActive w := by
  apply (FiniteWireFrame.floor_iff _ _ _).mp
  exact (bridge_free w hw b _ (by omega) (by omega) (by omega) (by omega)).1

theorem bridge_finish_active (w : ℕ) (hw : 2 ≤ w) (b : Bridge) : b.finish w ∈ flipActive w := by
  apply (FiniteWireFrame.floor_iff _ _ _).mp
  exact (bridge_free w hw b _ (by omega) (by omega) (by omega) (by omega)).1

theorem sweep_low_high (w : ℕ) (hw : 2 ≤ w) (before after : List Atom) (n m : ℕ)
    (hn : buffer w ≤ n) (hm : buffer w ≤ m) (above : Bool) :
    Reachable (macroBoard w (before++ .line n:: .flip:: .line m::after) above) (some 1)
      ⟨outerHub w _, cutBoxes w hw (ownedCount w before+n+3) (before++ .line n:: .flip:: .line m::after)⟩
      ⟨outerHub w _, cutBoxes w hw (ownedCount w before+n) (before++ .line n:: .flip:: .line m::after)⟩ := by
  have he := outer_reachable w hw before after n m hn hm above true false
    (Bridge.fVertical.start w) (bridge_start_active w hw _) rfl
  have hx := outer_return w hw before after n m hn hm above true true
    (Bridge.fExit.finish w) (bridge_finish_active w hw _) rfl
  exact he.trans ((outer_low_to_high w hw before after n m hn hm above).trans hx)

theorem sweep_high_low (w : ℕ) (hw : 2 ≤ w) (before after : List Atom) (n m : ℕ)
    (hn : buffer w ≤ n) (hm : buffer w ≤ m) (above : Bool) :
    Reachable (macroBoard w (before++ .line n:: .flip:: .line m::after) above) (some 1)
      ⟨outerHub w _, cutBoxes w hw (ownedCount w before+n) (before++ .line n:: .flip:: .line m::after)⟩
      ⟨outerHub w _, cutBoxes w hw (ownedCount w before+n+3) (before++ .line n:: .flip:: .line m::after)⟩ := by
  have he := outer_reachable w hw before after n m hn hm above true true
    (Bridge.bVertical.start w) (bridge_start_active w hw _) rfl
  have hx := outer_return w hw before after n m hn hm above false false
    (Bridge.bExit.finish w) (bridge_finish_active w hw _) rfl
  exact he.trans ((outer_high_to_low w hw before after n m hn hm above).trans hx)

end PushPuzzle.PushS.FiniteRouting.Line.Tool.Flip
