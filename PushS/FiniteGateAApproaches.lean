/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateA
public import PushS.FiniteGateAFrame
public import PushS.FiniteToolApproaches
import Mathlib.Tactic.FinCases

public import PushS.FiniteGeometrySimp

/-! Local A-branch travel into tool supports and along exposed straight lanes. -/

public section
namespace PushPuzzle.PushS.FiniteGateAApproaches

-- The embedded tool coordinates require normalization of nested finite casts.
set_option maxRecDepth 8192

open PushFS FiniteGeometry FiniteGateCore FiniteGateState FiniteGateTools
open FiniteGateA FiniteGateAStraight FiniteGateMacros FiniteSquareLine FiniteLineMacros

attribute [local irreducible] FiniteGeometry.side FiniteTools.side

attribute [local finite_gate_tool_coords]
  upperEmbedding GridEmbedding.translate FiniteTools.turnHorizontalEntry FiniteTools.radius Segment.sweep Sweep.hub Sweep.map Segment.hubCoordinate Segment.lane s t origin FiniteTools.turnVerticalEntry flipEmbedding FiniteTools.flipLowerExit Line.rightGap Segment.base Segment.count flipY

private theorem upper_walk (w : ℕ) (hw : 2 ≤ w) (X : AndPhases w) (q : Bool)
    (goals : Finset (Cell (side w) (side w))) {p r : Cell (FiniteTools.side w) (FiniteTools.side w)}
    (hr : Reachable (FiniteTools.turnMacroBoard w) (some 1)
      ⟨p, FiniteTools.turnBoxes w q⟩ ⟨r, FiniteTools.turnBoxes w q⟩) :
    Reachable (andBoard w goals) (some 1)
      ⟨(upperEmbedding w).cells p, andMixedBoxes w (upperPhases w X q)⟩
      ⟨(upperEmbedding w).cells r, andMixedBoxes w (upperPhases w X q)⟩ := by
  have hh := (upper_frame w hw X goals).replay hr
  simpa only [GridEmbedding.extend, upper_inventory] using hh

private theorem protection_walk (w : ℕ) (hw : 2 ≤ w) (X : AndPhases w) (q : Bool)
    (goals : Finset (Cell (side w) (side w))) {p r : Cell (FiniteTools.side w) (FiniteTools.side w)}
    (hr : Reachable (FiniteTools.turnMacroBoard w) (some 1)
      ⟨p, FiniteTools.turnBoxes w q⟩ ⟨r, FiniteTools.turnBoxes w q⟩) :
    Reachable (andBoard w goals) (some 1)
      ⟨(protectionEmbedding w).cells p, andMixedBoxes w (protectionPhases w X q)⟩
      ⟨(protectionEmbedding w).cells r, andMixedBoxes w (protectionPhases w X q)⟩ := by
  have hh := (protection_frame w hw X goals).replay hr
  simpa only [GridEmbedding.extend, protection_inventory] using hh

private theorem flip_walk (w : ℕ) (hw : 2 ≤ w) (X : AndPhases w) (q : Bool)
    (goals : Finset (Cell (side w) (side w))) {p r : Cell (FiniteTools.side w) (FiniteTools.side w)}
    (hr : Reachable (FiniteTools.flipMacroBoard w) (some 1)
      ⟨p, FiniteTools.flipBoxes w q⟩ ⟨r, FiniteTools.flipBoxes w q⟩) :
    Reachable (andBoard w goals) (some 1)
      ⟨(flipEmbedding w).cells p, andMixedBoxes w (flipPhases w X q)⟩
      ⟨(flipEmbedding w).cells r, andMixedBoxes w (flipPhases w X q)⟩ := by
  have hh := (flip_frame w hw X goals).replay hr
  simpa only [GridEmbedding.extend, flip_inventory] using hh

theorem upper_horizontal (w : ℕ) :
    (upperEmbedding w).cells (FiniteTools.turnHorizontalEntry w) = (Segment.west.sweep w).hub := by
  apply Prod.ext <;> apply Fin.ext <;>
    simp [finite_gate_tool_coords] <;> omega

theorem upper_vertical (w : ℕ) :
    (upperEmbedding w).cells (FiniteTools.turnVerticalEntry w) = (Segment.upper.sweep w).hub := by
  apply Prod.ext <;> apply Fin.ext <;>
    simp [finite_gate_tool_coords] <;> omega

theorem protection_vertical (w : ℕ) :
    (protectionEmbedding w).cells (FiniteTools.turnVerticalEntry w) = (Segment.lower.sweep w).hub := by
  apply Prod.ext <;> apply Fin.ext <;>
    simp [protectionEmbedding, FiniteTools.turnVerticalEntry, FiniteTools.radius,
      Segment.sweep, Sweep.hub, Sweep.map, Segment.hubCoordinate, Segment.lane, s, origin] <;> omega

theorem protection_horizontal (w : ℕ) :
    (protectionEmbedding w).cells (FiniteTools.turnHorizontalEntry w) =
      (Segment.guard.sweep w).map ((Segment.guard.sweep w).line.leftGap, (Segment.guard.sweep w).line.lane) := by
  apply Prod.ext <;> apply Fin.ext <;>
    simp [protectionEmbedding, FiniteTools.turnHorizontalEntry, FiniteTools.radius,
      Segment.sweep, Sweep.map, Line.leftGap, Segment.base, Segment.lane, s, origin] <;> omega

theorem flip_upper_exit (w : ℕ) :
    (flipEmbedding w).cells (FiniteTools.flipUpperExit w) =
      (Segment.lower.sweep w).map ((Segment.lower.sweep w).line.leftGap, (Segment.lower.sweep w).line.lane) := by
  apply Prod.ext <;> apply Fin.ext <;>
    simp [flipEmbedding, FiniteTools.flipUpperExit, FiniteTools.radius,
      Segment.sweep, Sweep.map, Line.leftGap, Segment.base, Segment.lane, s, flipY, origin] <;> omega

theorem flip_lower_exit (w : ℕ) :
    (flipEmbedding w).cells (FiniteTools.flipLowerExit w) =
      (Segment.upper.sweep w).map ((Segment.upper.sweep w).line.rightGap, (Segment.upper.sweep w).line.lane) := by
  apply Prod.ext <;> apply Fin.ext <;>
    simp [finite_gate_tool_coords] <;> omega

/-- The real west-lane endpoint reaches the upper corner's support through its open side. -/
private theorem west_upper (w : ℕ) (hw : 2 ≤ w) (b c : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (andBoard w goals) (some 1)
      ⟨(Segment.west.sweep w).hub, andMixedBoxes w (stage w b c 1)⟩
      ⟨upperEntry w, andMixedBoxes w (stage w b c 1)⟩ := by
  have hh := upper_walk w hw (stage w b c 1) true goals (FiniteTools.turn_enter_horizontal w)
  simpa only [upper_source, upper_horizontal, upperEntry] using hh

private theorem upper_line (w : ℕ) (hw : 2 ≤ w) (b c : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (andBoard w goals) (some 1)
      ⟨upperExit w, andMixedBoxes w (stage w b c 2)⟩
      ⟨(Segment.upper.sweep w).hub, andMixedBoxes w (stage w b c 2)⟩ := by
  have hh := upper_walk w hw (stage w b c 1) false goals (FiniteTools.turn_exit_vertical w)
  simpa only [upper_target, upper_vertical, upperExit] using hh

private theorem line_upper_reverse (w : ℕ) (hw : 2 ≤ w) (b c : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (andBoard w goals) (some 1)
      ⟨(Segment.upper.sweep w).hub, andMixedBoxes w (stage w b c 2)⟩
      ⟨upperEntry w, andMixedBoxes w (stage w b c 2)⟩ := by
  have hh := upper_walk w hw (stage w b c 1) false goals (FiniteTools.turn_enter_vertical w)
  simpa only [upper_target, upper_vertical, upperEntry] using hh

private theorem upper_line_reverse (w : ℕ) (hw : 2 ≤ w) (b c : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (andBoard w goals) (some 1)
      ⟨upperReverseExit w, andMixedBoxes w (stage w b c 1)⟩
      ⟨(Segment.west.sweep w).hub, andMixedBoxes w (stage w b c 1)⟩ := by
  have hh := upper_walk w hw (stage w b c 1) true goals (FiniteTools.turn_exit_horizontal w)
  simpa only [upper_source, upper_horizontal, upperReverseExit] using hh

private theorem line_protection (w : ℕ) (hw : 2 ≤ w) (b c : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (andBoard w goals) (some 1)
      ⟨(Segment.lower.sweep w).hub, andMixedBoxes w (stage w b c 5)⟩
      ⟨protectionEntry w, andMixedBoxes w (stage w b c 5)⟩ := by
  have hh := protection_walk w hw (stage w b c 5) false goals (FiniteTools.turn_enter_vertical w)
  simpa only [protection_source, protection_vertical, protectionEntry] using hh

private theorem protection_line_reverse (w : ℕ) (hw : 2 ≤ w) (b c : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (andBoard w goals) (some 1)
      ⟨protectionReverseExit w, andMixedBoxes w (stage w b c 5)⟩
      ⟨(Segment.lower.sweep w).hub, andMixedBoxes w (stage w b c 5)⟩ := by
  have hh := protection_walk w hw (stage w b c 5) false goals (FiniteTools.turn_exit_vertical w)
  simpa only [protection_source, protection_vertical, protectionReverseExit] using hh

private theorem protection_line (w : ℕ) (hw : 2 ≤ w) (b c : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (andBoard w goals) (some 1)
      ⟨protectionExit w, andMixedBoxes w (stage w b c 6)⟩
      ⟨(Segment.guard.sweep w).hub, andMixedBoxes w (stage w b c 6)⟩ := by
  have hh := protection_walk w hw (stage w b c 5) true goals (FiniteTools.turn_exit_horizontal w)
  rw [protection_target, protection_horizontal] at hh
  have hl := Segment.lane_walk w hw b c false .guard goals
    (Segment.guard.sweep w).line.leftGap (Segment.guard.sweep w).line.hub
    ((Segment.guard.sweep w).line.leftGap_lane) ((Segment.guard.sweep w).line.hub_lane)
  exact hh.trans hl

private theorem line_protection_reverse (w : ℕ) (hw : 2 ≤ w) (b c : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (andBoard w goals) (some 1)
      ⟨(Segment.guard.sweep w).hub, andMixedBoxes w (stage w b c 6)⟩
      ⟨protectionEntry w, andMixedBoxes w (stage w b c 6)⟩ := by
  have hl := Segment.lane_walk w hw b c false .guard goals
    (Segment.guard.sweep w).line.hub (Segment.guard.sweep w).line.leftGap
    ((Segment.guard.sweep w).line.hub_lane) ((Segment.guard.sweep w).line.leftGap_lane)
  have hh := protection_walk w hw (stage w b c 5) true goals (FiniteTools.turn_enter_horizontal w)
  rw [protection_target, protection_horizontal] at hh
  exact hl.trans hh

private theorem flip_line (w : ℕ) (hw : 2 ≤ w) (b c : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (andBoard w goals) (some 1)
      ⟨flipExit w, andMixedBoxes w (stage w b c 4)⟩
      ⟨(Segment.lower.sweep w).hub, andMixedBoxes w (stage w b c 4)⟩ := by
  have hh := flip_walk w hw (stage w b c 3) true goals (FiniteTools.flip_exit_upper w hw)
  rw [flip_target, flip_upper_exit] at hh
  have hl := Segment.lane_walk w hw b c false .lower goals
    (Segment.lower.sweep w).line.leftGap (Segment.lower.sweep w).line.hub
    ((Segment.lower.sweep w).line.leftGap_lane) ((Segment.lower.sweep w).line.hub_lane)
  exact hh.trans hl

private theorem flip_line_reverse (w : ℕ) (hw : 2 ≤ w) (b c : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (andBoard w goals) (some 1)
      ⟨flipReverseExit w, andMixedBoxes w (stage w b c 3)⟩
      ⟨(Segment.upper.sweep w).hub, andMixedBoxes w (stage w b c 3)⟩ := by
  have hh := flip_walk w hw (stage w b c 3) false goals (FiniteTools.flip_exit_lower w hw)
  rw [flip_source, flip_lower_exit] at hh
  have hl := Segment.lane_walk w hw b c true .upper goals
    (Segment.upper.sweep w).line.rightGap (Segment.upper.sweep w).line.hub
    ((Segment.upper.sweep w).line.rightGap_lane) ((Segment.upper.sweep w).line.hub_lane)
  exact hh.trans hl

/-- The two normal flip mouths face the opposite sides of its finite wall islands. -/
@[expose] def leftFlipOuter (w : ℕ) := (flipEmbedding w).cells (FiniteTools.flipNode w .lowerMouthOuter)
/-- The right exterior endpoint of the embedded flip. -/
@[expose] def rightFlipOuter (w : ℕ) := (flipEmbedding w).cells (FiniteTools.flipNode w .upperMouthOuter)

/-- The exposed rectangle joining the upper tools. -/
@[expose] def leftDetour (w : ℕ) : Cell (side w) (side w) :=
  (⟨s w-w-1, by unfold FiniteGeometry.side s origin; omega⟩,
   ⟨t w+2, by unfold FiniteGeometry.side t origin; omega⟩)

/-- The exposed rectangle joining the lower tools. -/
@[expose] def rightDetour (w : ℕ) : Cell (side w) (side w) :=
  (⟨s w+w+1, by unfold FiniteGeometry.side s origin; omega⟩,
   ⟨origin w-2, by unfold FiniteGeometry.side origin; omega⟩)

/-- The four island detours between consecutive A-branch tools. -/
inductive Detour
  | upperAcross | upperDown | lowerAcross | lowerUp

namespace Detour

/-- The source cell of a selected detour. -/
@[expose] def start (w : ℕ) : Detour → Cell (side w) (side w)
  | .upperAcross => (Segment.upper.sweep w).hub
  | .upperDown => leftDetour w
  | .lowerAcross => (Segment.lower.sweep w).hub
  | .lowerUp => rightDetour w

/-- The destination cell of a selected detour. -/
@[expose] def finish (w : ℕ) : Detour → Cell (side w) (side w)
  | .upperAcross => leftDetour w
  | .upperDown => leftFlipOuter w
  | .lowerAcross => rightDetour w
  | .lowerUp => rightFlipOuter w

/-- The source coordinates of a selected detour. -/
@[expose] def startPoint (w : ℕ) : Detour → ℕ × ℕ
  | .upperAcross => (s w-1, t w+2)
  | .upperDown => (s w-w-1, t w+2)
  | .lowerAcross => (s w+1, origin w-2)
  | .lowerUp => (s w+w+1, origin w-2)

/-- The destination coordinates of a selected detour. -/
@[expose] def finishPoint (w : ℕ) : Detour → ℕ × ℕ
  | .upperAcross => (s w-w-1, t w+2)
  | .upperDown => (s w-w-1, flipY w-1)
  | .lowerAcross => (s w+w+1, origin w-2)
  | .lowerUp => (s w+w+1, flipY w-2)

/-- Literal coordinates of the actual detour entrance. -/
theorem start_coordinates (w : ℕ) (k : Detour) :
    ((k.start w).1.val, (k.start w).2.val) = k.startPoint w := by
  cases k <;> apply Prod.ext <;>
    dsimp [start, startPoint, leftDetour, rightDetour,
      Segment.sweep, Sweep.hub, Sweep.map, Segment.hubCoordinate, Segment.lane]

/-- Literal coordinates of the actual detour exit. -/
theorem finish_coordinates (w : ℕ) (k : Detour) :
    ((k.finish w).1.val, (k.finish w).2.val) = k.finishPoint w := by
  cases k <;> apply Prod.ext <;>
    dsimp [finish, finishPoint, leftDetour, rightDetour, leftFlipOuter, rightFlipOuter,
      flipEmbedding, FiniteTools.flipNode, FiniteTools.flipNodePoint]
  all_goals dsimp [s, t, flipY, origin, FiniteTools.radius]; omega

-- The embedded tool coordinates require normalization of nested finite casts.
set_option maxHeartbeats 1000000 in
/-- Every literal detour rectangle is free for the complete mixed local working stock. -/
theorem free (w : ℕ) (hw : 2 ≤ w) (X : AndPhases w) (k : Detour)
    (goals : Finset (Cell (side w) (side w))) (p : Cell (side w) (side w))
    (hx : min (k.start w).1.val (k.finish w).1.val ≤ p.1.val)
    (hx' : p.1.val ≤ max (k.start w).1.val (k.finish w).1.val)
    (hy : min (k.start w).2.val (k.finish w).2.val ≤ p.2.val)
    (hy' : p.2.val ≤ max (k.start w).2.val (k.finish w).2.val) :
    Free (andBoard w goals) (andMixedBoxes w X) p := by
  have hsx : (k.start w).1.val = (k.startPoint w).1 := congrArg Prod.fst (start_coordinates w k)
  have hsy : (k.start w).2.val = (k.startPoint w).2 := congrArg Prod.snd (start_coordinates w k)
  have hfx : (k.finish w).1.val = (k.finishPoint w).1 := congrArg Prod.fst (finish_coordinates w k)
  have hfy : (k.finish w).2.val = (k.finishPoint w).2 := congrArg Prod.snd (finish_coordinates w k)
  rw [hsx, hfx] at hx hx'
  rw [hsy, hfy] at hy hy'
  clear hsx hfx hsy hfy
  constructor
  · intro hp
    obtain ⟨i, hi, hm⟩ := Finset.mem_biUnion.mp hp
    have hm' := ((andRectangle w i).mem_cells _ _ _).mp hm
    cases k <;> fin_cases i <;>
      simp [startPoint, finishPoint, andRectangle, s, t, flipY, origin] at hx hx' hy hy' hm' <;> omega
  · intro hp
    obtain ⟨l, hl, he⟩ := Finset.mem_image.mp hp
    have hpx := congrArg (fun p => p.1.val) he
    have hpy := congrArg (fun p => p.2.val) he
    cases k <;> cases l <;>
      dsimp [startPoint, finishPoint, andMixedCell, andCell, andPoint, s, t, flipY, origin]
        at hx hx' hy hy' hpx hpy <;> omega

private theorem walk (w : ℕ) (hw : 2 ≤ w) (X : AndPhases w) (k : Detour)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (andBoard w goals) (some 1)
      ⟨k.start w, andMixedBoxes w X⟩ ⟨k.finish w, andMixedBoxes w X⟩ := by
  have hstock : Disjoint (andMixedBoxes w X) (andBoard w goals).walls := by
    apply Finset.disjoint_left.mpr
    intro p hp hm
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hp
    exact andMixedCell_floor w hw X l hm
  exact FiniteWireFrame.walk_rectangle hstock _ _ (k.free w hw X goals)

end Detour

/-- Walk around the upper island and through the open normal flip crossing to J's support. -/
private theorem line_flip (w : ℕ) (hw : 2 ≤ w) (b c : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (andBoard w goals) (some 1)
      ⟨(Segment.upper.sweep w).hub, andMixedBoxes w (stage w b c 3)⟩
      ⟨flipEntry w, andMixedBoxes w (stage w b c 3)⟩ := by
  have h1 := Detour.upperAcross.walk w hw (stage w b c 3) goals
  have h2 := Detour.upperDown.walk w hw (stage w b c 3) goals
  have h3 := flip_walk w hw (stage w b c 3) false goals (FiniteTools.flip_enter_forward w hw)
  rw [flip_source] at h3
  exact h1.trans (h2.trans h3)

/-- Walk around the lower island and through the normal crossing to H's reverse support. -/
private theorem line_flip_reverse (w : ℕ) (hw : 2 ≤ w) (b c : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (andBoard w goals) (some 1)
      ⟨(Segment.lower.sweep w).hub, andMixedBoxes w (stage w b c 4)⟩
      ⟨flipReverseEntry w, andMixedBoxes w (stage w b c 4)⟩ := by
  have h1 := Detour.lowerAcross.walk w hw (stage w b c 4) goals
  have h2 := Detour.lowerUp.walk w hw (stage w b c 4) goals
  have h3 := flip_walk w hw (stage w b c 3) true goals (FiniteTools.flip_enter_backward w hw)
  rw [flip_target] at h3
  exact h1.trans (h2.trans h3)

/-- All reverse A-branch entry connections are supplied by explicit local walks. -/
private theorem backwardConnections (w : ℕ) (hw : 2 ≤ w) (b c : Bool)
    (goals : Finset (Cell (side w) (side w))) : BackwardConnections w b c goals where
  line_protection := line_protection_reverse w hw b c goals
  protection_line := protection_line_reverse w hw b c goals
  line_flip := line_flip_reverse w hw b c goals
  flip_line := flip_line_reverse w hw b c goals
  line_upper := line_upper_reverse w hw b c goals
  upper_line := upper_line_reverse w hw b c goals

/-- Every A auxiliary box can be reset through real local turn, flip, and lane paths. -/
theorem and_A_backward_local (w : ℕ) (hw : 2 ≤ w) (b c : Bool)
    (goals : Finset (Cell (side w) (side w))) :
    Reachable (andBoard w goals) (some 1)
      ⟨point w 1 1, andBoxes w true b c⟩
      ⟨(Segment.west.sweep w).hub, andBoxes w false b c⟩ :=
  and_A_backward w hw b c goals (backwardConnections w hw b c goals)

/-- All forward auxiliary travel is local; the last C-side access remains an explicit actual connection. -/
theorem forwardConnections (w : ℕ) (hw : 2 ≤ w) (b : Bool)
    (goals : Finset (Cell (side w) (side w)))
    (hfinal : Reachable (andBoard w goals) (some 1)
      ⟨(Segment.guard.sweep w).hub, andMixedBoxes w (stage w b false 7)⟩
      ⟨point w (w+4) 1, andMixedBoxes w (stage w b false 7)⟩) :
    ForwardConnections w b goals where
  west_upper := west_upper w hw b false goals
  upper_line := upper_line w hw b false goals
  line_flip := line_flip w hw b false goals
  flip_line := flip_line w hw b false goals
  line_protection := line_protection w hw b false goals
  protection_line := protection_line w hw b false goals
  line_trigger := hfinal

/-- The whole protected A branch needs only its final outer-face connection. -/
theorem and_A_forward_local (w : ℕ) (hw : 2 ≤ w) (b : Bool)
    (goals : Finset (Cell (side w) (side w)))
    (hfinal : Reachable (andBoard w goals) (some 1)
      ⟨(Segment.guard.sweep w).hub, andMixedBoxes w (stage w b false 7)⟩
      ⟨point w (w+4) 1, andMixedBoxes w (stage w b false 7)⟩) :
    Reachable (andBoard w goals) (some 1)
      ⟨(Segment.west.sweep w).hub, andBoxes w false b false⟩
      ⟨point w (w+4) 1, andBoxes w true b false⟩ :=
  and_A_forward w hw b goals (forwardConnections w hw b goals hfinal)

end PushPuzzle.PushS.FiniteGateAApproaches
