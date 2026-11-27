/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushFS.Gadgets.Wires.Soundness.Tools
public import PushS.FiniteTools

/-! Successful-path thresholds for arbitrarily thick parity and face-switch tools. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteToolSoundness

open PushFS PushFS.Gadgets
open Wires.Soundness

variable {W H : ℕ}

/-- Both normal phases of an odd-width parity roof. -/
def ParityNormal (x m : ℕ) (S : Configuration W H) : Prop :=
  (S.left.1.val = x ∧ S.right.1.val = x + m + 2) ∨
  (S.left.1.val = x + 1 ∧ S.right.1.val = x + m + 3)

private theorem ParityNormal.good {x m : ℕ} {S : Configuration W H} (hn : ParityNormal x m S) :
    Good (x+2) (x+m+1) S := by
  rcases hn with ⟨hl, hr⟩ | ⟨hl, hr⟩ <;> simp only [Good] <;> omega

/-- The parity roof transmits a threshold through all successful intermediate states. -/
theorem parity_signal_on_successful_path {B : Board W H} {x m y : ℕ}
    {initial S final : Configuration W H}
    (hw : StripWalls B (x+2) (x+m+1) y)
    (hstart : ParityNormal x m initial) (hfinish : ParityNormal x m final)
    (hbefore : Relation.ReflTransGen (GeometricStep B y) initial S)
    (hafter : Relation.ReflTransGen (GeometricStep B y) S final) :
    x+1 ≤ S.left.1.val → x+m+3 ≤ S.right.1.val := by
  have hg := good_on_successful_path hw hstart.good hfinish.good hbefore hafter
  rcases hg with hg | hg <;> omega

/-- Both full phases of the three working boxes of a width-`w` flip. -/
def FlipNormal (x w : ℕ) (S : AND.Configuration W H) : Prop :=
  (S.a.1.val+w = x ∧ S.b.1.val = x ∧ S.c.1.val = x+w+2) ∨
  (S.a.1.val+w = x+1 ∧ S.b.1.val = x+3 ∧ S.c.1.val = x+w+3)

private theorem FlipNormal.good_left {x w : ℕ} {S : AND.Configuration W H}
    (hx : w ≤ x) (hn : FlipNormal x w S) : Good (x+2-w) x (leftPair S) := by
  rcases hn with ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ <;> simp only [Good, leftPair] <;> omega

private theorem FlipNormal.good_right {x w : ℕ} {S : AND.Configuration W H}
    (hn : FlipNormal x w S) : Good (x+3) (x+w+1) (rightPair S) := by
  rcases hn with ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ <;> simp only [Good, rightPair] <;> omega

/-- The two thick islands transmit the flip signal through arbitrary middle-box offsets. -/
theorem flip_signal_on_successful_path {B : Board W H} {x w y : ℕ}
    {initial S final : AND.Configuration W H}
    (hx : w ≤ x)
    (hleft : StripWalls B (x+2-w) x y) (hright : StripWalls B (x+3) (x+w+1) y)
    (hstart : FlipNormal x w initial) (hfinish : FlipNormal x w final)
    (hbefore : Relation.ReflTransGen (TripleStep B y) initial S)
    (hafter : Relation.ReflTransGen (TripleStep B y) S final) :
    x+1 ≤ S.a.1.val+w → x+w+3 ≤ S.c.1.val := by
  have hl := good_on_successful_path hleft (hstart.good_left hx) (hfinish.good_left hx)
    (hbefore.lift leftPair (fun _ _ ht => leftPair_geometric ht))
    (hafter.lift leftPair (fun _ _ ht => leftPair_geometric ht))
  have hr := good_on_successful_path hright hstart.good_right hfinish.good_right
    (hbefore.lift rightPair (fun _ _ ht => rightPair_geometric ht))
    (hafter.lift rightPair (fun _ _ ht => rightPair_geometric ht))
  simp only [Good, leftPair, rightPair] at hl hr
  omega

attribute [local irreducible] FiniteTools.side

/-- Both concrete sides of the odd parity roof enclose its entire threshold interval. -/
theorem parity_stripWalls (w : ℕ) (hw : 2 ≤ w)
    (goals : Finset (Cell (FiniteTools.side w) (FiniteTools.side w))) :
    StripWalls ⟨FiniteTools.parityWalls w, goals⟩ (FiniteTools.radius w+2)
      (FiniteTools.radius w+FiniteTools.paritySpan w+1) (FiniteTools.radius w) := by
  have hm := FiniteTools.paritySpan_bounds w
  constructor
  · intro p hy hx hx'
    apply Finset.mem_biUnion.mpr
    refine ⟨0, Finset.mem_univ _, ?_⟩
    apply (FiniteGeometry.Rectangle.mem_cells (FiniteTools.parityRectangle w 0) _ _ p).mpr
    simp [FiniteTools.parityRectangle, FiniteTools.radius, FiniteTools.side] at *
    omega
  · intro p hy hx hx'
    apply Finset.mem_biUnion.mpr
    refine ⟨1, Finset.mem_univ _, ?_⟩
    apply (FiniteGeometry.Rectangle.mem_cells (FiniteTools.parityRectangle w 1) _ _ p).mpr
    simp [FiniteTools.parityRectangle, FiniteTools.radius] at *
    omega

theorem flip_left_stripWalls (w : ℕ) (hw : 2 ≤ w)
    (goals : Finset (Cell (FiniteTools.side w) (FiniteTools.side w))) :
    StripWalls ⟨FiniteTools.flipWalls w, goals⟩ (FiniteTools.radius w+2-w)
      (FiniteTools.radius w) (FiniteTools.radius w) := by
  constructor
  · intro p hy hx hx'
    apply Finset.mem_biUnion.mpr
    refine ⟨0, Finset.mem_univ _, ?_⟩
    apply (FiniteGeometry.Rectangle.mem_cells (FiniteTools.flipRectangle w 0) _ _ p).mpr
    simp [FiniteTools.flipRectangle, FiniteTools.radius] at *
    omega
  · intro p hy hx hx'
    apply Finset.mem_biUnion.mpr
    refine ⟨2, Finset.mem_univ _, ?_⟩
    apply (FiniteGeometry.Rectangle.mem_cells (FiniteTools.flipRectangle w 2) _ _ p).mpr
    simp [FiniteTools.flipRectangle, FiniteTools.radius] at *
    omega

theorem flip_right_stripWalls (w : ℕ) (hw : 2 ≤ w)
    (goals : Finset (Cell (FiniteTools.side w) (FiniteTools.side w))) :
    StripWalls ⟨FiniteTools.flipWalls w, goals⟩ (FiniteTools.radius w+3)
      (FiniteTools.radius w+w+1) (FiniteTools.radius w) := by
  constructor
  · intro p hy hx hx'
    apply Finset.mem_biUnion.mpr
    refine ⟨1, Finset.mem_univ _, ?_⟩
    apply (FiniteGeometry.Rectangle.mem_cells (FiniteTools.flipRectangle w 1) _ _ p).mpr
    simp [FiniteTools.flipRectangle, FiniteTools.radius] at *
    omega
  · intro p hy hx hx'
    apply Finset.mem_biUnion.mpr
    refine ⟨3, Finset.mem_univ _, ?_⟩
    apply (FiniteGeometry.Rectangle.mem_cells (FiniteTools.flipRectangle w 3) _ _ p).mpr
    simp [FiniteTools.flipRectangle, FiniteTools.radius] at *
    omega

def parityConfiguration (w : ℕ) (q : Bool)
    (player : Cell (FiniteTools.side w) (FiniteTools.side w)) :
    Configuration (FiniteTools.side w) (FiniteTools.side w) :=
  ⟨⟨player, FiniteTools.parityBoxes w q⟩,
    FiniteTools.parityCell w q .left, FiniteTools.parityCell w q .right⟩

def flipConfiguration (w : ℕ) (q : Bool)
    (player : Cell (FiniteTools.side w) (FiniteTools.side w)) :
    AND.Configuration (FiniteTools.side w) (FiniteTools.side w) :=
  ⟨⟨player, FiniteTools.flipBoxes w q⟩, FiniteTools.flipCell w q .left,
    FiniteTools.flipCell w q .middle, FiniteTools.flipCell w q .right⟩

theorem parityConfiguration_normal (w : ℕ) (q : Bool)
    (player : Cell (FiniteTools.side w) (FiniteTools.side w)) :
    ParityNormal (FiniteTools.radius w) (FiniteTools.paritySpan w)
      (parityConfiguration w q player) := by
  cases q <;>
    simp [ParityNormal, parityConfiguration, FiniteTools.parityCell, FiniteTools.parityPoint]

theorem flipConfiguration_normal (w : ℕ) (q : Bool)
    (player : Cell (FiniteTools.side w) (FiniteTools.side w)) :
    FlipNormal (FiniteTools.radius w) w (flipConfiguration w q player) := by
  cases q <;>
    simp [FlipNormal, flipConfiguration, FiniteTools.flipCell, FiniteTools.flipPoint,
      FiniteTools.radius] <;> omega

end PushPuzzle.PushS.FiniteToolSoundness
