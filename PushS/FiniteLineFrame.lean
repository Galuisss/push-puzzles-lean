/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteLineMacros
public import PushS.FiniteWireFrame

/-! Place an entire straight sweep using only its actual track and walking lane. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteLineMacros.Line

open PushFS

variable {W H U V : ℕ}

local instance (L : Line W H) (x : Fin W) : Decidable (L.track x) := by
  unfold track
  infer_instance

local instance (L : Line W H) (x : Fin W) : Decidable (L.laneSegment x) := by
  unfold laneSegment
  infer_instance

/-- The full active footprint of every forward and reverse frontier update. -/
def active (L : Line W H) : Finset (Cell W H) :=
  Finset.univ.filter fun p =>
    (p.2 = L.row ∧ L.track p.1) ∨ (p.2 = L.lane ∧ L.laneSegment p.1)

@[simp] theorem mem_active (L : Line W H) (p : Cell W H) :
    p ∈ L.active ↔ (p.2 = L.row ∧ L.track p.1) ∨ (p.2 = L.lane ∧ L.laneSegment p.1) := by
  simp only [active, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem proofFrame (L : Line W H) :
    L.Frame (FiniteWireFrame.board L.active ∅) ∅ where
  fixed_floor := Finset.disjoint_empty_left _
  track_free _x hx := ⟨(FiniteWireFrame.floor_iff _ _ _).mpr ((L.mem_active _).mpr (Or.inl ⟨rfl, hx⟩)),
    Finset.notMem_empty _⟩
  lane_free _x hx := ⟨(FiniteWireFrame.floor_iff _ _ _).mpr ((L.mem_active _).mpr (Or.inr ⟨rfl, hx⟩)),
    Finset.notMem_empty _⟩

/-- Replay the full forward chain with its real ambient fixed stock, including prepared port neighbors. -/
theorem forward_placed (L : Line W H) (e : GridEmbedding W H U V) {B : Board U V}
    {fixed : Finset (Cell U V)} (F : FiniteWireFrame.Frame L.active e B fixed) :
    Reachable B (some 1)
      (e.extend fixed ⟨(L.hub, L.lane), Finset.univ.image (L.position 0)⟩)
      (e.extend fixed ⟨(L.hub, L.lane), Finset.univ.image (L.position L.count)⟩) := by
  have hr := (proofFrame L).forward
  simp only [boxes, Finset.empty_union] at hr
  exact F.replay hr

/-- Replay the full reverse chain with every real ambient fixed box retained. -/
theorem backward_placed (L : Line W H) (e : GridEmbedding W H U V) {B : Board U V}
    {fixed : Finset (Cell U V)} (F : FiniteWireFrame.Frame L.active e B fixed) :
    Reachable B (some 1)
      (e.extend fixed ⟨(L.hub, L.lane), Finset.univ.image (L.position L.count)⟩)
      (e.extend fixed ⟨(L.hub, L.lane), Finset.univ.image (L.position 0)⟩) := by
  have hr := (proofFrame L).backward
  simp only [boxes, Finset.empty_union] at hr
  exact F.replay hr

/-- The support gap immediately before the first low slot. -/
def leftGap (L : Line W H) : Fin W := ⟨L.base-1, by have hb := L.fits; omega⟩

def rightGap (L : Line W H) : Fin W := ⟨L.base+2*L.count, by have hb := L.fits; omega⟩

theorem leftGap_lane (L : Line W H) : L.laneSegment L.leftGap := by
  dsimp [leftGap, laneSegment]
  omega

theorem rightGap_lane (L : Line W H) : L.laneSegment L.rightGap := by
  have hb := L.base_pos
  dsimp [rightGap, laneSegment]
  omega

theorem hub_lane (L : Line W H) : L.laneSegment L.hub := by
  dsimp [laneSegment]
  omega

/-- Travel along the exposed lane with the exact current frontier inventory fixed. -/
theorem Frame.lane_walk {L : Line W H} {B : Board W H} {fixed : Finset (Cell W H)}
    (F : L.Frame B fixed) (j : ℕ) (a b : Fin W) (ha : L.laneSegment a) (hb : L.laneSegment b) :
    Reachable B (some 1) ⟨(a, L.lane), L.boxes fixed j⟩ ⟨(b, L.lane), L.boxes fixed j⟩ := by
  apply walk_horizontal (F.boxes_floor j)
  intro x hx hx'
  apply F.lane_free_boxes j x
  dsimp [laneSegment] at *
  omega

end PushPuzzle.PushS.FiniteLineMacros.Line
