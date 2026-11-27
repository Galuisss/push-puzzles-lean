/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceGateRailProjection
public import PushS.PortGateTrainReadout
import all PushS.PortGateTrains

/-! Signed gate samples recover genuine nonempty gaps from weak ordered terminal trains. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout PushS.RowLabels

namespace GateRailBlocks

variable {p : Scales.Parameters} {g : Placement} {kind : Shuttle.Kind}
  {u : State (p.W + 1) (p.H + 1)} {b : ThreeBlocks}

private theorem axis_geometry (p : Scales.Parameters) (g : Placement) (hshape : g.right = g.left + 2) :
    p.x (g.left + 1) = p.x g.left + p.D ∧ p.x g.right = p.x (g.left + 1) + p.D := by
  exact ⟨x_succ_eq p g.left, by simpa only [hshape, Nat.add_assoc] using x_succ_eq p (g.left + 1)⟩

/-- The three prescribed physical train lengths are positive. -/
private theorem positive (hs : GateRailBlocks p g kind u b) : b.Positive := by
  have hD := readDepth_readLength_margin p 0 0
  have hk : kind.kappa.toNat ≤ 4 := by cases kind <;> decide +kernel
  change 0 < b.firstLength ∧ 0 < b.middleLength ∧ 0 < b.lastLength
  rw [hs.first_length, hs.middle_length, hs.last_length]
  omega

private theorem slot_inside (hs : GateRailBlocks p g kind u b) {x : ℤ} (hx : x ∈ b.slots) :
    (p.x g.left : ℤ) < x ∧ x < p.x g.right := by
  rw [← hs.slots] at hx
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
  have hR := (Finset.mem_filter.mp (Finset.mem_inter.mp hq).2).2
  exact ⟨by change (p.x g.left : ℤ) < (q.1.val : ℤ); omega,
    by change (q.1.val : ℤ) < (p.x g.right : ℤ); omega⟩

/-- The complete physical trains fit strictly between their two actual outer axes. -/
theorem fits (hs : GateRailBlocks p g kind u b) :
    (p.x g.left : ℤ) < b.first ∧ b.last + b.lastLength ≤ p.x g.right := by
  have hpos := hs.positive
  have hfirst := hs.slot_inside ((b.mem_slots b.first).mpr (Or.inl ⟨le_rfl, by have h := hpos.1; omega⟩))
  have hlast := hs.slot_inside ((b.mem_slots (b.last + b.lastLength - 1)).mpr
    (Or.inr (Or.inr ⟨by have h := hpos.2.2; omega, by omega⟩)))
  exact ⟨hfirst.1, by omega⟩

/-- Both natural outer hole counts agree with the signed interval differences. -/
theorem placement_coordinates (hs : GateRailBlocks p g kind u b) :
    ((gateTrainPlacement p g b).left : ℤ) = b.first - (p.x g.left : ℤ) - 1 ∧
      ((gateTrainPlacement p g b).right : ℤ) = (p.x g.right : ℤ) - b.last - b.lastLength := by
  have hfit := hs.fits
  exact ⟨Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)⟩

/-- The ordered weak blocks give the signed shuttle nonoverlap inequalities. -/
private theorem placement_separated (hs : GateRailBlocks p g kind u b)
    (hshape : g.right = g.left + 2) :
    ((gateTrainPlacement p g b).left : ℤ) - kind.kappa ≤ (gateTrainPlacement p g b).short ∧
      (gateTrainPlacement p g b).short ≤ 11 - ((gateTrainPlacement p g b).right : ℤ) := by
  have hcoord := hs.placement_coordinates
  have hgap := hs.separated
  have hfirst := hs.first_length
  have hmiddle := hs.middle_length
  have hlast := hs.last_length
  have hD := readDepth_readLength_margin p 0 0
  obtain ⟨hmid, hright⟩ := axis_geometry p g hshape
  have hk : (kind.kappa.toNat : ℤ) = kind.kappa := by cases kind <;> decide +kernel
  have hk4 : kind.kappa.toNat ≤ 4 := by cases kind <;> decide +kernel
  change b.first + b.firstLength ≤ b.middle ∧ b.middle + b.middleLength ≤ b.last at hgap
  change ((gateTrainPlacement p g b).left : ℤ) - kind.kappa ≤ b.middle - (p.x (g.left + 1) : ℤ) - 1 ∧
    b.middle - (p.x (g.left + 1) : ℤ) - 1 ≤ 11 - ((gateTrainPlacement p g b).right : ℤ)
  omega

/-- The actual decoded gate placement satisfies the shuttle nonoverlap inequalities. -/
private theorem placement_ordered (hs : GateRailBlocks p g kind u b)
    (hshape : g.right = g.left + 2) :
    (gateTrainPlacement p g b).Ordered kind := by
  have hg := hs.placement_separated hshape
  exact hg

/-- Occupancy anywhere on the actual open rail is exactly occupancy in its three train intervals. -/
theorem box_iff (hs : GateRailBlocks p g kind u b) {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ gateOpenRail p g) :
    q ∈ u.boxes ↔ (q.1.val : ℤ) ∈ b.slots := by
  rw [← hs.slots]
  exact BoxMask.box_mem_iff_image (axis := .east) (lane := p.H - readDepth p 1)
    (fun _ hr => (Finset.mem_filter.mp hr).2.1) u hq

/-- On the core's complete sampled window, actual physical holes are exactly the signed G/J gaps. -/
theorem core_hole (hs : GateRailBlocks p g kind u b) (hshape : g.right = g.left + 2)
    {q : Cell (p.W + 1) (p.H + 1)} (hy : q.2.val = p.H - readDepth p 1)
    (hx : -2 ≤ (q.1.val : ℤ) - p.x (g.left + 1) ∧ (q.1.val : ℤ) - p.x (g.left + 1) ≤ 12) :
    q ∈ holes u ↔ (gateTrainPlacement p g b).hole kind ((q.1.val : ℤ) - p.x (g.left + 1)) := by
  have hcoord := hs.placement_coordinates
  have hg := hs.placement_separated hshape
  change ((gateTrainPlacement p g b).left : ℤ) - kind.kappa ≤ b.middle - (p.x (g.left + 1) : ℤ) - 1 ∧
    b.middle - (p.x (g.left + 1) : ℤ) - 1 ≤ 11 - ((gateTrainPlacement p g b).right : ℤ) at hg
  have hD := readDepth_readLength_margin p 0 0
  obtain ⟨hmid, hright⟩ := axis_geometry p g hshape
  have hk : (kind.kappa.toNat : ℤ) = kind.kappa := by cases kind <;> decide +kernel
  have hk4 : kind.kappa.toNat ≤ 4 := by cases kind <;> decide +kernel
  have hR : q ∈ gateOpenRail p g := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy, by omega, by omega⟩
  rw [mem_holes, hs.box_iff hR, ThreeBlocks.mem_slots]
  have hfirst := hs.first_length
  have hmiddle := hs.middle_length
  have hlast := hs.last_length
  simp only [Shuttle.Placement.hole, Shuttle.Placement.leftGap, Shuttle.Placement.rightGap]
  change (¬ ((b.first ≤ (q.1.val : ℤ) ∧ (q.1.val : ℤ) < b.first + b.firstLength) ∨
      (b.middle ≤ (q.1.val : ℤ) ∧ (q.1.val : ℤ) < b.middle + b.middleLength) ∨
      (b.last ≤ (q.1.val : ℤ) ∧ (q.1.val : ℤ) < b.last + b.lastLength))) ↔
    (((gateTrainPlacement p g b).left : ℤ) - kind.kappa + 1 ≤ (q.1.val : ℤ) - p.x (g.left + 1) ∧
      (q.1.val : ℤ) - p.x (g.left + 1) ≤ b.middle - (p.x (g.left + 1) : ℤ) - 1) ∨
      (b.middle - (p.x (g.left + 1) : ℤ) - 1 + 3 ≤ (q.1.val : ℤ) - p.x (g.left + 1) ∧
        (q.1.val : ℤ) - p.x (g.left + 1) ≤ 13 - ((gateTrainPlacement p g b).right : ℤ))
  omega

/-- Accepted signed samples and real outer payments separate both original marked train gaps. -/
theorem gapped_of_samples (hs : GateRailBlocks p g kind u b) (hshape : g.right = g.left + 2)
    (target : Shuttle.Target) (legal : target.Legal kind)
    (samples : Shuttle.Samples kind target (gateTrainPlacement p g b))
    (left : target.left = false → 2 ≤ (gateTrainPlacement p g b).left)
    (right : target.relay = false → 2 ≤ (gateTrainPlacement p g b).right) :
    b.Gapped ∧
      (target.heavy = true ↔ 6 ≤ (gateTrainPlacement p g b).short) ∧
      (target.left = true ↔ (gateTrainPlacement p g b).left ≤ 1) ∧
      (target.relay = true ↔ (gateTrainPlacement p g b).right ≤ 1) := by
  obtain ⟨heavy, leftBit, relay, ⟨x, hx⟩, ⟨y, hy⟩⟩ :=
    Shuttle.readout kind target (gateTrainPlacement p g b) legal (hs.placement_ordered hshape) samples left right
  have coordinates := hs.placement_coordinates
  obtain ⟨middleAxis, rightAxis⟩ := axis_geometry p g hshape
  have firstLength := hs.first_length
  have middleLength := hs.middle_length
  have lastLength := hs.last_length
  have margin := readDepth_readLength_margin p 0 0
  have kappa : (kind.kappa.toNat : ℤ) = kind.kappa := by cases kind <;> decide +kernel
  have kappaBound : kind.kappa.toNat ≤ 4 := by cases kind <;> decide +kernel
  change ((gateTrainPlacement p g b).left : ℤ) - kind.kappa + 1 ≤ x ∧
    x ≤ (gateTrainPlacement p g b).short at hx
  change (gateTrainPlacement p g b).short + 3 ≤ y ∧
    y ≤ 13 - ((gateTrainPlacement p g b).right : ℤ) at hy
  have shortCoordinate : (gateTrainPlacement p g b).short = b.middle - (p.x (g.left + 1) : ℤ) - 1 := rfl
  refine ⟨?_, heavy, leftBit, relay⟩
  change b.first + b.firstLength < b.middle ∧ b.middle + b.middleLength < b.last
  omega

end GateRailBlocks

end PushPuzzle.Push.AcceptanceSoundness
