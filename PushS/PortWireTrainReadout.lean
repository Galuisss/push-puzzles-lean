/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortWireTrains

/-! Complementary endpoint hole counts from an actual ordinary WIRE's rigid train. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS

namespace WireTrainShape

variable {p : Scales.Parameters} {g : Placement} {u : State (p.W + 1) (p.H + 1)} {first : ℤ}

private theorem slot_inside (hs : WireTrainShape p g u first) {x : ℤ}
    (hx : x ∈ Finset.Ico first (first + wireTrainLength p g)) :
    (p.x g.left : ℤ) < x ∧ x < p.x g.right := by
  rw [← hs.slots] at hx
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
  have hR := (Finset.mem_filter.mp (Finset.mem_inter.mp hq).2).2
  exact ⟨by change (p.x g.left : ℤ) < (q.1.val : ℤ); omega,
    by change (q.1.val : ℤ) < (p.x g.right : ℤ); omega⟩

/-- The complete physical train lies between its actual two port axes. -/
theorem fits (hs : WireTrainShape p g u first) (hlen : 0 < wireTrainLength p g) :
    (p.x g.left : ℤ) < first ∧ first + wireTrainLength p g ≤ p.x g.right := by
  have hfirst := hs.slot_inside (x := first) (Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩)
  have hlast := hs.slot_inside (x := first + wireTrainLength p g - 1) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
  exact ⟨hfirst.1, by omega⟩

/-- Every actual rail box is exactly one coordinate of the same full rigid train. -/
theorem box_iff (hs : WireTrainShape p g u first) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ wireOpenRail p g) : q ∈ u.boxes ↔ (q.1.val : ℤ) ∈ Finset.Ico first (first + wireTrainLength p g) := by
  rw [← hs.slots]
  exact BoxMask.box_mem_iff_image (axis := .east)
    (lane := if g.side = .upper then readDepth p g.level else p.H - readDepth p g.level)
    (fun _ hr => (Finset.mem_filter.mp hr).2.1) u hq

end WireTrainShape

/-- The two actual WIRE endpoint gaps, described on the complete open work-row rail. -/
structure WireRailReadout (p : Scales.Parameters) (g : Placement)
    (u : State (p.W + 1) (p.H + 1)) (left right : ℕ) : Prop where
  /-- Its two natural endpoint hole counts use the entire three-hole inventory. -/
  holes_sum : left + right = 3
  /-- Every actual hole lies in precisely the corresponding left or right endpoint interval. -/
  rail_holes (q : Cell (p.W + 1) (p.H + 1)) (rail : q ∈ wireOpenRail p g) :
    q ∈ holes u ↔ (q.1.val : ℤ) ≤ (p.x g.left : ℤ) + left ∨ (p.x g.right : ℤ) - right ≤ q.1.val

/-- An actual full-span WIRE train directly determines both natural endpoint gap readouts. -/
theorem WireTrainShape.readout {p : Scales.Parameters} {g : Placement}
    {u : State (p.W + 1) (p.H + 1)} {first : ℤ} (hs : WireTrainShape p g u first)
    (hlen : 0 < wireTrainLength p g) :
    WireRailReadout p g u (first - (p.x g.left : ℤ) - 1).toNat
      ((p.x g.right : ℤ) - first - wireTrainLength p g).toNat := by
  have hfit := hs.fits hlen
  have hleft : (((first - (p.x g.left : ℤ) - 1).toNat : ℕ) : ℤ) = first - (p.x g.left : ℤ) - 1 :=
    Int.toNat_of_nonneg (by omega)
  have hright : ((((p.x g.right : ℤ) - first - wireTrainLength p g).toNat : ℕ) : ℤ) =
      (p.x g.right : ℤ) - first - wireTrainLength p g := Int.toNat_of_nonneg (by omega)
  have hlength : ((wireTrainLength p g : ℕ) : ℤ) = (p.x g.right : ℤ) - p.x g.left - 4 := by
    unfold wireTrainLength at hlen ⊢
    omega
  refine ⟨by omega, ?_⟩
  intro q hq
  rw [mem_holes, hs.box_iff hq, Finset.mem_Ico]
  omega

/-- Every successful physical ordinary WIRE prefix has complementary endpoint gaps and this full exact hole word. -/
theorem physicalInstance_wire_train_readout (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)
    {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    ∃ left right, WireRailReadout p g u left right := by
  obtain ⟨first, hs⟩ := l.physicalInstance_wire_train_shape p hl hM ha initial target hg hw hsu hut ht
  exact ⟨_, _, hs.readout (l.wireTrainLength_positive p hl hg hw)⟩

end PushPuzzle.PushS.PortLayout
