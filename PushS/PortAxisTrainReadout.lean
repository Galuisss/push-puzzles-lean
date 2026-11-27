/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortAxisTrainRigidity
import all PushS.PortLayoutCoordinates

/-! Exact half-axis hole words and complementary ordinary endpoint parameters. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS RowLabels

/-- The complementary ordinary endpoint parameter and the two outward rod shifts. -/
structure OrdinaryAxisPlacement where
  parameter : ℕ
  upperShift : ℕ
  lowerShift : ℕ

/-- The parameter seen from the lower ordinary endpoint. -/
@[expose] def OrdinaryAxisPlacement.lowerParameter (a : OrdinaryAxisPlacement) : ℕ := 3 - a.parameter

/-- Read the ordinary axis parameters from its actual three train starts. -/
@[expose] def ordinaryAxisPlacement (p : Scales.Parameters) (upper : Endpoint) (b : ThreeBlocks) : OrdinaryAxisPlacement where
  parameter := ((readDepth p upper.level : ℤ) + 4 - b.middle).toNat
  upperShift := (b.first - 1).toNat
  lowerShift := ((p.H : ℤ) - b.last - b.lastLength).toNat

/-- The exact two half-axis hole words of a physical ordinary axis. -/
structure OrdinaryAxisReadout (p : Scales.Parameters) (upper lower : Endpoint)
    (u : State (p.W + 1) (p.H + 1)) (a : OrdinaryAxisPlacement) : Prop where
  parameter_le : a.parameter ≤ 3
  upper_shift_le : a.upperShift + a.parameter ≤ 3
  lower_shift_le : a.lowerShift ≤ a.parameter
  upper_holes (q : Cell (p.W + 1) (p.H + 1)) (axis : q.1.val = p.x upper.port)
      (half : 0 < q.2.val ∧ q.2.val < p.D) :
    q ∈ holes u ↔ q.2.val ≤ a.upperShift ∨
      ((a.upperShift : ℤ) ≤ (q.2.val : ℤ) - readDepth p upper.level ∧
        (q.2.val : ℤ) - readDepth p upper.level ≤ 3 - (a.parameter : ℤ))
  lower_holes (q : Cell (p.W + 1) (p.H + 1)) (axis : q.1.val = p.x upper.port)
      (half : 0 < p.H - q.2.val ∧ p.H - q.2.val < p.D) :
    q ∈ holes u ↔ p.H - q.2.val ≤ a.lowerShift ∨
      ((a.lowerShift : ℤ) ≤ (p.H - q.2.val : ℕ) - (readDepth p lower.level : ℤ) ∧
        (p.H - q.2.val : ℕ) - (readDepth p lower.level : ℤ) ≤ a.parameter)

/-- The decoded ordinary endpoint parameters sum to three. -/
theorem OrdinaryAxisReadout.complementary {p : Scales.Parameters} {upper lower : Endpoint}
    {u : State (p.W + 1) (p.H + 1)} {a : OrdinaryAxisPlacement} (hr : OrdinaryAxisReadout p upper lower u a) :
    a.parameter + a.lowerParameter = 3 := Nat.add_sub_of_le hr.parameter_le

namespace OrdinaryAxisTrainShape

variable {p : Scales.Parameters} {upper lower : Endpoint}
  {u : State (p.W + 1) (p.H + 1)} {b : ThreeBlocks}

private theorem slot_inside (hs : OrdinaryAxisTrainShape p upper lower u b) {y : ℤ} (hy : y ∈ b.slots) :
    0 < y ∧ y < p.H := by
  rw [← hs.slots] at hy
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
  have hR := (Finset.mem_filter.mp (Finset.mem_inter.mp hq).2).2
  exact ⟨by change (0 : ℤ) < q.2.val; omega, by change (q.2.val : ℤ) < p.H; omega⟩

private theorem fits (hs : OrdinaryAxisTrainShape p upper lower u b) (hpos : b.Positive) :
    1 ≤ b.first ∧ b.last + b.lastLength ≤ p.H := by
  have hf := hs.slot_inside ((b.mem_slots b.first).mpr (Or.inl ⟨le_rfl, by have h := hpos.1; omega⟩))
  have hl := hs.slot_inside ((b.mem_slots (b.last + b.lastLength - 1)).mpr
    (Or.inr (Or.inr ⟨by have h := hpos.2.2; omega, by omega⟩)))
  exact ⟨by omega, by omega⟩

private theorem placement_coordinates (hs : OrdinaryAxisTrainShape p upper lower u b) (hpos : b.Positive) :
    let a := ordinaryAxisPlacement p upper b
    (a.parameter : ℤ) = (readDepth p upper.level : ℤ) + 4 - b.middle ∧ a.parameter ≤ 3 ∧
      (a.upperShift : ℤ) = b.first - 1 ∧ (a.lowerShift : ℤ) = (p.H : ℤ) - b.last - b.lastLength := by
  have hfit := hs.fits hpos
  have hgap := hs.gapped
  have hfirst := hs.first_length
  have hmiddle := hs.middle_length
  have hlast := hs.last_length
  have h1 := hpos.1
  have h3 := hpos.2.2
  have hDu := readDepth_add_lt_D p upper.level
  have hDl := readDepth_add_lt_D p lower.level
  have hH : p.H = 2 * p.D := rfl
  change b.first + b.firstLength < b.middle ∧ b.middle + b.middleLength < b.last at hgap
  have ht0 : 0 ≤ (readDepth p upper.level : ℤ) + 4 - b.middle := by omega
  have ht3 : (readDepth p upper.level : ℤ) + 4 - b.middle ≤ 3 := by omega
  have htcast := Int.toNat_of_nonneg ht0
  exact ⟨htcast, by change ((readDepth p upper.level : ℤ) + 4 - b.middle).toNat ≤ 3; omega,
    Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)⟩

private theorem box_iff (hs : OrdinaryAxisTrainShape p upper lower u b)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ ordinaryAxis p upper.port) :
    q ∈ u.boxes ↔ (q.2.val : ℤ) ∈ b.slots := by
  constructor
  · intro hb
    rw [← hs.slots]
    exact Finset.mem_image.mpr ⟨q, Finset.mem_inter.mpr ⟨hb, hq⟩, rfl⟩
  · intro hy
    rw [← hs.slots] at hy
    obtain ⟨r, hr, he⟩ := Finset.mem_image.mp hy
    have hrR := (Finset.mem_filter.mp (Finset.mem_inter.mp hr).2).2
    have hqR := (Finset.mem_filter.mp hq).2
    have hrq : r = q := Direction.south.cell_ext (by change r.1.val = q.1.val; omega) he
    exact hrq ▸ (Finset.mem_inter.mp hr).1

private theorem readout (hs : OrdinaryAxisTrainShape p upper lower u b) (hpos : b.Positive) :
    OrdinaryAxisReadout p upper lower u (ordinaryAxisPlacement p upper b) := by
  have hc := hs.placement_coordinates hpos
  have hgap := hs.gapped
  change b.first + b.firstLength < b.middle ∧ b.middle + b.middleLength < b.last at hgap
  have hfirst := hs.first_length
  have hmiddle := hs.middle_length
  have hlast := hs.last_length
  have h1 := hpos.1
  have h3 := hpos.2.2
  have hDu := readDepth_add_lt_D p upper.level
  have hDl := readDepth_add_lt_D p lower.level
  have hH : p.H = 2 * p.D := rfl
  refine ⟨hc.2.1, by omega, by omega, ?_, ?_⟩
  · intro q hx hy
    have hR : q ∈ ordinaryAxis p upper.port := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx, hy.1, by omega⟩
    rw [mem_holes, hs.box_iff hR, ThreeBlocks.mem_slots]
    omega
  · intro q hx hy
    have hR : q ∈ ordinaryAxis p upper.port := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx, by omega, by omega⟩
    rw [mem_holes, hs.box_iff hR, ThreeBlocks.mem_slots]
    omega

end OrdinaryAxisTrainShape

/-- Every successful ordinary-axis prefix has its genuine half-axis words and complementary parameters in 0..3. -/
theorem physicalInstance_ordinaryAxis_train_readout (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)
    {upper lower : Endpoint} (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hslSide : lower.side = .lower) (hport : lower.port = upper.port)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    ∃ a, OrdinaryAxisReadout p upper lower u a := by
  obtain ⟨b, hs⟩ := l.physicalInstance_ordinaryAxis_train_shape p hl hM ha initial target hu hlow hsuSide hslSide hport hsu hut ht
  have hpos0 := l.ordinaryAxisTrainBlocks_positive p hl hM hu hlow initial
  have hpos : b.Positive := by
    change 0 < b.firstLength ∧ 0 < b.middleLength ∧ 0 < b.lastLength
    rw [hs.first_length, hs.middle_length, hs.last_length]
    exact hpos0
  exact ⟨ordinaryAxisPlacement p upper b, hs.readout hpos⟩

end PushPuzzle.PushS.PortLayout
