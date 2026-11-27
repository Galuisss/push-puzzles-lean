/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessWireRowInventory
public import PushS.PortEndpointHorizontalReadout
import all Push.AcceptanceProgramWireRowStockPaid
import all Push.AcceptanceSoundnessWireTrimStock
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceSoundnessCentral
import all PushS.PortWireIndexing

/-! Exact accepted WIRE accounts force every r-trim collateral hole onto its own work rail. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate

/-- The real WIRE prepayments are exactly the two complete r-trim collateral accounts. -/
theorem canonical_wire_trim_collateral_exact {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t)) :
    (holes t ∩ wireOpenRail p g) \
      roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target) (holes t) 23 =
      rTrimCollateral l p target (holes t) (wireWorkLeft g) ∪
        rTrimCollateral l p target (holes t) (wireWorkRight g) := by
  let A := roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
    (targetHoles l p target) (holes t) 23
  let M := holes t ∩ wireOpenRail p g
  let N := A ∩ wireOpenRail p g
  let left := rTrimCollateral l p target (holes t) (wireWorkLeft g)
  let right := rTrimCollateral l p target (holes t) (wireWorkRight g)
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) accepted).2
  have source : A ⊆ holes t := scan_subset (roundResidual_eval _ _ _ 23 hc)
  have sub : N ⊆ M := by
    intro q hq
    exact Finset.mem_inter.mpr ⟨source (Finset.mem_inter.mp hq).1, (Finset.mem_inter.mp hq).2⟩
  have difference : M \ N = M \ A := by
    ext q
    simp only [M, N, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have count := Finset.card_sdiff_add_card_eq_card sub
  rw [difference] at count
  have terminal := canonical_wire_terminal_holes l p hl hM haxes initial target hgate hg hw hr accepted
  have work := canonical_wire_work_stock_exact l p hl hM haxes initial target hgate hg hw hr accepted
  change M.card = 3 at terminal
  change N.card + endpointWorkDelta l p target (wireWorkLeft g) + endpointWorkDelta l p target (wireWorkRight g) = 3 at work
  have paidCount : (M \ A).card = endpointWorkDelta l p target (wireWorkLeft g) +
      endpointWorkDelta l p target (wireWorkRight g) := by omega
  have contained : M \ A ⊆ left ∪ right :=
    canonical_wire_prework_paid l p hl hM haxes initial target hgate hg hw hr accepted
  obtain ⟨heL, heR⟩ := wire_endpoints l hg hw
  have heL' : wireWorkLeft g ∈ l.endpoints := by simpa only [wireWorkLeft, wireLeft] using heL
  have heR' : wireWorkRight g ∈ l.endpoints := by
    simpa only [wireWorkRight, wireRight, hw, Option.isSome_none, ite_false, Nat.add_zero] using heR
  have lc : left.card = endpointWorkDelta l p target (wireWorkLeft g) :=
    canonical_r_trim_collateral_card l p hl hM haxes initial target hgate _ heL' hr accepted
  have rc : right.card = endpointWorkDelta l p target (wireWorkRight g) :=
    canonical_r_trim_collateral_card l p hl hM haxes initial target hgate _ heR' hr accepted
  have union := Finset.card_union_le left right
  have cardinal : (left ∪ right).card ≤ (M \ A).card := by omega
  have same : M \ A = left ∪ right := Finset.eq_of_subset_of_card_le contained cardinal
  exact same

/-- A WIRE endpoint's emitted nonzero r-work quota supplies its actual second horizontal hole. -/
theorem canonical_wire_horizontal_target_payment {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {e : Endpoint} (endpoint : e = wireWorkLeft g ∨ e = wireWorkRight g)
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (payment : endpointWorkDelta l p target e = 1)
    {horizontal : ℕ} (word : EndpointHorizontalReadout p e t horizontal) : 2 ≤ horizontal := by
  obtain ⟨heL, heR⟩ := wire_endpoints l hg hw
  have he : e ∈ l.endpoints := by
    rcases endpoint with rfl | rfl
    · simpa only [wireWorkLeft, wireLeft] using heL
    · simpa only [wireWorkRight, wireRight, hw, Option.isSome_none, ite_false, Nat.add_zero] using heR
  have card := canonical_r_trim_collateral_card l p hl hM haxes initial target hgate e he hr accepted
  rw [payment] at card
  obtain ⟨q, hq⟩ := Finset.card_pos.mp (show 0 < (rTrimCollateral l p target (holes t) e).card by omega)
  have together : q ∈ rTrimCollateral l p target (holes t) (wireWorkLeft g) ∪
      rTrimCollateral l p target (holes t) (wireWorkRight g) := by
    rcases endpoint with rfl | rfl
    · exact Finset.mem_union_left _ hq
    · exact Finset.mem_union_right _ hq
  rw [← canonical_wire_trim_collateral_exact l p hl hM haxes initial target hgate hg hw hr accepted] at together
  obtain ⟨hole, rail⟩ := Finset.mem_inter.mp (Finset.mem_sdiff.mp together).1
  have column := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hq).1).2
  have row := (Finset.mem_filter.mp rail).2.1
  have col : q.1.val = if e.inward then p.x e.port + 2 else p.x e.port - 2 := by
    simpa only [EndpointStreet.column_r] using column
  have depth : q.2.val = if e.side = .upper then readDepth p e.level else p.H - readDepth p e.level := by
    rcases endpoint with rfl | rfl <;> exact row
  exact (word.near_holes q 2 (by omega) (by omega) col depth).mp hole

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
