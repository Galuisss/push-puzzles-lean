/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessWireTrimPayment
public import Push.AcceptanceSoundnessRowLedger
public import Push.AcceptanceSoundnessWireFixedStock
public import Push.AcceptanceProgramWireRowStockDisjoint
public import Push.AcceptanceProgramWireRowStockFixed
import all Push.AcceptanceProgramWireRowStockSlots
import all PushS.PortWireIndexing
import all PushS.PortSegments

/-! Full working-row quotas cancel all one-way ordinary WIRE inventory gains. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram
open scoped BigOperators

private theorem disjoint_row_inventory {w h : ℕ} (A F : Finset (Cell w h))
    (K : Finset Placement) (rails : Placement → Finset (Cell w h)) (row : ℕ)
    (hF : F ⊆ A.filter fun q => q.2.val = row)
    (hdis : ∀ g ∈ K, Disjoint F (rails g))
    (hpair : Set.PairwiseDisjoint (↑K) rails)
    (hrows : ∀ g ∈ K, ∀ q ∈ rails g, q.2.val = row) :
    F.card + ∑ g ∈ K, (A ∩ rails g).card ≤ (A.filter fun q => q.2.val = row).card := by
  classical
  have hsub : F ∪ K.biUnion (fun g => A ∩ rails g) ⊆ A.filter fun q => q.2.val = row := by
    intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · exact hF hq
    · obtain ⟨g, hg, hq⟩ := Finset.mem_biUnion.mp hq
      exact Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp hq).1, hrows g hg q (Finset.mem_inter.mp hq).2⟩
  have hd : Disjoint F (K.biUnion fun g => A ∩ rails g) := by
    apply Finset.disjoint_left.mpr
    intro q hq hR
    obtain ⟨g, hg, hqR⟩ := Finset.mem_biUnion.mp hR
    exact Finset.disjoint_left.mp (hdis g hg) hq (Finset.mem_inter.mp hqR).2
  have hp : Set.PairwiseDisjoint (↑K) (fun g => A ∩ rails g) := by
    intro g hg g' hg' hne
    exact (hpair hg hg' hne).mono Finset.inter_subset_right Finset.inter_subset_right
  have hb := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd, Finset.card_biUnion hp] at hb
  exact hb

private theorem three_of_sum_bound (K : Finset Placement) (holes : Placement → ℕ)
    (hge : ∀ g ∈ K, 3 ≤ holes g) (hsum : ∑ g ∈ K, holes g ≤ 3 * K.card) :
    ∀ g ∈ K, holes g = 3 := by
  classical
  intro g hg
  have hrest : 3 * (K.erase g).card ≤ ∑ a ∈ K.erase g, holes a := by
    have h := Finset.sum_le_sum (s := K.erase g)
      (f := fun _ => 3) (g := holes) (fun a ha => hge a (Finset.mem_of_mem_erase ha))
    simpa only [Finset.sum_const, smul_eq_mul, Nat.mul_comm] using h
  have hcard := Finset.card_erase_add_one hg
  have he := Finset.sum_erase_add K holes hg
  have hown := hge g hg
  omega

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate

private theorem wire_inventory_account {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    (PushS.holes t ∩ wireOpenRail p g).card = 3 ∧
      (roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target) (PushS.holes t) 23 ∩ wireOpenRail p g).card +
        endpointWorkDelta l p target (wireWorkLeft g) + endpointWorkDelta l p target (wireWorkRight g) = 3 := by
  classical
  let E := PushS.holes t
  let A := roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
    (targetHoles l p target) E 23
  let F := wireRowFixedStock l p g.side g.level
  let K := wireRowPlacements l g.side g.level
  let delta := fun h => endpointWorkDelta l p target (wireWorkLeft h) + endpointWorkDelta l p target (wireWorkRight h)
  obtain ⟨hj, hjM⟩ := placement_level_bounds l hl hg
  have hjm := hjM.trans hM
  have hordinary : g.side = .upper ∨ 2 ≤ g.level := by
    cases hs : g.side
    · exact Or.inl rfl
    · right
      obtain ⟨i, hi, hgi⟩ : ∃ i : l.pages.lowerPage.Index,
          l.pages.lowerPage.group i = .wire g.left g.right ∧ l.pages.lowerLevel i = g.level := by
        have ho := wire_owner l hg hw
        rw [hs] at ho
        exact ho
      have hb := l.pages.lowerLevel_wire_ge_two hl hi
      omega
  have hmem : g ∈ K := Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hg, hw, rfl, rfl⟩
  have hfixed : F ⊆ A.filter fun q => q.2.val = wireWorkRow p g.side g.level := by
    intro q hq
    exact Finset.mem_filter.mpr
      ⟨canonical_wire_fixed_stock_at_work l p hl hM haxes initial target hgate g.side hj hjm hordinary hr ha hq,
        (Finset.mem_filter.mp hq).2⟩
  have hdis : ∀ h ∈ K, Disjoint F (wireOpenRail p h) := by
    intro h hh
    obtain ⟨hh, hhw, _, _⟩ := Finset.mem_filter.mp hh
    apply Finset.disjoint_left.mpr
    intro q hq hrail
    have hf := emit_remaining_subset _ _ (Finset.mem_filter.mp hq).1
    exact Finset.disjoint_left.mp (wire_fixed_disjoint l p hl hM haxes target (List.mem_toFinset.mp hh) hhw) hf hrail
  have hrows : ∀ h ∈ K, ∀ q ∈ wireOpenRail p h, q.2.val = wireWorkRow p g.side g.level := by
    intro h hh q hq
    obtain ⟨_, _, hs, hj'⟩ := Finset.mem_filter.mp hh
    have hy := (Finset.mem_filter.mp hq).2.1
    rw [hs, hj', readDepth_eq p hj hjm] at hy
    exact hy
  have hstock := disjoint_row_inventory A F K (wireOpenRail p) (wireWorkRow p g.side g.level)
    hfixed hdis (wireRowPlacements_rails_pairwise l p hl g.side g.level) hrows
  have hrow : (A.filter fun q => q.2.val = wireWorkRow p g.side g.level).card =
      ((wireWorkReference l p target).filter fun q => q.2.val = wireWorkRow p g.side g.level).card := by
    exact canonical_work_row_input_card l p hl hM haxes initial target hr ha _
      (wire_work_row_requested l p hl hM hg)
  have href : ((wireWorkReference l p target).filter fun q => q.2.val = wireWorkRow p g.side g.level).card +
      ∑ h ∈ K, delta h = F.card + 3 * K.card :=
    wireWork_row_card_deltas l p hl hM haxes target g.side hj hjm hordinary
  have hsum : ∑ h ∈ K, (E ∩ wireOpenRail p h).card ≤
      (∑ h ∈ K, (A ∩ wireOpenRail p h).card) + ∑ h ∈ K, delta h := by
    have h := Finset.sum_le_sum (s := K)
      (f := fun h => (E ∩ wireOpenRail p h).card)
      (g := fun h => (A ∩ wireOpenRail p h).card + delta h) (by
        intro h hh
        obtain ⟨hh, hhw, _, _⟩ := Finset.mem_filter.mp hh
        have hb := canonical_wire_work_stock_bound l p hl hM haxes initial target hgate (List.mem_toFinset.mp hh) hhw hr ha
        simpa only [delta, Nat.add_assoc] using hb)
    simpa only [Finset.sum_add_distrib] using h
  have hbound : ∑ h ∈ K, (E ∩ wireOpenRail p h).card ≤ 3 * K.card := by omega
  have terminal : ∀ h ∈ K, (E ∩ wireOpenRail p h).card = 3 := by
    apply three_of_sum_bound K (fun h => (E ∩ wireOpenRail p h).card) _ hbound
    intro h hh
    obtain ⟨hh, hhw, _, _⟩ := Finset.mem_filter.mp hh
    exact canonical_wire_holes_ge_three l p hl hM haxes initial target hgate (List.mem_toFinset.mp hh) hhw hr .refl ha
  have lower : ∀ h ∈ K, 3 ≤ (A ∩ wireOpenRail p h).card + delta h := by
    intro h hh
    have th := terminal h hh
    obtain ⟨hh, hhw, _, _⟩ := Finset.mem_filter.mp hh
    have bound := canonical_wire_work_stock_bound l p hl hM haxes initial target hgate (List.mem_toFinset.mp hh) hhw hr ha
    change (E ∩ wireOpenRail p h).card ≤ (A ∩ wireOpenRail p h).card +
      endpointWorkDelta l p target (wireWorkLeft h) + endpointWorkDelta l p target (wireWorkRight h) at bound
    change 3 ≤ (A ∩ wireOpenRail p h).card +
      (endpointWorkDelta l p target (wireWorkLeft h) + endpointWorkDelta l p target (wireWorkRight h))
    omega
  have sum : ∑ h ∈ K, ((A ∩ wireOpenRail p h).card + delta h) ≤ 3 * K.card := by
    rw [Finset.sum_add_distrib]
    omega
  have exactStock := three_of_sum_bound K (fun h => (A ∩ wireOpenRail p h).card + delta h) lower sum g hmem
  exact ⟨terminal g hmem, by simpa only [delta, Nat.add_assoc] using exactStock⟩

/-- The genuine accepted work-row quota forces every ordinary WIRE's terminal inventory to be exactly three holes. -/
theorem canonical_wire_terminal_holes {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    (PushS.holes t ∩ wireOpenRail p g).card = 3 :=
  (wire_inventory_account l p hl hM haxes initial target hgate hg hw hr ha).1

/-- Each actual WIRE's final work-row stock plus its two emitted r-cell payments is exactly three. -/
theorem canonical_wire_work_stock_exact {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    (roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 23 ∩ wireOpenRail p g).card +
      endpointWorkDelta l p target (wireWorkLeft g) + endpointWorkDelta l p target (wireWorkRight g) = 3 :=
  (wire_inventory_account l p hl hM haxes initial target hgate hg hw hr ha).2

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
