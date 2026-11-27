/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramWireRowStockPartition

/-! Exact three-hole row budgets before the actual complete working-row read. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS PushS.PortLayout
open scoped BigOperators

/-- The literal target row pays three holes per ordinary WIRE, after accounting for its actual earlier payments and fixed background. -/
theorem wireWork_row_card (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (target : List Bool)
    (side : Side) {j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ p.levels)
    (hordinary : side = .upper ∨ 2 ≤ j) :
    ((wireWorkReference l p target).filter (fun q => q.2.val = wireWorkRow p side j)).card +
        ∑ g ∈ wireRowPlacements l side j, (wireWorkPaid l p target g).card =
      (wireRowFixedStock l p side j).card + 3 * (wireRowPlacements l side j).card := by
  classical
  have hsub : wireWorkReference l p target ⊆ targetHoles l p target := emit_remaining_subset _ _
  have hd : Disjoint (wireRowFixedStock l p side j)
      ((wireRowPlacements l side j).biUnion fun g => wireWorkReference l p target ∩ wireOpenRail p g) := by
    apply Finset.disjoint_left.mpr
    intro q hf hr
    obtain ⟨g, hg, hq⟩ := Finset.mem_biUnion.mp hr
    obtain ⟨hg, hw, _, _⟩ := Finset.mem_filter.mp hg
    exact Finset.disjoint_left.mp (wire_fixed_disjoint l p hl hM haxes target (List.mem_toFinset.mp hg) hw)
      (emit_remaining_subset _ _ (Finset.mem_filter.mp hf).1) (Finset.mem_inter.mp hq).2
  have hp : Set.PairwiseDisjoint (↑(wireRowPlacements l side j))
      (fun g => wireWorkReference l p target ∩ wireOpenRail p g) := by
    intro g hg h hh hne
    obtain ⟨hg, hgw, hgs, _⟩ := Finset.mem_filter.mp hg
    obtain ⟨hh, hhw, hhs, _⟩ := Finset.mem_filter.mp hh
    exact (wire_target_rails_disjoint l p hl hM haxes target (List.mem_toFinset.mp hg) hgw
      (List.mem_toFinset.mp hh) hhw (hgs.trans hhs.symm) hne).mono
        (fun q hq => Finset.mem_inter.mpr ⟨hsub (Finset.mem_inter.mp hq).1, (Finset.mem_inter.mp hq).2⟩)
        (fun q hq => Finset.mem_inter.mpr ⟨hsub (Finset.mem_inter.mp hq).1, (Finset.mem_inter.mp hq).2⟩)
  rw [wireWork_row_eq l p hl hM haxes target side hj hjm hordinary,
    Finset.card_union_of_disjoint hd, Finset.card_biUnion hp]
  calc
    _ = (wireRowFixedStock l p side j).card +
        ∑ g ∈ wireRowPlacements l side j,
          ((wireWorkReference l p target ∩ wireOpenRail p g).card + (wireWorkPaid l p target g).card) := by
      rw [Finset.sum_add_distrib]
      omega
    _ = (wireRowFixedStock l p side j).card + ∑ _g ∈ wireRowPlacements l side j, 3 := by
      congr 1
      apply Finset.sum_congr rfl
      intro g hg
      obtain ⟨hg, hw, _, _⟩ := Finset.mem_filter.mp hg
      exact wireWork_rail_card l p hl hM haxes target (List.mem_toFinset.mp hg) hw
    _ = _ := by simp [Nat.mul_comm]

end PushPuzzle.Push.AcceptanceProgram
