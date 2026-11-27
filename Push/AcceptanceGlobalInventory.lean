/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSignalInventory
public import Push.AcceptanceSignalRegionsDisjoint
public import Push.AcceptanceInventoryPartition
public import Push.AcceptancePhysicalDynamics

/-! The actual conserved total hole inventory closes all gate rails after the principal axes balance. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram AcceptanceSignalRegions

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate

/-- True principal-axis balance and conservation of the complete board saturate each actual signal account. -/
theorem canonical_signal_family_exact {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (I).board none (I).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (inventory : AxisInventories l p t) (i : Option (RegionIndex l)) :
    (family l p (holes t) i).card = (family l p (holes (I).initial) i).card := by
  classical
  let start : State (p.W + 1) (p.H + 1) := (I).initial
  have cover : holes start ⊆ Finset.univ.biUnion (family l p (holes start)) := by
    have source : holes start = fixedHoles l p ∪
        Finset.univ.biUnion (fun j : RegionIndex l => holes start ∩ region l p j) :=
      initial_holes_cover l p hl hM haxes initial target
    intro q hq
    rw [source] at hq
    rcases Finset.mem_union.mp hq with fixed | signal
    · exact Finset.mem_biUnion.mpr ⟨none, Finset.mem_univ _, fixed⟩
    · obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp signal
      exact Finset.mem_biUnion.mpr ⟨some j, Finset.mem_univ _, hj⟩
  have contained : ∀ j, family l p (holes t) j ⊆ holes t := by
    intro j
    cases j with
    | none => exact canonical_allfixed_holes_empty l p hl hM haxes initial target hgate hr .refl accepted
    | some j => exact Finset.inter_subset_left
  have monotone := canonical_signal_family_lower l p hl hM haxes initial target hgate hr accepted inventory
  exact AcceptanceInventory.partition_card_eq (holes start) (holes t)
    (family l p (holes start)) (family l p (holes t)) cover contained
    (canonical_family_pairwise l p hl hM haxes initial target hgate hr accepted) monotone
    (card_holes_reachable hr).symm i

/-- Each actual gate rail has precisely its original kappa-plus-eleven holes once the axes balance. -/
theorem canonical_gateRail_holes_of_axes {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (I).board none (I).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (inventory : AxisInventories l p t) : (holes t ∩ gateOpenRail p g).card = kind.kappa.toNat + 11 := by
  classical
  have same := canonical_signal_family_exact l p hl hM haxes initial target hgate hr accepted inventory
    (some (.inr ⟨g, List.mem_toFinset.mpr hg⟩))
  simp only [family, region, railRegion, hk] at same
  have initialCount : ((holes (I).initial : Finset (Cell (p.W + 1) (p.H + 1))) ∩ gateOpenRail p g).card = kind.kappa.toNat + 11 :=
    l.physicalInstance_gateOpenRail_initial_holes p hl hM haxes (l.canonical initial) (l.canonical target) hg hk
  exact same.trans initialCount

/-- The complete actual gate-rail inventory certificate follows from the same balanced principal axes. -/
theorem canonical_gateRail_inventories_of_axes {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (I).board none (I).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (inventory : AxisInventories l p t) : GateRailInventories l p t := by
  constructor
  intro g hg kind hk
  exact canonical_gateRail_holes_of_axes l p hl hM haxes initial target hgate hg hk hr accepted inventory

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
