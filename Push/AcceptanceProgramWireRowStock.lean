/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramProbeStock
public import PushS.PortWireRail
import all Push.AcceptanceProgramLayout
import all PushS.PortSegments

/-! Exact canonical WIRE inventories at the actual R23 work-row boundary. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushFS.Reduction PushS PushS.PortLayout SegmentRecipe

/-- The literal prefix before the remaining working rows are read. -/
@[expose] def wireWorkPrefix (l : PortLayout) (p : Scales.Parameters) (target : List Bool) : List Template :=
  (schedule l p (targetHoles l p target \ Boundary.frame).card).take 23

/-- The actual target bitmap presented to the complete working-row read. -/
@[expose] def wireWorkReference (l : PortLayout) (p : Scales.Parameters) (target : List Bool) :
    Finset (Cell (p.W + 1) (p.H + 1)) :=
  (emit (wireWorkPrefix l p target) (targetHoles l p target)).remaining

/-- The original three-hole canonical WIRE stock already consumed by this literal prefix. -/
@[expose] def wireWorkPaid (l : PortLayout) (p : Scales.Parameters) (target : List Bool) (g : Placement) :
    Finset (Cell (p.W + 1) (p.H + 1)) :=
  (targetHoles l p target ∩ wireOpenRail p g) ∩ allRegions (wireWorkPrefix l p target)

/-- The canonical interior inventory, and hence every literal prefix mask, is independent of the target word. -/
theorem canonical_interior_card_eq (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (target : List Bool) :
    (targetHoles l p target \ Boundary.frame).card = (targetHoles l p [] \ Boundary.frame).card := by
  have htotal := l.encodedSegments_holes_card_eq p hl hM haxes (l.canonical target) (l.canonical [])
  have ht := Finset.card_sdiff_add_card_eq_card (l.encodedSegments_frame_subset p (l.canonical target))
  have hz := Finset.card_sdiff_add_card_eq_card (l.encodedSegments_frame_subset p (l.canonical []))
  change (targetHoles l p target).card = (targetHoles l p []).card at htotal
  change (targetHoles l p target \ Boundary.frame).card + Boundary.frame.card = (targetHoles l p target).card at ht
  change (targetHoles l p [] \ Boundary.frame).card + Boundary.frame.card = (targetHoles l p []).card at hz
  omega

/-- R23 uses one fixed geometric prefix for every canonical target word. -/
theorem wireWorkPrefix_eq (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (target : List Bool) :
    wireWorkPrefix l p target = wireWorkPrefix l p [] := by
  unfold wireWorkPrefix
  rw [canonical_interior_card_eq l p hl hM haxes target]

/-- Each actual ordinary WIRE has exactly its three canonical holes split between the R23 stock and earlier payments. -/
theorem wireWork_rail_card (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (target : List Bool)
    {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none) :
    (wireWorkReference l p target ∩ wireOpenRail p g).card + (wireWorkPaid l p target g).card = 3 := by
  have hpartition := Finset.card_sdiff_add_card_inter
    (targetHoles l p target ∩ wireOpenRail p g) (allRegions (wireWorkPrefix l p target))
  have he : wireWorkReference l p target ∩ wireOpenRail p g =
      (targetHoles l p target ∩ wireOpenRail p g) \ allRegions (wireWorkPrefix l p target) := by
    ext q
    simp only [wireWorkReference, emit_remaining, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  rw [he]
  exact hpartition.trans (l.encodedSegments_wireOpenRail_card p hl hM haxes (l.canonical target) hg hw)

end PushPuzzle.Push.AcceptanceProgram
