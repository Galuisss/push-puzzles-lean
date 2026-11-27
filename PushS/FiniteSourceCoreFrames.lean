/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceCoreActiveActors
public import PushS.FiniteFramePlacement

/-! Place any selected core frame using the actual globally clear region and whole remaining inventory. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory.CoreSite

open PushFS PushFS.Reduction FiniteRouting FiniteGeometry FiniteGateActiveRegion
open Cslib.Complexity.NCL
open scoped Classical

attribute [local irreducible] codes width height FiniteGeometry.side

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (c : CoreSite w hw v)

/-- The complete AND selector is exactly the actual emitted core-owner identity set. -/
theorem andLabels_piece (hg : c.gate.core.isAND = true) :
    Finset.univ.map (c.andLabels hg) = (inventory w hw v).pieceLabels c.index := by
  apply Finset.Subset.antisymm
  · intro l hl
    obtain ⟨q,_,rfl⟩ := Finset.mem_map.mp hl
    exact (inventory w hw v).mem_pieceLabels c.index _ |>.mpr (c.andLabels_owner hg q)
  · exact c.andLabels_cover hg

/-- The complete OR selector is exactly the actual emitted core-owner identity set. -/
theorem orLabels_piece (hg : c.gate.core.isAND = false) :
    Finset.univ.map (c.orLabels hg) = (inventory w hw v).pieceLabels c.index := by
  apply Finset.Subset.antisymm
  · intro l hl
    obtain ⟨q,_,rfl⟩ := Finset.mem_map.mp hl
    exact (inventory w hw v).mem_pieceLabels c.index _ |>.mpr (c.orLabels_owner hg q)
  · exact c.orLabels_cover hg

/-- A real local selected footprint becomes its actual whole-board frame, including all shared and foreign boxes. -/
theorem region_frame {n m : ℕ} (selected : Fin 3) (p : PathSite w hw v (armSpec w c.gate selected))
    (hloc : p.location = ((codes w v).get c.index).1) (ha : (inventory w hw v).Admissible)
    (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (hb : (armSpec w c.gate selected).target = !(armSpec w c.gate selected).initial)
    (active : Finset (Cell n m)) (a : GridEmbedding n m (FiniteGeometry.side w) (FiniteGeometry.side w))
    (A : Board (FiniteGeometry.side w) (FiniteGeometry.side w)) (fixed : Finset (Cell (FiniteGeometry.side w) (FiniteGeometry.side w)))
    (hA : A.walls = FiniteCoreGuardCoverage.walls w c.gate.core.isAND)
    (F : FiniteWireFrame.Frame active a A fixed)
    (hactive : ∀ q ∈ active,Region w c.gate.core.isAND selected (a.cells q))
    (hfixed : ∀ q ∈ fixed,Envelope w c.gate.core.isAND (coordinates q))
    (B : Board (width w v) (height w v)) (hB : B.walls = (inventory w hw v).walls) :
    FiniteWireFrame.Frame active (a.trans c.embedding) B
      (fixed.map c.embedding.cells ∪ c.remaining (c.corePhase selected p (tilePhases phase))) := by
  apply F.place c.embedding
  · intro q hq
    rw [hB]
    exact c.envelope_floor _ (hactive q hq).1 (by simpa only [hA] using F.floor q hq)
  · intro q hq
    rw [hB]
    apply c.envelope_floor q (hfixed q hq)
    rw [←hA]
    exact fun hm => Finset.disjoint_left.mp F.fixed_floor hq hm
  · rw [hB]
    exact PrimitiveProfile.outside_floor ha _ _
  · intro q hq
    exact c.remaining_avoids_region selected p hloc ha phase fresh hb (a.cells q) (hactive q hq)

end PushPuzzle.PushS.FiniteSourceInventory.CoreSite
