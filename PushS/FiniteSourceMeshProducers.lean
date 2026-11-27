/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceMeshShoulders

/-! Every actual used coarse-grid edge selects the complete producer program on one of its two sides. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting
open Cslib.Complexity.NCL

attribute [local irreducible] codes width height

private theorem meshFaceBase_neighbor (face : Direction) (p r : GridRouting.Point)
    (hn : PushFS.Reduction.neighbor face p = some r) : meshFaceBase face p = meshFaceBase face.opposite r := by
  have ht := neighbor_travels hn
  cases face <;> dsimp [meshFaceBase,Travels,Direction.opposite] at * <;> apply Prod.ext <;> omega

private theorem used_producer (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) (pos : GridRouting.Point) (face : Direction)
    (hu : CellPlan.Used (CellPlan.cell (v,pos)) face) :
    ∃ (s : LineSite w hw v) (out : Direction), (out = face ∨ out = face.opposite) ∧
      segmentDirection s.code.segment = out ∧ s.code.segment.finish = boundaryPoint w out ∧ s.code.last = true ∧
      meshFaceBase out ((codes w v).get s.index).1 = meshFaceBase face pos := by
  obtain ⟨incoming,hp⟩ := local_port_of_used v pos face hu
  cases incoming
  · obtain ⟨s,hs,hd,he,hl⟩ := producer_line_site w hw v pos face hp
    exact ⟨s,face,Or.inl rfl,hd,he,hl,by rw [hs]⟩
  · obtain ⟨r,hn,_⟩ := CellPlan.used_neighbor v hP hT pos face hu
    have hport := local_port_reciprocal v hP hT pos r face hn true hp
    simp only [Bool.not_true] at hport
    obtain ⟨s,hs,hd,he,hl⟩ := producer_line_site w hw v r face.opposite hport
    exact ⟨s,face.opposite,Or.inr rfl,hd,he,hl,by rw [hs]; exact (meshFaceBase_neighbor face pos r hn).symm⟩

theorem vertical_used_producer (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) (gx gy : ℕ)
    (hu : CellPlan.Used (CellPlan.cell (v,(gx,gy))) .west) :
    ∃ (s : LineSite w hw v) (out : Direction), (out = .west ∨ out = .east) ∧
      segmentDirection s.code.segment = out ∧ s.code.segment.finish = boundaryPoint w out ∧ s.code.last = true ∧
      meshFaceBase out ((codes w v).get s.index).1 = (gx,gy) := by
  obtain ⟨s,out,hout,hd,he,hl,hbase⟩ := used_producer w hw v hP hT (gx,gy) .west hu
  exact ⟨s,out,hout,hd,he,hl,hbase⟩

theorem horizontal_used_producer (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) (gx gy : ℕ)
    (hu : CellPlan.Used (CellPlan.cell (v,(gx,gy))) .north) :
    ∃ (s : LineSite w hw v) (out : Direction), (out = .north ∨ out = .south) ∧
      segmentDirection s.code.segment = out ∧ s.code.segment.finish = boundaryPoint w out ∧ s.code.last = true ∧
      meshFaceBase out ((codes w v).get s.index).1 = (gx,gy) := by
  obtain ⟨s,out,hout,hd,he,hl,hbase⟩ := used_producer w hw v hP hT (gx,gy) .north hu
  exact ⟨s,out,hout,hd,he,hl,hbase⟩

end PushPuzzle.PushS.FiniteSourceInventory
