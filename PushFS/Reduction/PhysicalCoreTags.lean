/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalCertificate
public import PushFS.Reduction.PhysicalGateReadout
public import PushFS.Reduction.FullGateStatics.CoreAuxiliaryNames

/-! Exact actual core rail, junction and sink names on the complete physical source board. -/

@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory

open Cslib.Complexity.NCL Plan PhysicalBitmap Gadgets
open GateTileRouting.FullGateStatics
set_option maxHeartbeats 100000
set_option maxRecDepth 65536
attribute [local irreducible] Raster.width Raster.height StorageAtlas.initial StorageAtlas.board

private theorem core_name_of_local (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (g : VertexData) (hg : g∈vertexRecords v.1) (p : Gates.C) (t : AxisTrack)
    (ht : (classifier (gateTileState (g,v.2))).name
      ((chart (gateTileState (g,v.2)) (.inl (.inl 0))).embedding.cells p)=
      AxisTrack.shift (chart (gateTileState (g,v.2)) (.inl (.inl 0))).dx
        (chart (gateTileState (g,v.2)) (.inl (.inl 0))).dy t)
    (hs : t.Supports p) (ha : t≠.outside) :
    (axisTracks v hP hT).name ((coreEmbedding v g hg).cells p)=
      AxisTrack.shift (coreOffset g).1 (coreOffset g).2 t := by
  let G:=gateTileState (g,v.2)
  let i:=gateIndex v g hg
  let q:=(chart G (.inl (.inl 0))).embedding.cells p
  have hlocal : (PhysicalTiles.classifier (tile i)).name q≠.outside := by
    intro he
    have hh:=he.symm.trans ht
    apply ha
    exact AxisTrack.shift_injective _ _ hh.symm
  have hn:=inner_name v hP hT i q (full_core_inner G p) hlocal
  change (axisTracks v hP hT).name ((coreEmbedding v g hg).cells p)=
    AxisTrack.shift (axisChart v i).dx (axisChart v i).dy ((classifier G).name q) at hn
  have hl:=congrArg AxisTrack.level hn
  rw [AxisTrack.level_shift,ht,AxisTrack.level_shift] at hl
  have hs' := AxisTrack.shift_supported (coreOffset g).1 (coreOffset g).2
    (core_fits v g hg).1 (core_fits v g hg).2 hs
  have hsGlobal : (AxisTrack.shift (coreOffset g).1 (coreOffset g).2 t).Supports
      ((coreEmbedding v g hg).cells p) := (core_cells v g hg p).symm ▸hs'
  apply supported_level_injective _ ((axisTracks v hP hT).supported _) hsGlobal
  exact hl.trans (AxisTrack.level_shift _ _ t).symm

theorem coreTags (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (g : VertexData) (hg : g∈vertexRecords v.1) : CoreTags v hP hT (axisTracks v hP hT) g hg := by
  let G:=gateTileState (g,v.2)
  constructor
  · intro l
    let b:=gateSignals (g.ports,v.2.1)
    let p:=Gates.position g.ports.isAND b l
    apply core_name_of_local v hP hT g hg p (Gates.axisName g.ports.isAND p)
    · exact core_slot_name G b l
    · exact (Gates.classifier g.ports.isAND ∅).supported p
    · exact Gates.slot_position_active _ _ (List.getElem_mem l.isLt) b
  · exact core_name_of_local v hP hT g hg _ (.horizontal 90) (core_junction_name G)
      (by cases g.ports.isAND <;> rfl) (by intro he; cases he)
  · intro hk
    exact core_name_of_local v hP hT g hg (39,90) (.sink 39 90) (core_protected_name G hk)
      ⟨rfl,rfl⟩ (by intro he; cases he)

end PushPuzzle.PushFS.Reduction.PhysicalInventory
