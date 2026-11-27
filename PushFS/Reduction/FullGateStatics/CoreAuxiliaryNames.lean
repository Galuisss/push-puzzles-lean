/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateStatics.CoreNames
public import PushFS.Gadgets.Gates.Soundness.Ambient

/-! Actual complete-gate names of every central physical slot, junction and protected sink. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics

open Inventory Gadgets
set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem auxiliary_checked : ∀k : Geometry,
    coreLevelTest (ofGeometry k) (Gates.Soundness.junctionPoint k.1)=true ∧
      (k.1=true→coreLevelTest (ofGeometry k) ((39,90):Gates.C)=true) := by
  rintro ⟨kind,pattern,rotation,incoming⟩
  cases kind <;> fin_cases pattern <;> fin_cases rotation
  all_goals revert incoming; decide +kernel

theorem core_slot_name (g : GateTileState) (b : Gates.Signals) (l : Fin (Gates.slots g.core.isAND).length) :
    (classifier g).name ((chart g (.inl (.inl 0))).embedding.cells (Gates.position g.core.isAND b l))=
      AxisTrack.shift (chart g (.inl (.inl 0))).dx (chart g (.inl (.inl 0))).dy
        (Gates.axisName g.core.isAND (Gates.position g.core.isAND b l)) := by
  exact core_name g _ (Gates.slot_position_active g.core.isAND _ (List.get_mem _ l) b)
    (coreLevel_position g _ (List.get_mem _ l) b)

theorem core_junction_name (g : GateTileState) :
    (classifier g).name ((chart g (.inl (.inl 0))).embedding.cells (Gates.Soundness.junctionPoint g.core.isAND))=
      .horizontal ((chart g (.inl (.inl 0))).dy+90) := by
  have hlevel : coreLevelTest g (Gates.Soundness.junctionPoint g.core.isAND)=true :=
    (auxiliary_checked (geometry g)).1
  have hn : Gates.axisName g.core.isAND (Gates.Soundness.junctionPoint g.core.isAND)=.horizontal 90 := by
    cases g.core.isAND <;> rfl
  have hh:=core_name g _ (by rw [hn]; intro he; cases he) hlevel
  rw [hn] at hh
  exact hh

theorem core_protected_name (g : GateTileState) (hk : g.core.isAND=true) :
    (classifier g).name ((chart g (.inl (.inl 0))).embedding.cells ((39,90):Gates.C))=
      .sink ((chart g (.inl (.inl 0))).dx+39) ((chart g (.inl (.inl 0))).dy+90) := by
  have hlevel : coreLevelTest g ((39,90):Gates.C)=true :=(auxiliary_checked (geometry g)).2 hk
  have hn : Gates.axisName g.core.isAND ((39,90):Gates.C)=.sink 39 90 := by rw [hk]; rfl
  have hh:=core_name g _ (by rw [hn]; intro he; cases he) hlevel
  rw [hn] at hh
  exact hh

end PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics
