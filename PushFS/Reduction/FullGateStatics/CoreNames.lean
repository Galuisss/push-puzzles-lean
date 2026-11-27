/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateStatics.CoreLevelsChecked

/-! Literal central gate slot names are preserved by the actual complete-gate classifier. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics

open Inventory Gadgets
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

private theorem coreLevels_all (g : GateTileState) : coreLevelsTest g=true := by
  have hh:=coreLevels_checked (geometry g)
  exact hh

theorem coreLevel_position (g : GateTileState) (s : Gates.Slot) (hs : s∈Gates.slots g.core.isAND) (b : Gates.Signals) :
    coreLevelTest g (s.position b)=true := by
  have hh:=List.all_eq_true.mp (coreLevels_all g) s hs
  simp only [Bool.and_eq_true] at hh
  unfold Gates.Slot.position
  split
  · exact hh.2
  · exact hh.1

private theorem core_dominant (g : GateTileState) (p : Gates.C) (hp : coreLevelTest g p=true)
    (c : ChartIndex g) (q : Cell (chart g c).width (chart g c).height)
    (he : (chart g c).embedding.cells q=(chart g (.inl (.inl 0))).embedding.cells p) :
    ((chart g c).classifier.name q).level≤(Gates.axisName g.core.isAND p).level := by
  have ht:=List.all_eq_true.mp hp c (mem_chartIndices g c)
  let s:=shape (chart g c)
  let u:=(shape (chart g (.inl (.inl 0)))).global (p.1.val,p.2.val)
  have hx:=congrArg (fun r : C=>r.1.val) he
  have hy:=congrArg (fun r : C=>r.2.val) he
  change (chart g c).dx+q.1.val=(chart g (.inl (.inl 0))).dx+p.1.val at hx
  change (chart g c).dy+q.2.val=(chart g (.inl (.inl 0))).dy+p.2.val at hy
  have hu:s.Contains u := by
    have hqx:=q.1.isLt
    have hqy:=q.2.isLt
    dsimp only [s,u,Shape.Contains,Shape.global,shape]
    omega
  change (if s.Contains u then decide ((s.name (s.local u)).level≤(Gates.axisName g.core.isAND p).level) else true)=true at ht
  rw [ite_eq_left hu] at ht
  have hh:=of_decide_eq_true ht
  have hlocal:s.local u=(q.1.val,q.2.val) := by
    dsimp only [s,u,Shape.local,Shape.global,shape]
    apply Prod.ext <;> dsimp only <;> omega
  rw [hlocal] at hh
  change ((shape (chart g c)).name (q.1.val,q.2.val)).level≤_ at hh
  rw [shape_name] at hh
  exact hh

theorem core_name (g : GateTileState) (p : Gates.C) (ha : Gates.axisName g.core.isAND p≠.outside)
    (hp : coreLevelTest g p=true) :
    (classifier g).name ((chart g (.inl (.inl 0))).embedding.cells p)=
      AxisTrack.shift (chart g (.inl (.inl 0))).dx (chart g (.inl (.inl 0))).dy (Gates.axisName g.core.isAND p) := by
  let P:=(chart g (.inl (.inl 0))).embedding.cells p
  let T:=AxisTrack.shift (chart g (.inl (.inl 0))).dx (chart g (.inl (.inl 0))).dy (Gates.axisName g.core.isAND p)
  have hr:(mosaic g).Represents P T:=⟨.inl (.inl 0),p,rfl,rfl⟩
  have hactive:(mosaic g).name P≠.outside:=(mosaic g).source_active (.inl (.inl 0)) p ha
  obtain ⟨c,q,he,hn⟩:=(mosaic g).attained P hactive
  have hle:=core_dominant g p hp c q he
  have hlo:=(mosaic g).represented_le hr
  have hlevel:((mosaic g).name P).level=T.level := by
    have hh:=congrArg AxisTrack.level hn
    rw [AxisTrack.level_shift] at hh
    change ((chart g c).classifier.name q).level=((mosaic g).name P).level at hh
    dsimp only [T] at hlo ⊢
    rw [AxisTrack.level_shift] at hlo ⊢
    omega
  exact supported_level_injective P ((mosaic g).supported P) ((mosaic g).represented_supported hr) hlevel

end PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics
