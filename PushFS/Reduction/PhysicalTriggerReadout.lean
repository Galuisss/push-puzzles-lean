/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalSourceIncidences
public import PushFS.Reduction.FullGateRawCanonical

/-! Actual whole-board internal trigger thresholds recover the original finite NCL orientations. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory


open Cslib.Complexity.NCL PushPuzzle.NCL Plan PhysicalBitmap Gadgets
set_option maxRecDepth 65536
attribute [local irreducible] Raster.width Raster.height

def thresholdAt (kind : Bool) (offset : ℕ×ℕ) (role : Fin 3) (p : ℕ×ℕ) : Bool :=
  if role=0 then
    if kind then decide (p.1<offset.1+43) else decide (p.1+1<offset.1+44)
  else if role=1 then decide (p.2+1<offset.2+90)
  else !(decide (p.1≤offset.1+(if kind then 43 else 44)+3))

private theorem threshold_position (kind : Bool) (a : Gates.Signals) (role : Fin 3) (offset : ℕ×ℕ) :
    thresholdAt kind offset role
      (offset.1+(Gates.position kind a (triggerIndex kind role)).1.val,
        offset.2+(Gates.position kind a (triggerIndex kind role)).2.val)=gateClaim a role := by
  fin_cases role <;> cases kind <;> rcases a with ⟨a,b,c⟩ <;> cases a <;> cases b <;> cases c <;>
    simp [thresholdAt,triggerIndex,Gates.position_triggerA,Gates.position_triggerB,Gates.position_triggerC,
      gateClaim,Gates.Signals.get,Nat.add_assoc]

def gateThreshold {W H : ℕ} (g : VertexData) (role : Fin 3) (p : Cell W H) : Bool :=
  thresholdAt g.ports.isAND (coreOffset g) role (p.1.val,p.2.val)

/-- The literal source threshold of every true physical trigger reads its own source incidence. -/
private theorem gateTrigger_source (v : CellPlan.Source) (hP : v.1.checkPlane=true)
    (hT : v.1.WellTyped [] [])
    (g : VertexData) (hg : g∈vertexRecords v.1) (r : Fin 3) :
    gateThreshold g r ((rawSlotMatching v hP hT).source (coreLabel v g hg (triggerIndex g.ports.isAND r)))=
      decide ((g.ports.port r).In (fun e=>v.2.1.getD e false)) := by
  rw [coreLabel_source]
  unfold gateThreshold
  rw [core_coordinates,threshold_position]
  exact gateSignals_claim g.ports v.2.1 r

/-- The prescribed physical target identity reads precisely its original target orientation. -/
private theorem gateTrigger_target (v : CellPlan.Source) (hP : v.1.checkPlane=true)
    (hT : v.1.WellTyped [] [])
    (g : VertexData) (hg : g∈vertexRecords v.1) (r : Fin 3) :
    gateThreshold g r ((rawSlotMatching v hP hT).target (coreLabel v g hg (triggerIndex g.ports.isAND r)))=
      decide ((g.ports.port r).In (fun e=>v.2.2.getD e false)) := by
  rw [coreLabel_target]
  unfold gateThreshold
  rw [core_coordinates,threshold_position]
  exact gateSignals_claim g.ports v.2.2 r

noncomputable def sourceReadout (v : CellPlan.Source) (hw : (Word.compile v.1).Valid)
    (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] []) (hG : (Word.compile v.1).graph.WellFormed) :
    TriggerReadout (Fin (Word.compile v.1).edgeCount) (RawLabel v)
      (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7) :=
  TriggerReadout.ofIncidences hG (sourceTriggers v hw hP hT hG)
    (fun i=>gateThreshold (sourceRecord v.1 hP hT i.1) (sourceRole v.1 hw hP hT i))

/-- The actual initial labelled state decodes to the exact upstream finite source configuration. -/
theorem sourceReadout_initial (v : CellPlan.Source) (hw : (Word.compile v.1).Valid)
    (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] []) (hG : (Word.compile v.1).graph.WellFormed) :
    (sourceReadout v hw hP hT hG).read (rawSlotMatching v hP hT).initialLabelled=
      PortClaims.full (fun e : Fin (Word.compile v.1).edgeCount=>v.2.1.getD e.val false) := by
  apply TriggerReadout.ofIncidences_full
  intro i
  change gateThreshold (sourceRecord v.1 hP hT i.1) (sourceRole v.1 hw hP hT i)
    ((rawSlotMatching v hP hT).source (coreLabel v (sourceRecord v.1 hP hT i.1)
      (sourceRecord_mem v.1 hP hT i.1) (triggerIndex (sourceRecord v.1 hP hT i.1).ports.isAND
        (sourceRole v.1 hw hP hT i))))=_
  rw [gateTrigger_source,sourceRole_port]
  rfl

/-- Recovered physical goal identities decode to the exact upstream finite target configuration. -/
theorem sourceReadout_target (v : CellPlan.Source) (hw : (Word.compile v.1).Valid)
    (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] []) (hG : (Word.compile v.1).graph.WellFormed)
    (S : LabelledState (RawLabel v) (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7))
    (hs : S.position=(rawSlotMatching v hP hT).target) :
    (sourceReadout v hw hP hT hG).read S=
      PortClaims.full (fun e : Fin (Word.compile v.1).edgeCount=>v.2.2.getD e.val false) := by
  apply TriggerReadout.ofIncidences_full
  intro i
  change gateThreshold (sourceRecord v.1 hP hT i.1) (sourceRole v.1 hw hP hT i)
    (S.position (coreLabel v (sourceRecord v.1 hP hT i.1)
      (sourceRecord_mem v.1 hP hT i.1) (triggerIndex (sourceRecord v.1 hP hT i.1).ports.isAND
        (sourceRole v.1 hw hP hT i))))=_
  rw [hs]
  exact (gateTrigger_target v hP hT (sourceRecord v.1 hP hT i.1)
    (sourceRecord_mem v.1 hP hT i.1) (sourceRole v.1 hw hP hT i)).trans (by
      rw [sourceRole_port]
      rfl)

end PushPuzzle.PushFS.Reduction.PhysicalInventory
