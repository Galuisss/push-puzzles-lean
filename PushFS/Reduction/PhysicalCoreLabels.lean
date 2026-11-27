/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalRawLabels
public import PushFS.Gadgets.Gates.Triggers

/-! Every genuine long-wall gate box has its own physical identity and literal whole-board position. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory


open Cslib.Complexity.NCL Plan PhysicalBitmap Gadgets
set_option maxRecDepth 65536
attribute [local irreducible] Raster.width Raster.height

noncomputable def coreLabel (v : CellPlan.Source) (g : VertexData) (hg : g∈vertexRecords v.1)
    (l : Fin (Gates.slots g.ports.isAND).length) : RawLabel v :=
  gateLabel v g hg ⟨.inl 0,l⟩

noncomputable def coreLabels (v : CellPlan.Source) (g : VertexData) (hg : g∈vertexRecords v.1) :
    Fin (Gates.slots g.ports.isAND).length↪RawLabel v where
  toFun := coreLabel v g hg
  inj' := by
    intro l k he
    change (⟨gateIndex v g hg,GateTileRouting.rawLabelEquiv (gateTileState (g,v.2)) ⟨.inl 0,l⟩⟩ : RawLabel v)=
      ⟨gateIndex v g hg,GateTileRouting.rawLabelEquiv (gateTileState (g,v.2)) ⟨.inl 0,k⟩⟩ at he
    have hh := (GateTileRouting.rawLabelEquiv (gateTileState (g,v.2))).injective (eq_of_heq (Sigma.mk.inj he).2)
    exact eq_of_heq (Sigma.mk.inj hh).2

noncomputable def coreEmbedding (v : CellPlan.Source) (g : VertexData) (hg : g∈vertexRecords v.1) :
    GridEmbedding 81 107 (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7) :=
  gatePrimitiveEmbedding v g hg (.inl 0)

theorem coreLabel_source (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (g : VertexData) (hg : g∈vertexRecords v.1) (l : Fin (Gates.slots g.ports.isAND).length) :
    (rawSlotMatching v hP hT).source (coreLabel v g hg l)=
      (coreEmbedding v g hg).cells (Gates.position g.ports.isAND (gateSignals (g.ports,v.2.1)) l) :=
  gateLabel_source v hP hT g hg (.inl 0) l

theorem coreLabel_target (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (g : VertexData) (hg : g∈vertexRecords v.1) (l : Fin (Gates.slots g.ports.isAND).length) :
    (rawSlotMatching v hP hT).target (coreLabel v g hg l)=
      (coreEmbedding v g hg).cells (Gates.position g.ports.isAND (gateSignals (g.ports,v.2.2)) l) :=
  gateLabel_target v hP hT g hg (.inl 0) l

theorem core_walls_agree (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (g : VertexData) (hg : g∈vertexRecords v.1) :
    (coreEmbedding v g hg).WallsAgree (Gates.board g.ports.isAND ∅) (atlas v hP hT).board :=
  gate_primitive_walls v hP hT g hg (.inl 0)

def coreOffset (g : VertexData) : ℕ×ℕ :=
  (strideX*(refinePoint g.point).1+(GateAnnulus.coreOffset g.ports.isAND).1+3,
    strideY*(refinePoint g.point).2+(GateAnnulus.coreOffset g.ports.isAND).2+3)

/-- The genuine unrotated 81×107 core uses these same literal translated coordinates. -/
theorem core_coordinates (v : CellPlan.Source) (g : VertexData) (hg : g∈vertexRecords v.1) (p : Gates.C) :
    (((coreEmbedding v g hg).cells p).1.val,((coreEmbedding v g hg).cells p).2.val)=
      ((coreOffset g).1+p.1.val,(coreOffset g).2+p.2.val) := by
  have hx : (GateTileRouting.bufferOffset g.ports.isAND).1+2311=(GateAnnulus.coreOffset g.ports.isAND).1+3 := by
    cases g.ports.isAND <;> decide +kernel
  have hy : (GateTileRouting.bufferOffset g.ports.isAND).2+2321=(GateAnnulus.coreOffset g.ports.isAND).2+3 := by
    cases g.ports.isAND <;> decide +kernel
  change (strideX*(refinePoint g.point).1+((GateTileRouting.bufferOffset g.ports.isAND).1+2311+p.1.val),
    strideY*(refinePoint g.point).2+((GateTileRouting.bufferOffset g.ports.isAND).2+2321+p.2.val))=_
  dsimp only [coreOffset]
  rw [hx,hy]
  simp only [Nat.add_assoc]


theorem coreLabel_owner (v : CellPlan.Source) (g h : VertexData) (hg : g∈vertexRecords v.1)
    (hh : h∈vertexRecords v.1) (l : Fin (Gates.slots g.ports.isAND).length)
    (k : Fin (Gates.slots h.ports.isAND).length) (he : coreLabel v g hg l=coreLabel v h hh k) : g=h := by
  apply gateIndex_injective v hg hh
  exact congrArg Sigma.fst he

/-- The genuine three internal threshold boxes, retaining their physical slot identities. -/
def triggerIndex (kind : Bool) (role : Fin 3) : Fin (Gates.slots kind).length :=
  if role=0 then Gates.triggerA kind else if role=1 then Gates.triggerB kind else Gates.triggerC kind

theorem triggerIndex_injective : ∀kind : Bool,Function.Injective (triggerIndex kind) := by
  decide +kernel

abbrev GatePort (v : CellPlan.Source) := {g : VertexData //g∈vertexRecords v.1}×Fin 3

/-- Distinct actual source-gate roles use distinct physical boxes in the full board. -/
noncomputable def gateTriggers (v : CellPlan.Source) : GatePort v↪RawLabel v where
  toFun p := coreLabel v p.1.val p.1.property (triggerIndex p.1.val.ports.isAND p.2)
  inj' := by
    rintro ⟨⟨g,hg⟩,r⟩ ⟨⟨h,hh⟩,s⟩ he
    have hgh := coreLabel_owner v g h hg hh _ _ he
    subst h
    have hr := triggerIndex_injective g.ports.isAND ((coreLabels v g hg).injective he)
    change r=s at hr
    subst s
    rfl

end PushPuzzle.PushFS.Reduction.PhysicalInventory
