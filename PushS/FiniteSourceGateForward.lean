/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceArmInput
public import PushS.FiniteSourceGateCompletion

/-! Execute one real selected gate arm and core in their required order on the complete global inventory. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting FiniteGeometry FiniteGateSelected
open FiniteGateCanonicalAccess FiniteGateFaceBridge FiniteGateFaceGeometry
open Cslib.Complexity.NCL
open scoped Classical

attribute [local irreducible] codes width height inventory FiniteGeometry.side Line.width Line.height

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source}

namespace CoreSite

variable (c : CoreSite w hw v)

/-- Precisely one real selected core macro with actual endpoint inventory access. -/
inductive Action (phase : Fin (codes w v).length → Bool) (B : Board (width w v) (height w v)) : Prop
  | andStep (hg : c.gate.core.isAND = true)
    (S : AndStep w c.embedding B (PrimitiveProfile.outside w hw v phase (Finset.univ.map (c.andLabels hg)))
      c.gate.core.initial c.gate.core.target)
    (Ai : AndAccess w c.embedding B ((andBoxes w c.gate.core.initial.left c.gate.core.initial.upper
      c.gate.core.initial.right).map c.embedding.cells ∪
      PrimitiveProfile.outside w hw v phase (Finset.univ.map (c.andLabels hg))))
    (Af : AndAccess w c.embedding B ((andBoxes w c.gate.core.target.left c.gate.core.target.upper
      c.gate.core.target.right).map c.embedding.cells ∪
      PrimitiveProfile.outside w hw v phase (Finset.univ.map (c.andLabels hg)))) : Action phase B
  | orStep (hg : c.gate.core.isAND = false)
    (S : OrStep w c.embedding B (PrimitiveProfile.outside w hw v phase (Finset.univ.map (c.orLabels hg)))
      c.gate.core.initial c.gate.core.target)
    (Ai : Access w false c.embedding B ((orBoxes w c.gate.core.initial.left c.gate.core.initial.upper
      c.gate.core.initial.right).map c.embedding.cells ∪
      PrimitiveProfile.outside w hw v phase (Finset.univ.map (c.orLabels hg))))
    (Af : Access w false c.embedding B ((orBoxes w c.gate.core.target.left c.gate.core.target.upper
      c.gate.core.target.right).map c.embedding.cells ∪
      PrimitiveProfile.outside w hw v phase (Finset.univ.map (c.orLabels hg)))) : Action phase B

/-- The canonical real dock of this actual AND or OR core. -/
@[expose] def dockCell : Cell (width w v) (height w v) :=
  c.embedding.cells (dock w c.gate.core.isAND true)

/-- The selected real branch changes exactly the actual core's complete global stock. -/
private theorem Action.run {phase : Fin (codes w v).length → Bool} {B : Board (width w v) (height w v)}
    (S : c.Action phase B) (fresh : phase c.index = false) :
    Reachable B (some 1) (PrimitiveProfile.state w hw v phase c.dockCell)
      (PrimitiveProfile.state w hw v (Function.update phase c.index true) c.dockCell) := by
  cases S with
  | andStep hg S Ai Af => simpa only [dockCell,hg] using c.and_run hg phase fresh B S Ai Af
  | orStep hg S Ai Af => simpa only [dockCell,hg] using c.or_run hg phase fresh B S Ai Af

/-- Actual same-stock walks connect the global anchor to the core dock before and after its real macro. -/
structure AnchorAccess (phase : Fin (codes w v).length → Bool)
    (B : Board (width w v) (height w v)) (anchor : Cell (width w v) (height w v)) : Prop where
  enter : Reachable B (some 1) (PrimitiveProfile.state w hw v phase anchor)
    (PrimitiveProfile.state w hw v phase c.dockCell)
  leave : Reachable B (some 1) (PrimitiveProfile.state w hw v (Function.update phase c.index true) c.dockCell)
    (PrimitiveProfile.state w hw v (Function.update phase c.index true) anchor)

/-- The real selected core execution starts and ends at the same actual global anchor. -/
private theorem Action.at_anchor {phase : Fin (codes w v).length → Bool} {B : Board (width w v) (height w v)}
    (S : c.Action phase B) (fresh : phase c.index = false)
    {anchor : Cell (width w v) (height w v)} (W : c.AnchorAccess phase B anchor) :
    Reachable B (some 1) (PrimitiveProfile.state w hw v phase anchor)
      (PrimitiveProfile.state w hw v (Function.update phase c.index true) anchor) :=
  W.enter.trans ((S.run c fresh).trans W.leave)

/-- A rising inward claim changes the arm before its core; a falling claim changes the core first. -/
@[expose] noncomputable def corePhase (role : Fin 3) (p : PathSite w hw v (armSpec w c.gate role))
    (base : Fin (codes w v).length → Bool) : Fin (codes w v).length → Bool :=
  if (armSpec w c.gate role).initial then base else p.wave base (PathSite.waveLength (P := armSpec w c.gate role))

/-- The actual core is untouched when its selected macro is reached in either propagation direction. -/
private theorem corePhase_fresh (role : Fin 3) (p : PathSite w hw v (armSpec w c.gate role))
    (base : Fin (codes w v).length → Bool) (fresh : base c.index = false) :
    c.corePhase role p base c.index = false := by
  unfold corePhase
  split_ifs
  · exact fresh
  · rw [p.wave_outside _ _ _ (c.arm_event_ne_core role p)]
    exact fresh

/-- The complete real gate execution updates exactly its actual source tile, including every selected arm auxiliary. -/
theorem gate_tile_forward (role : Fin 3) (p : PathSite w hw v (armSpec w c.gate role))
    (hloc : p.location = ((codes w v).get c.index).1) (ha : (inventory w hw v).Admissible)
    (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (idle : ∀ i : Fin (codes w v).length,((codes w v).get i).1 = p.location → i ≠ c.index →
      ((codes w v).get i).2 ∉ (armSpec w c.gate role).codes → (((codes w v).get i).2).SamePhase)
    (I : ArmInput c role p)
    (outside : ∀ h,phase ((codes w v).get (I.endpoints.final h).1).1 = !(armSpec w c.gate role).initial)
    (hb : (armSpec w c.gate role).target = !(armSpec w c.gate role).initial)
    (B : Board (width w v) (height w v))
    (S : c.Action (c.corePhase role p (tilePhases phase)) B)
    (C : c.AnchorAccess (c.corePhase role p (tilePhases phase)) B (inventory w hw v).player)
    (F : ∀ cut,cut < PathSite.waveLength (P := armSpec w c.gate role) → ∀ a : PathEvent (armSpec w c.gate role),
      a.rank = PathSite.waveRank (P := armSpec w c.gate role) cut →
      p.EventFrame (armSpec_geometry w c.gate role) I.endpoints B (p.wave (c.preparedArmBase role (tilePhases phase)) cut) a)
    (W : p.WaveAccess (armSpec_geometry w c.gate role) (c.preparedArmBase role (tilePhases phase)) B (inventory w hw v).player) :
    Reachable B (some 1) (profileState w hw v phase)
      (profileState w hw v (Function.update phase p.location true)) := by
  have hf : tilePhases phase c.index = false := by unfold tilePhases; rw [←hloc]; exact fresh
  have hc := S.at_anchor c (c.corePhase_fresh role p _ hf) C
  have hp := p.path_forward (armSpec_geometry w c.gate role) ha I.endpoints
    (c.preparedArmBase role (tilePhases phase)) (c.preparedArmBase_fresh role p phase fresh)
    (I.ready hloc phase fresh outside) hb B (inventory w hw v).player F W
  have hfinal := c.armCoreFinal_state role p hloc ha phase idle (inventory w hw v).player
  change Reachable B (some 1)
    (PrimitiveProfile.state w hw v (tilePhases phase) (inventory w hw v).player)
    (PrimitiveProfile.state w hw v (tilePhases (Function.update phase p.location true)) (inventory w hw v).player)
  cases hphase : (armSpec w c.gate role).initial
  · simp only [corePhase,preparedArmBase,hphase,Bool.false_eq_true,ite_false] at hc hp
    have hr := hp.trans hc
    rw [←hfinal]
    simpa only [armCoreFinal] using hr
  · simp only [corePhase,preparedArmBase,hphase,ite_true] at hc hp
    have hr := hc.trans hp
    rw [p.wave_update_external (tilePhases phase) _ c.index (c.arm_event_ne_core role p)] at hr
    rw [←hfinal]
    simpa only [armCoreFinal] using hr

end CoreSite
end PushPuzzle.PushS.FiniteSourceInventory
