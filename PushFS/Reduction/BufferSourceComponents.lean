/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateBufferedWalking
public import PushFS.Reduction.FullGateRawLabels
public import PushFS.Gadgets.Gates.Soundness.Relay.Boundary

/-! Actual core port identities and their buffered leads share the same wall-only component. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting

open Gadgets Gadgets.Wires Gates.Soundness
set_option maxRecDepth 65536
set_option maxHeartbeats 100000
attribute [local irreducible] StorageAtlas.initial StorageAtlas.board

def coreGhost (kind : Bool) : Fin 3→Gates.C :=
  ![(⟨if kind then 1 else 2,by cases kind <;> decide⟩,
      ⟨if kind then 29 else 90,by cases kind <;> decide⟩),
    (⟨if kind then 43 else 44,by cases kind <;> decide⟩,2),
    (⟨if kind then 79 else 78,by cases kind <;> decide⟩,90)]

def chainGhost (n : ℕ) : Chain.C n := (⟨1,by omega⟩,10)

private theorem ghost_checked : ∀(kind : Bool) (b : Gates.Signals) (r : Fin 3),
    Gates.staticRun (Gates.wallTest kind) (Gates.position kind b (Relay.outerLabel kind r))
        (if gateClaim b r then [] else [Gates.portDirection r])=some (coreGhost kind r) ∧
      Gates.staticRun (Gates.wallTest kind) (coreGhost kind r)
        (if gateClaim b r then [] else [(Gates.portDirection r).opposite])=
          some (Gates.position kind b (Relay.outerLabel kind r)) := by
  decide +kernel

private theorem core_ghost_component (kind : Bool) (b : Gates.Signals) (r : Fin 3) :
    SameComponent (Gates.board kind ∅) (Gates.position kind b (Relay.outerLabel kind r)) (coreGhost kind r) :=
  ⟨Gates.staticRun_sound (Gates.wallTest_correct kind ∅) (ghost_checked kind b r).1,
    Gates.staticRun_sound (Gates.wallTest_correct kind ∅) (ghost_checked kind b r).2⟩

theorem core_ghost_step : ∀(kind : Bool) (b : Gates.Signals) (r : Fin 3),
    (gateClaim b r=true→Gates.position kind b (Relay.outerLabel kind r)=coreGhost kind r) ∧
      (gateClaim b r=false→Adjacent (Gates.portDirection r)
        (Gates.position kind b (Relay.outerLabel kind r)) (coreGhost kind r)) := by decide +kernel

private theorem gateLead_ghost (kind : Bool) (n : ℕ) (r : Fin 3) :
    (GateLead.gate n).cells (coreGhost kind r)=(frontierLeadPlacement kind n r).cells (chainGhost n) := by
  fin_cases r
  · change (GateLead.gate n).cells (coreGhost kind 0)=(GateLead.west kind n).cells (chainGhost n)
    cases kind <;> apply Prod.ext <;> apply Fin.ext
    all_goals simp [coreGhost,chainGhost,GateLead.gate_x,GateLead.gate_y,GateLead.west_x,GateLead.west_y]
    all_goals omega
  · change (GateLead.gate n).cells (coreGhost kind 1)=(GateLead.north kind n).cells (chainGhost n)
    cases kind <;> apply Prod.ext <;> apply Fin.ext
    all_goals simp [coreGhost,chainGhost,GateLead.gate_x,GateLead.gate_y,GateLead.north_x,GateLead.north_y]
    all_goals omega
  · change (GateLead.gate n).cells (coreGhost kind 2)=(GateLead.east kind n).cells (chainGhost n)
    cases kind <;> apply Prod.ext <;> apply Fin.ext
    all_goals simp [coreGhost,chainGhost,GateLead.gate_x,GateLead.gate_y,GateLead.east_x,GateLead.east_y]

theorem buffer_ghost (g : GateTileState) (r : Fin 3) :
    (coreEmbedding g).cells (coreGhost g.core.isAND r)=
      (bufferLeadEmbedding g r).cells (chainGhost 2301) := by
  have he:=(GateLead.atlas g.core.isAND 2301 (by omega) g.core.initial g.core.target).translate_embedding
    (bufferOffset g.core.isAND).1 (bufferOffset g.core.isAND).2
    (buffer_fitX g.core.isAND) (buffer_fitY g.core.isAND) 0 (coreGhost g.core.isAND r)
  exact he.trans (congrArg (bufferRect g.core.isAND).cells (gateLead_ghost g.core.isAND 2301 r))

def bufferLabel (g : GateTileState) (r : Fin 3) (l : Chain.Label 2301) : RawLabel g :=
  Fin.cases ⟨.inl 1,l⟩ (Fin.cases ⟨.inl 2,l⟩ (fun _=>⟨.inl 3,l⟩)) r

theorem bufferLabel_source (g : GateTileState) (r : Fin 3) (l : Chain.Label 2301) :
    (rawSlotMatching g).source (bufferLabel g r l)=(bufferLeadEmbedding g r).cells
      (Chain.position 2301 (by omega) (Chain.uniform 2301 (Inventory.initialPhase g r)) l) := by
  fin_cases r
  all_goals dsimp only [bufferLabel,Fin.cases]
  all_goals rw [raw_source]
  · exact buffer_lead_placement g 0 _
  · exact buffer_lead_placement g 1 _
  · exact buffer_lead_placement g 2 _

theorem buffer_source_component (g : GateTileState) (r : Fin 3) (l : Chain.Label 2301) :
    SameComponent (fullPuzzle g).board
      ((rawSlotMatching g).source ⟨.inl 0,Relay.outerLabel g.core.isAND r⟩)
      ((rawSlotMatching g).source (bufferLabel g r l)) := by
  have hw : (coreEmbedding g).WallsAgree (Gates.board g.core.isAND ∅) (fullPuzzle g).board :=
    primitive_walls_agree g (.inl 0)
  have hc:=core_ghost_component g.core.isAND g.core.initial r
  have hc' : SameComponent (fullPuzzle g).board
      ((coreEmbedding g).cells (Gates.position g.core.isAND g.core.initial (Relay.outerLabel g.core.isAND r)))
      ((coreEmbedding g).cells (coreGhost g.core.isAND r)) :=
    ⟨GridEmbedding.staticReach hw hc.1,GridEmbedding.staticReach hw hc.2⟩
  have hb : SameComponent (Chain.board 2301 (by omega) ∅) (chainGhost 2301)
      (Chain.position 2301 (by omega) (Chain.uniform 2301 (Inventory.initialPhase g r)) l) := by
    have hx:=Polyline.chain_phase_bounds 2301 (by omega) (Inventory.initialPhase g r) l
    have hy:=Chain.position_row 2301 (by omega) (Chain.uniform 2301 (Inventory.initialPhase g r)) l
    have hp : Chain.position 2301 (by omega) (Chain.uniform 2301 (Inventory.initialPhase g r)) l=
        ((Chain.position 2301 (by omega) (Chain.uniform 2301 (Inventory.initialPhase g r)) l).1,10) :=
      Prod.ext rfl (Fin.ext hy)
    rw [hp]
    have hphase : (Inventory.initialPhase g r).toNat≤1 := by cases Inventory.initialPhase g r <;> decide
    exact Wires.Soundness.horizontal_component 10 (Wires.Soundness.ChainGeometry.row_floor 2301 (by omega))
      1 _ (by decide) (by omega)
  have hb' : SameComponent (fullPuzzle g).board
      ((bufferLeadEmbedding g r).cells (chainGhost 2301))
      ((bufferLeadEmbedding g r).cells (Chain.position 2301 (by omega) (Chain.uniform 2301 (Inventory.initialPhase g r)) l)) :=
    ⟨GridEmbedding.staticReach (buffer_lead_walls g r) hb.1,GridEmbedding.staticReach (buffer_lead_walls g r) hb.2⟩
  rw [bufferLabel_source]
  rw [buffer_ghost] at hc'
  have hsource:=raw_source g (.inl 0) (Relay.outerLabel g.core.isAND r)
  exact hsource.symm ▸⟨hc'.1.trans hb'.1,hb'.2.trans hc'.2⟩

end PushPuzzle.PushFS.Reduction.GateTileRouting
