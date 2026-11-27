/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateProfiles
public import PushFS.Reduction.FullGateBufferedWalking
public import PushFS.Reduction.GateLeadProfiles
public import PushFS.Reduction.StorageProfileTransport

/-! The complete independently selected gate profile is its exact mixed buffered state plus the real annular inventory. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting

open Gadgets Gadgets.Wires
open scoped Classical
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] StorageAtlas.initial StorageAtlas.board profile profileOutside

def bufferMask (g : GateTileState) (f : Inventory.Index g→Bool) : Fin 4→Bool := fun i=>f (.inl i)

def bufferCoreSignals (g : GateTileState) (f : Inventory.Index g→Bool) : Gates.Signals :=
  GateLead.profileCore g.core.initial g.core.target (bufferMask g f)

def bufferLeadSignals (g : GateTileState) (f : Inventory.Index g→Bool) : Gates.Signals :=
  GateLead.profileLeads g.core.initial g.core.target (bufferMask g f)

noncomputable def annularProfileBoxes (g : GateTileState) (f : Inventory.Index g→Bool) : Finset C :=
  Finset.univ.biUnion fun i : Inventory.Index g=>
    if Inventory.external g i then (selectedMarks g (f i) i).map (primitiveEmbedding g i).cells else ∅

theorem mem_profile (g : GateTileState) (f : Inventory.Index g→Bool) (player p : C) :
    p∈(profile g f player).boxes ↔∃i : Inventory.Index g,
      ∃q : Cell (Inventory.piece g i).width (Inventory.piece g i).height,
        q∈selectedMarks g (f i) i ∧(primitiveEmbedding g i).cells q=p := by
  rw [profile_split g f (.inl 0),Finset.mem_union]
  constructor
  · rintro (hp|hp)
    · obtain ⟨q,hq,he⟩:=Finset.mem_map.mp hp
      exact ⟨.inl 0,q,hq,he⟩
    · obtain ⟨i,_,q,hq,he⟩:=(mem_profileOutside g f (.inl 0) p).mp hp
      exact ⟨i,q,hq,he⟩
  · rintro ⟨i,q,hq,he⟩
    by_cases hi : i=.inl 0
    · subst i
      exact Or.inl (Finset.mem_map.mpr ⟨q,hq,he⟩)
    · exact Or.inr ((mem_profileOutside g f (.inl 0) p).mpr ⟨i,hi,q,hq,he⟩)

theorem mem_annularProfileBoxes (g : GateTileState) (f : Inventory.Index g→Bool) (p : C) :
    p∈annularProfileBoxes g f ↔∃i : Inventory.Index g,Inventory.external g i=true ∧
      ∃q : Cell (Inventory.piece g i).width (Inventory.piece g i).height,
        q∈selectedMarks g (f i) i ∧(primitiveEmbedding g i).cells q=p := by
  simp only [annularProfileBoxes,Finset.mem_biUnion,Finset.mem_univ,true_and]
  apply exists_congr
  intro i
  by_cases hi : Inventory.external g i=true
  · simp only [hi,ite_true,Finset.mem_map,true_and]
  · simp only [hi,Bool.false_eq_true,ite_false,Finset.notMem_empty,false_and]

attribute [local irreducible] annularProfileBoxes

theorem profile_floor (g : GateTileState) (f : Inventory.Index g→Bool) (player : C) :
    Disjoint (profile g f player).boxes (fullPuzzle g).board.walls := by
  unfold profile StorageAtlas.profileAt
  exact (fullAtlas g).profile_floor (profileMask g f)

private theorem buffer_profile_mem (g : GateTileState) (f : Inventory.Index g→Bool) (p : C) :
    p∈(bufferAtlas g).profileBoxes (bufferMask g f) ↔∃i : Fin 4,
      ∃q : Cell (Inventory.piece g (.inl i)).width (Inventory.piece g (.inl i)).height,
        q∈selectedMarks g (f (.inl i)) (.inl i) ∧(primitiveEmbedding g (.inl i)).cells q=p := by
  simp only [StorageAtlas.profileBoxes,Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_map]
  exact Iff.rfl

/-- Every actual selected box belongs either to the real buffered gate or to the actual selected annulus. -/
private theorem profile_buffer_split (g : GateTileState) (f : Inventory.Index g→Bool) (player : C) :
    @Eq (Finset C) (profile g f player).boxes ((bufferAtlas g).profileBoxes (bufferMask g f)∪annularProfileBoxes g f) := by
  ext p
  rw [mem_profile,Finset.mem_union,buffer_profile_mem,mem_annularProfileBoxes]
  constructor
  · rintro ⟨i,q,hq,he⟩
    cases i with
    | inl i=>exact Or.inl ⟨i,q,hq,he⟩
    | inr i=>exact Or.inr ⟨.inr i,rfl,q,hq,he⟩
  · rintro (⟨i,q,hq,he⟩|⟨i,_,q,hq,he⟩)
    · exact ⟨.inl i,q,hq,he⟩
    · exact ⟨i,q,hq,he⟩

theorem annularProfileBoxes_floor (g : GateTileState) (f : Inventory.Index g→Bool) :
    Disjoint (annularProfileBoxes g f) (fullPuzzle g).board.walls := by
  apply (profile_floor g f (fullAtlas g).player).mono_left
  rw [profile_buffer_split]
  exact Finset.subset_union_right

private theorem buffer_profile_boxes (g : GateTileState) (f : Inventory.Index g→Bool) :
    @Eq (Finset C) ((bufferAtlas g).profileBoxes (bufferMask g f))
      ((GateLead.boxes g.core.isAND 2301 (by omega) (bufferCoreSignals g f) (bufferLeadSignals g f)).map
        (bufferRect g.core.isAND).cells) := by
  change ((GateLead.atlas g.core.isAND 2301 (by omega) g.core.initial g.core.target).translate
    (bufferOffset g.core.isAND).1 (bufferOffset g.core.isAND).2
    (buffer_fitX g.core.isAND) (buffer_fitY g.core.isAND)).profileBoxes _=_
  rw [StorageAtlas.profileBoxes_translate,GateLead.profile_boxes]
  rfl

/-- Exact full-profile storage while the core and all three buffered leads independently choose their physical phases. -/
theorem full_buffer_profile (g : GateTileState) (f : Inventory.Index g→Bool) :
    (bufferRect g.core.isAND).extend (annularProfileBoxes g f)
      (GateLead.state g.core.isAND 2301 (by omega) (bufferCoreSignals g f) (bufferLeadSignals g f))=
      profile g f (fullAtlas g).player := by
  apply State.ext
  · have hh:=congrArg State.player (full_buffer_state g)
    change (bufferRect g.core.isAND).cells (GateLead.player 2301)=(fullAtlas g).initial.player at hh
    unfold StorageAtlas.initial at hh
    unfold profile StorageAtlas.profileAt
    exact hh
  · rw [profile_buffer_split,buffer_profile_boxes]
    rfl

end PushPuzzle.PushFS.Reduction.GateTileRouting
