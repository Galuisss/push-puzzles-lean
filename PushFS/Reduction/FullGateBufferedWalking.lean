/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateWalking
public import PushFS.Reduction.GateLeadTransit

/-! The complete annular inventory supplies the real foreign boxes of the buffered gate shell. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting


open Gadgets Gadgets.Wires
open scoped Classical
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

noncomputable def annularBoxes (g : GateTileState) : Finset C :=
  Finset.univ.biUnion fun i : Inventory.Index g=>
    if Inventory.external g i then (Inventory.piece g i).initial.boxes.map (primitiveEmbedding g i).cells else ∅

private theorem buffer_initial (g : GateTileState) :
    (bufferAtlas g).initial=(bufferRect g.core.isAND).extend ∅
      (GateLead.state g.core.isAND 2301 (by omega) g.core.initial g.core.initial) := by
  change ((GateLead.atlas g.core.isAND 2301 (by omega) g.core.initial g.core.target).translate
    (bufferOffset g.core.isAND).1 (bufferOffset g.core.isAND).2
    (buffer_fitX g.core.isAND) (buffer_fitY g.core.isAND)).initial=_
  rw [StorageAtlas.translate_initial,GateLead.initial_state]
  rfl

private theorem west_piece_wall (kind : Bool) (n : ℕ) (hn : 2301≤n) (a b : Gates.Signals) (p : Chain.C n) :
    (GateLead.westIso kind n).cells p∈(GateLead.piece kind n hn a b 1).board.walls ↔p∈Chain.walls n hn :=
  (GateLead.westIso kind n).mem_walls (Chain.puzzle n hn a.left b.left).board p

private theorem north_piece_wall (kind : Bool) (n : ℕ) (hn : 2301≤n) (a b : Gates.Signals) (p : Chain.C n) :
    (GateLead.northIso n).cells p∈(GateLead.piece kind n hn a b 2).board.walls ↔p∈Chain.walls n hn :=
  (GateLead.northIso n).mem_walls (Chain.puzzle n hn a.upper b.upper).board p

private theorem east_piece_wall (kind : Bool) (n : ℕ) (hn : 2301≤n) (a b : Gates.Signals) (p : Chain.C n) :
    (GateLead.eastIso n).cells p∈(GateLead.piece kind n hn a b 3).board.walls ↔p∈Chain.walls n hn :=
  (GateLead.eastIso n).mem_walls (Chain.puzzle n hn (!a.right) (!b.right)).board p

attribute [local irreducible] StorageAtlas.initial StorageAtlas.board

theorem mem_annularBoxes (g : GateTileState) (p : C) :
    p∈annularBoxes g ↔∃i : Inventory.Index g,Inventory.external g i=true ∧
      ∃q : Cell (Inventory.piece g i).width (Inventory.piece g i).height,
        q∈(Inventory.piece g i).initial.boxes ∧(primitiveEmbedding g i).cells q=p := by
  simp only [annularBoxes,Finset.mem_biUnion,Finset.mem_univ,true_and]
  apply exists_congr
  intro i
  by_cases hi : Inventory.external g i=true
  · simp only [hi,ite_true,Finset.mem_map,true_and]
  · simp only [hi,Bool.false_eq_true,ite_false,Finset.notMem_empty,false_and]

attribute [local irreducible] annularBoxes

private theorem annularBoxes_subset
    (g : GateTileState) : annularBoxes g⊆(fullPuzzle g).initial.boxes := by
  intro p hp
  obtain ⟨i,_,q,hq,rfl⟩:=(mem_annularBoxes g p).mp hp
  exact (full_box_membership g _).mpr ⟨i,q,hq,rfl⟩

private theorem annularBoxes_floor (g : GateTileState) : Disjoint (annularBoxes g)
    (fullPuzzle g).board.walls :=
  (fullPuzzle g).initial_valid.2.1.mono_left (annularBoxes_subset g)

/-- The full source inventory is exactly the real buffered gate plus all actual annular pieces. -/
private theorem full_initial_split (g : GateTileState) :
    @Eq (Finset C) (fullPuzzle g).initial.boxes ((bufferAtlas g).initial.boxes∪annularBoxes g) := by
  apply Finset.ext (α:=C)
  intro p
  constructor
  · intro hp
    obtain ⟨i,q,hq,he⟩:=(full_box_membership g p).mp hp
    cases i with
    | inl i =>
      apply Finset.mem_union_left
      apply ((bufferAtlas g).mem_boxes_iff p).mpr
      refine ⟨i,q,hq,?_⟩
      apply Prod.ext <;> apply Fin.ext
      · exact congrArg Prod.fst he
      · exact congrArg Prod.snd he
    | inr i =>
      apply Finset.mem_union_right
      apply (mem_annularBoxes g p).mpr
      refine ⟨.inr i,rfl,q,hq,?_⟩
      apply Prod.ext <;> apply Fin.ext
      · exact congrArg Prod.fst he
      · exact congrArg Prod.snd he
  · intro hp
    rcases Finset.mem_union.mp hp with hp|hp
    · obtain ⟨i,q,hq,rfl⟩:=((bufferAtlas g).mem_boxes_iff p).mp hp
      exact (full_box_membership g _).mpr ⟨.inl i,q,hq,rfl⟩
    · exact annularBoxes_subset g hp

/-- All annular boxes are outside the actual 81×107 core, in every complete canonical phase. -/
private theorem annularBoxes_core_empty (g : GateTileState) (p : Gates.C) :
    (coreEmbedding g).cells p∉annularBoxes g := by
  intro hp
  obtain ⟨i,hi,q,_,he⟩:=(mem_annularBoxes g _).mp hp
  cases i with
  | inl i => cases hi
  | inr i =>
    have hc : Inventory.contact g (.inl 0) (.inr i)=false := by
      rcases i with ⟨r,j|j⟩|r
      · simp only [Inventory.contact,decide_eq_false_iff_not,Fin.val_zero]
        omega
      · rfl
      · rfl
    exact Inventory.no_coincident g (.inl 0) (.inr i) (by simp) hc p q
      (congrArg (fun q : C=>(q.1.val,q.2.val)) he.symm)

def bufferLeadIso (g : GateTileState) : (r : Fin 3)→
    GridIsometry 2306 21 ((bufferAtlas g).piece (frontierBufferIndex r)).width
      ((bufferAtlas g).piece (frontierBufferIndex r)).height :=
  Fin.cases (GateLead.westIso g.core.isAND 2301)
    (Fin.cases (GateLead.northIso 2301) (fun _=>GateLead.eastIso 2301))

def bufferLeadEmbedding (g : GateTileState) (r : Fin 3) : GridEmbedding 2306 21 200007 198068 :=
  (frontierLeadPlacement g.core.isAND 2301 r).trans (bufferRect g.core.isAND)

theorem buffer_lead_placement (g : GateTileState) (r : Fin 3) (p : Chain.C 2301) :
    (primitiveEmbedding g (.inl (frontierBufferIndex r))).cells ((bufferLeadIso g r).cells p)=
      (bufferLeadEmbedding g r).cells p := by
  have hh:=(GateLead.atlas g.core.isAND 2301 (by omega) g.core.initial g.core.target).translate_embedding
    (bufferOffset g.core.isAND).1 (bufferOffset g.core.isAND).2
    (buffer_fitX g.core.isAND) (buffer_fitY g.core.isAND) (frontierBufferIndex r) ((bufferLeadIso g r).cells p)
  fin_cases r <;> exact hh

theorem buffer_lead_walls (g : GateTileState) (r : Fin 3) :
    (bufferLeadEmbedding g r).WallsAgree (Chain.board 2301 (by omega) ∅) (fullPuzzle g).board := by
  fin_cases r
  · intro p
    have hw:=primitive_walls_agree g (.inl 1) ((GateLead.westIso g.core.isAND 2301).cells p)
    have he:=buffer_lead_placement g 0 p
    change (primitiveEmbedding g (.inl 1)).cells ((GateLead.westIso g.core.isAND 2301).cells p)=
      (bufferLeadEmbedding g 0).cells p at he
    rw [he] at hw
    have hb : (GateLead.westIso g.core.isAND 2301).cells p∈(Inventory.piece g (.inl 1)).board.walls ↔
        p∈Chain.walls 2301 (by omega) :=
      west_piece_wall g.core.isAND 2301 (by omega) g.core.initial g.core.target p
    exact hw.trans hb
  · intro p
    have hw:=primitive_walls_agree g (.inl 2) ((GateLead.northIso 2301).cells p)
    have he:=buffer_lead_placement g 1 p
    change (primitiveEmbedding g (.inl 2)).cells ((GateLead.northIso 2301).cells p)=
      (bufferLeadEmbedding g 1).cells p at he
    rw [he] at hw
    have hb : (GateLead.northIso 2301).cells p∈(Inventory.piece g (.inl 2)).board.walls ↔
        p∈Chain.walls 2301 (by omega) :=
      north_piece_wall g.core.isAND 2301 (by omega) g.core.initial g.core.target p
    exact hw.trans hb
  · intro p
    have hw:=primitive_walls_agree g (.inl 3) ((GateLead.eastIso 2301).cells p)
    have he:=buffer_lead_placement g 2 p
    change (primitiveEmbedding g (.inl 3)).cells ((GateLead.eastIso 2301).cells p)=
      (bufferLeadEmbedding g 2).cells p at he
    rw [he] at hw
    have hb : (GateLead.eastIso 2301).cells p∈(Inventory.piece g (.inl 3)).board.walls ↔
        p∈Chain.walls 2301 (by omega) :=
      east_piece_wall g.core.isAND 2301 (by omega) g.core.initial g.core.target p
    exact hw.trans hb

theorem full_buffer_state (g : GateTileState) :
    (bufferRect g.core.isAND).extend (annularBoxes g)
      (GateLead.state g.core.isAND 2301 (by omega) g.core.initial g.core.initial)=(fullPuzzle g).initial := by
  apply State.ext
  · change (bufferRect g.core.isAND).cells (GateLead.player 2301)=(fullAtlas g).initial.player
    unfold StorageAtlas.initial
    rfl
  · rw [full_initial_split]
    have hh:=congrArg State.boxes (buffer_initial g)
    change (bufferAtlas g).initial.boxes=
      (GateLead.boxes g.core.isAND 2301 (by omega) g.core.initial g.core.initial).map (bufferRect g.core.isAND).cells∪∅ at hh
    rw [Finset.union_empty] at hh
    change _∪annularBoxes g=(bufferAtlas g).initial.boxes∪annularBoxes g
    exact congrArg (·∪annularBoxes g) hh.symm

/-- The complete real annulus meets all four actual buffered-gate wall stencils and leaves its core empty. -/
theorem bufferShell (g : GateTileState) :
    GateLead.ThinShell g.core.isAND 2301 (by omega) (bufferRect g.core.isAND) (fullPuzzle g).board (annularBoxes g) where
  gate p:=by
    have hw:=primitive_walls_agree g (.inl 0) p
    have he:=(GateLead.atlas g.core.isAND 2301 (by omega) g.core.initial g.core.target).translate_embedding
      (bufferOffset g.core.isAND).1 (bufferOffset g.core.isAND).2
      (buffer_fitX g.core.isAND) (buffer_fitY g.core.isAND) 0 p
    change (primitiveEmbedding g (.inl 0)).cells p=((GateLead.gate 2301).trans (bufferRect g.core.isAND)).cells p at he
    rw [he] at hw
    exact hw
  west:=buffer_lead_walls g 0
  north:=buffer_lead_walls g 1
  east:=buffer_lead_walls g 2
  outside_floor:=annularBoxes_floor g
  gate_empty p:=by
    have hh:=annularBoxes_core_empty g p
    have he:=(GateLead.atlas g.core.isAND 2301 (by omega) g.core.initial g.core.target).translate_embedding
      (bufferOffset g.core.isAND).1 (bufferOffset g.core.isAND).2
      (buffer_fitX g.core.isAND) (buffer_fitY g.core.isAND) 0 p
    change (coreEmbedding g).cells p=((GateLead.gate 2301).trans (bufferRect g.core.isAND)).cells p at he
    rw [he] at hh
    exact hh

end PushPuzzle.PushFS.Reduction.GateTileRouting
