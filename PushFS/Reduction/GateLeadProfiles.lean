/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.StorageProfiles
public import PushFS.Reduction.GateLeadStorage

/-! Exact independently selected core and three-lead inventories in the actual buffered gate. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateLead

open Gadgets Gadgets.Wires
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] StorageAtlas.initial StorageAtlas.board

def profileCore (a b : Gates.Signals) (f : Fin 4→Bool) : Gates.Signals := if f 0 then b else a

def profileLeads (a b : Gates.Signals) (f : Fin 4→Bool) : Gates.Signals :=
  ⟨if f 1 then b.left else a.left,if f 2 then b.upper else a.upper,if f 3 then b.right else a.right⟩

private def partBoxes (kind : Bool) (n : ℕ) (hn : 2301≤n) (a c : Gates.Signals) : Fin 4→Finset (C n) :=
  Fin.cases (gateBoxes n kind a)
    (Fin.cases (westBoxes kind n hn c.left) (Fin.cases (northBoxes kind n hn c.upper) (fun _=>eastBoxes kind n hn (!c.right))))

private theorem profile_part (kind : Bool) (n : ℕ) (hn : 2301≤n) (a b : Gates.Signals) (f : Fin 4→Bool) (i : Fin 4) :
    ((atlas kind n hn a b).pieceMarks f i).map ((atlas kind n hn a b).embedding i).cells=
      partBoxes kind n hn (profileCore a b f) (profileLeads a b f) i := by
  fin_cases i
  · change ((atlas kind n hn a b).pieceMarks f 0).map ((atlas kind n hn a b).embedding 0).cells=gateBoxes n kind (if f 0 then b else a)
    cases hf : f 0
    all_goals simp only [StorageAtlas.pieceMarks,hf,Bool.false_eq_true,ite_true,ite_false]
    all_goals rfl
  · change ((atlas kind n hn a b).pieceMarks f 1).map ((atlas kind n hn a b).embedding 1).cells=westBoxes kind n hn ((if f 1 then b.left else a.left))
    cases hf : f 1
    all_goals simp only [StorageAtlas.pieceMarks,hf,Bool.false_eq_true,ite_true,ite_false]
    all_goals
      change ((_ : Finset (Chain.C n)).map (westIso kind n).cells.toEmbedding).map _=_
      exact Finset.map_map _ _ _
  · change ((atlas kind n hn a b).pieceMarks f 2).map ((atlas kind n hn a b).embedding 2).cells=northBoxes kind n hn ((if f 2 then b.upper else a.upper))
    cases hf : f 2
    all_goals simp only [StorageAtlas.pieceMarks,hf,Bool.false_eq_true,ite_true,ite_false]
    all_goals
      change ((_ : Finset (Chain.C n)).map (northIso n).cells.toEmbedding).map _=_
      exact Finset.map_map _ _ _
  · change ((atlas kind n hn a b).pieceMarks f 3).map ((atlas kind n hn a b).embedding 3).cells=eastBoxes kind n hn (!(if f 3 then b.right else a.right))
    cases hf : f 3
    all_goals simp only [StorageAtlas.pieceMarks,hf,Bool.false_eq_true,ite_true,ite_false]
    all_goals
      change ((_ : Finset (Chain.C n)).map (eastIso n).cells.toEmbedding).map _=_
      exact Finset.map_map _ _ _

/-- Independently choosing the four true source/target inventories gives the exact semantic mixed buffered state. -/
theorem profile_boxes (kind : Bool) (n : ℕ) (hn : 2301≤n) (a b : Gates.Signals) (f : Fin 4→Bool) :
    (atlas kind n hn a b).profileBoxes f=boxes kind n hn (profileCore a b f) (profileLeads a b f) := by
  have hfin : (Finset.univ : Finset (Fin 4))={0,1,2,3}:=by decide
  unfold StorageAtlas.profileBoxes
  simp only [profile_part]
  rw [hfin]
  ext p
  simp only [Finset.mem_biUnion,Finset.mem_insert,Finset.mem_singleton,exists_eq_or_imp,exists_eq_left]
  change (p∈gateBoxes n kind (profileCore a b f) ∨p∈westBoxes kind n hn (profileLeads a b f).left ∨
      p∈northBoxes kind n hn (profileLeads a b f).upper ∨p∈eastBoxes kind n hn (!(profileLeads a b f).right)) ↔_
  simp only [boxes,leadBoxes,Finset.mem_union]
  tauto

end PushPuzzle.PushFS.Reduction.GateLead
