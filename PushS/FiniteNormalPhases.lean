/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceTargets

/-! Equal source and target orientations give the actual solved normal inventory. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction Gadgets.Wires

def PrimitiveCode.SamePhase : PrimitiveCode → Prop
  | .core g => g.core.initial = g.core.target
  | .line c => c.initial = c.target
  | .turn c => c.initial = c.target

private theorem PrimitiveCode.boxes_eq_targets (w : ℕ) (hw : 2 ≤ w) (c : PrimitiveCode)
    (h : c.SamePhase) :
    (c.instanceOf w hw).initial.boxes = (c.instanceOf w hw).board.goals := by
  cases c with
  | core g =>
    rcases g with ⟨⟨kind,s,t⟩,incoming,pattern,rotation⟩
    change s = t at h
    subst t
    cases kind <;> rfl
  | line c =>
    rcases c with ⟨segment,above,first,last,a,b,desiredSide⟩
    change a = b at h
    subst b
    rfl
  | turn c =>
    rcases c with ⟨incoming,outgoing,corner,a,b⟩
    change a = b at h
    subst b
    rfl

theorem pathCodes_samePhase (segments : List Segment) (initialSide targetSide keepEndpoint a : Bool)
    {c : PrimitiveCode} (hc : c ∈ pathCodes segments initialSide targetSide keepEndpoint a a) : c.SamePhase := by
  unfold pathCodes at hc
  obtain ⟨i,_,hc⟩ := List.mem_flatMap.mp hc
  split_ifs at hc
  · simp only [List.mem_append,List.mem_singleton] at hc
    rcases hc with rfl | rfl <;> rfl
  · simp only [List.append_nil,List.mem_singleton] at hc
    subst c
    rfl

theorem gateCodes_samePhase (w : ℕ) (g : GateTileState) (hg : g.core.initial = g.core.target)
    {c : PrimitiveCode} (hc : c ∈ gateCodes w g) : c.SamePhase := by
  simp only [gateCodes,List.mem_cons,List.mem_flatMap] at hc
  rcases hc with rfl | ⟨role,_,hc⟩
  · exact hg
  · rw [hg] at hc
    exact pathCodes_samePhase _ _ _ _ _ hc

theorem wireCodes_samePhase (w : ℕ) (kind : Catalog.Kind) (a : Bool)
    {c : PrimitiveCode} (hc : c ∈ wireCodes w (kind,a,a)) : c.SamePhase :=
  pathCodes_samePhase _ _ _ _ _ hc

end PushPuzzle.PushS.FiniteRouting

namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting
open Cslib.Complexity.NCL

attribute [local irreducible] Raster.width Raster.height Raster.vertexAt Raster.owner Raster.wireAt

private theorem localCodes_cell_samePhase (w : ℕ) (word : Word) (b : List Bool)
    (p : GridRouting.Point)
    {c : PrimitiveCode} (hc : c ∈ localCodes w (CellPlan.cell ((word,(b,b)),p))) : c.SamePhase := by
  cases hv : Raster.vertexAt (word,p) with
  | some v =>
    simp only [CellPlan.cell,hv,Option.elim_some,localCodes,Sum.elim_inl] at hc
    exact gateCodes_samePhase w _ rfl hc
  | none =>
    simp only [CellPlan.cell,hv,Option.elim_none,CellPlan.ordinary] at hc
    cases ho : Raster.owner (word,p) with
    | none => simp only [ho,Option.elim_none,localCodes,List.not_mem_nil] at hc
    | some e =>
      simp only [ho,Option.elim_some,CellPlan.wireData] at hc
      cases hk : Raster.wireAt (word,(e,p)) with
      | none => simp only [hk,Option.map_none,localCodes,Option.elim_none,List.not_mem_nil] at hc
      | some kind =>
        simp only [hk,Option.map_some,localCodes,Option.elim_some,Sum.elim_inr] at hc
        exact wireCodes_samePhase _ _ _ hc

private theorem cell_entry {v : CellPlan.Source} {entry : GridRouting.Point × CellPlan.Code}
    (he : entry ∈ CellPlan.cells v) : entry.2 = CellPlan.cell (v,entry.1) := by
  simp only [CellPlan.cells,List.mem_flatMap,List.mem_map] at he
  obtain ⟨y,_,x,_,rfl⟩ := he
  rfl

attribute [local irreducible] codes

private theorem code_samePhase (w : ℕ) (word : Word) (b : List Bool)
    {q : GridRouting.Point × PrimitiveCode} (hq : q ∈ codes w (word,(b,b))) : q.2.SamePhase := by
  unfold codes at hq
  obtain ⟨entry,hentry,hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hq
  rw [cell_entry hentry] at hc
  exact localCodes_cell_samePhase w word b entry.1 hc

/-- The emitted physical inventory for equal endpoint configurations is exactly solved. -/
theorem initial_boxes_eq_targets (w : ℕ) (hw : 2 ≤ w) (word : Word) (b : List Bool) :
    (inventory w hw (word,(b,b))).initial.boxes = (inventory w hw (word,(b,b))).board.goals := by
  have heq (i : Fin (codes w (word,(b,b))).length) :
      ((inventory w hw (word,(b,b))).piece i).initial.boxes =
        ((inventory w hw (word,(b,b))).piece i).board.goals :=
    (((codes w (word,(b,b))).get i).2).boxes_eq_targets w hw
      (code_samePhase w word b (List.get_mem _ _))
  ext p
  rw [(inventory w hw (word,(b,b))).mem_boxes_iff,(inventory w hw (word,(b,b))).mem_goals_iff]
  constructor <;> rintro ⟨i,q,hq,he⟩
  · exact ⟨i,q,by rwa [← heq i],he⟩
  · exact ⟨i,q,by rwa [heq i],he⟩

def canonicalBoard (w : ℕ) (hw : 2 ≤ w) (word : Word) (target : List Bool) :
    Board (width w (word,(target,target))) (height w (word,(target,target))) :=
  (inventory w hw (word,(target,target))).board

/-- The real emitted normal inventory, with the same exterior player cell for every configuration. -/
def canonicalState (w : ℕ) (hw : 2 ≤ w) (word : Word) (target current : List Bool) :
    State (width w (word,(target,target))) (height w (word,(target,target))) :=
  (inventory w hw (word,(current,target))).initial

theorem canonicalBoard_eq (w : ℕ) (hw : 2 ≤ w) (word : Word) (target current : List Bool) :
    canonicalBoard w hw word target = (inventory w hw (word,(current,target))).board := by
  apply Board.ext
  · exact walls_rephase w hw word target target current target
  · exact targets_rephase w hw word target current target

theorem canonicalState_solved (w : ℕ) (hw : 2 ≤ w) (word : Word) (target : List Bool) :
    (canonicalState w hw word target target).boxes = (canonicalBoard w hw word target).goals :=
  initial_boxes_eq_targets w hw word target

end PushPuzzle.PushS.FiniteSourceInventory
