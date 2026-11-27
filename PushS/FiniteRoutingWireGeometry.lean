/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingInventoryGeometry
public import PushS.FiniteRoutingPathJunctions

/-! The concrete emitted wire tiles have unique owned normal boxes on actual floor. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction Gadgets.Wires

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteTools.turnWalls

private theorem singletonInventory_actorsClear (w : ℕ) (hw : 2 ≤ w) (c : PrimitiveCode)
    (hf : ∀ a ∈ [c], PatchFits w (a.patch w hw)) :
    InventoryActorsClear (inventory w hw [c] hf) := by
  apply inventory_actorsClear
  · intro i j hij
    fin_cases i; fin_cases j
    exact (hij rfl).elim
  · intro i j hij
    fin_cases i; fin_cases j
    exact (hij rfl).elim

private theorem junctionInventory_actorsClear (w : ℕ) (hw : 2 ≤ w) (c d : LineCode) (t : TurnCode)
    (hc : LineGood w c.segment) (hd : LineGood w d.segment) (ht : Perpendicular t.incoming t.outgoing)
    (hlast : c.last = false) (hfirst : d.first = false)
    (hcdir : segmentDirection c.segment = t.incoming)
    (hcfinish : c.segment.finish = advance t.incoming.opposite t.corner 2)
    (hddir : segmentDirection d.segment = t.outgoing)
    (hdstart : d.segment.start = advance t.outgoing t.corner 1)
    (hf : ∀ a ∈ [PrimitiveCode.line c,.turn t,.line d], PatchFits w (a.patch w hw)) :
    InventoryActorsClear (inventory w hw [PrimitiveCode.line c,.turn t,.line d] hf) := by
  apply inventory_actorsClear
  · intro i j hij goal l r
    fin_cases i <;> fin_cases j
    all_goals try exact (hij rfl).elim
    · exact incoming_line_actor_ne_turn_actor w hw c t hc ht hlast hcdir hcfinish goal goal l r
    · exact incoming_line_actor_ne_outgoing_actor w hw c d t hc hd ht hlast hfirst
        hcdir hcfinish hddir hdstart goal goal l r
    · exact Ne.symm (incoming_line_actor_ne_turn_actor w hw c t hc ht hlast hcdir hcfinish goal goal r l)
    · exact Ne.symm (outgoing_line_actor_ne_turn_actor w hw d t hd ht hfirst hddir hdstart goal goal r l)
    · exact Ne.symm (incoming_line_actor_ne_outgoing_actor w hw c d t hc hd ht hlast hfirst
        hcdir hcfinish hddir hdstart goal goal r l)
    · exact outgoing_line_actor_ne_turn_actor w hw d t hd ht hfirst hddir hdstart goal goal l r
  · intro i j hij goal l p hp
    fin_cases i <;> fin_cases j
    all_goals try exact (hij rfl).elim
    · exact incoming_line_actor_ne_turn_wall w hw c t hc ht hlast hcdir hcfinish goal l p hp
    · exact incoming_line_actor_ne_outgoing_wall w hw c d t hc hd ht hlast hcdir hcfinish
        hddir hdstart goal l p hp
    · exact turn_actor_ne_incoming_wall w hw c t hc ht hcdir hcfinish goal l p hp
    · exact turn_actor_ne_outgoing_wall w hw d t hd ht hddir hdstart goal l p hp
    · exact outgoing_line_actor_ne_incoming_wall w hw c d t hc hd ht hfirst hcdir hcfinish
        hddir hdstart goal l p hp
    · exact outgoing_line_actor_ne_turn_wall w hw d t hd ht hfirst hddir hdstart goal l p hp

def wireHasTurn : Catalog.Kind → Bool
  | .east | .west | .south => false
  | .westSouth | .eastSouth | .southEast | .southWest => true

def wireLineCode (w : ℕ) (q : Catalog.Bitmap.Args) (i : ℕ) : LineCode :=
  lineCodeAt (wireRoute w q.1) false false true q.2.1 q.2.2 i

def wireTurnCode (w : ℕ) (q : Catalog.Bitmap.Args) : TurnCode :=
  turnCodeAt (wireRoute w q.1) q.2.1 q.2.2 0

theorem wireRoute_length (w : ℕ) (kind : Catalog.Kind) :
    (wireRoute w kind).length = if wireHasTurn kind then 2 else 1 := by
  cases kind <;> simp [wireRoute,wireVertices,wireHasTurn]

theorem wireRoute_joined (w : ℕ) (kind : Catalog.Kind) :
    (wireRoute w kind).IsChain (fun s t => s.finish = t.start) := by
  cases kind <;> simp [wireRoute,wireVertices,List.isChain_cons_cons]

set_option maxRecDepth 65536 in
private theorem wireCodes_shape (w : ℕ) (q : Catalog.Bitmap.Args) :
    wireCodes w q = if wireHasTurn q.1 then
      [.line (wireLineCode w q 0),.turn (wireTurnCode w q),.line (wireLineCode w q 1)]
    else [.line (wireLineCode w q 0)] := by
  rcases q with ⟨kind,initial,target⟩
  cases kind <;> dsimp only [wireCodes,wireHasTurn,wireLineCode,wireTurnCode] <;>
    simp only [Bool.false_eq_true,↓reduceIte]
  · exact pathCodes_singleton _ _ _ _ _ _
  · exact pathCodes_singleton _ _ _ _ _ _
  · exact pathCodes_singleton _ _ _ _ _ _
  all_goals
    apply pathCodes_pair
    have hs := spacing_pos w
    have hhalf : 25*spacing w < tileStride w := by unfold tileStride; omega
    unfold segmentDirection
    split_ifs <;> simp_all

private theorem wireTurnCode_perpendicular (w : ℕ) (q : Catalog.Bitmap.Args)
    (ht : wireHasTurn q.1 = true) :
    Perpendicular (wireTurnCode w q).incoming (wireTurnCode w q).outgoing := by
  apply wireCodes_turn_perpendicular w q
  rw [wireCodes_shape]
  simp [ht]

private theorem wire_junction_contract (w : ℕ) (q : Catalog.Bitmap.Args)
    (ht : wireHasTurn q.1 = true) :
    JunctionContract w (wireLineCode w q 0) (wireTurnCode w q) (wireLineCode w q 1) :=
  path_junction_contract w _ (wireRoute_good w q.1) (wireRoute_joined w q.1) false false true
    q.2.1 q.2.2 0 (by simp only [wireRoute_length,ht,↓reduceIte]; decide)
    (wireTurnCode_perpendicular w q ht)

private theorem transport_actorsClear (w : ℕ) (hw : 2 ≤ w) (codes pieces : List PrimitiveCode)
    (he : codes = pieces) (hf : ∀ a ∈ codes, PatchFits w (a.patch w hw))
    (hg : ∀ a ∈ pieces, PatchFits w (a.patch w hw))
    (hc : InventoryActorsClear (inventory w hw pieces hg)) :
    InventoryActorsClear (inventory w hw codes hf) := by
  subst pieces
  exact hc

/-- All seven actual emitted wire bitmaps have unique matched source and target boxes on actual union floor. -/
theorem wireInventory_actorsClear (w : ℕ) (hw : 2 ≤ w) (q : Catalog.Bitmap.Args) :
    InventoryActorsClear (wireInventory w hw q) := by
  have hshape := wireCodes_shape w q
  unfold wireInventory
  by_cases ht : wireHasTurn q.1 = true
  · simp only [ht,↓reduceIte] at hshape
    have hc := wire_junction_contract w q ht
    have hf : ∀ a ∈ [PrimitiveCode.line (wireLineCode w q 0),.turn (wireTurnCode w q),
        .line (wireLineCode w q 1)], PatchFits w (a.patch w hw) := by
      intro a ha
      exact wireCode_fits w hw q (by rw [hshape]; exact ha)
    have hclear := junctionInventory_actorsClear w hw _ _ _ hc.incoming_good hc.outgoing_good
      hc.perpendicular hc.incoming_last hc.outgoing_first hc.incoming_direction hc.incoming_finish
      hc.outgoing_direction hc.outgoing_start hf
    exact transport_actorsClear w hw _ _ hshape _ hf hclear
  · simp only [ht] at hshape
    have hf : ∀ a ∈ [PrimitiveCode.line (wireLineCode w q 0)], PatchFits w (a.patch w hw) := by
      intro a ha
      exact wireCode_fits w hw q (by rw [hshape]; exact ha)
    exact transport_actorsClear w hw _ _ hshape _ hf (singletonInventory_actorsClear w hw _ hf)

end PushPuzzle.PushS.FiniteRouting
