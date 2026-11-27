/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceCharts
public import PushS.FiniteSourcePhases
public import PushS.FiniteSourcePorts
public import PushS.FiniteRoutingSeamOwners

/-! Actual local seam owners lift through the emitted source list to complete-board interior charts. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting
open Cslib.Complexity.NCL

attribute [local irreducible] codes width height PrimitiveCode.instanceOf PrimitiveCode.chart

/-- A literal emitted primitive's owner, with its real macrocell coordinate, is a global interior owner. -/
private theorem primitive_owner_lift (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (entry : GridRouting.Point × PrimitiveCode) (hentry : entry ∈ codes w v)
    (p : Cell (entry.2.instanceOf w hw).width (entry.2.instanceOf w hw).height)
    (actual : Cell (width w v) (height w v)) (level : ℕ)
    (hp : coordinates actual = macroShift w entry.1 (entry.2.world w hw p))
    (ho : entry.2.Owner w hw p level) : InteriorOwner w hw v actual level := by
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hentry
  obtain ⟨c,q,hi,hq,hl⟩ := ho
  have hc : coordinates ((inventory w hw v).embedding i |>.cells p) =
      macroShift w ((codes w v).get i).1 (((codes w v).get i).2.world w hw p) :=
    inventory_coordinates w hw v i p
  have he : ((inventory w hw v).embedding i).cells p = actual := by
    have hec := hc.trans hp.symm
    apply Prod.ext <;> apply Fin.ext
    · exact congrArg Prod.fst hec
    · exact congrArg Prod.snd hec
  refine ⟨⟨i,c⟩,q,hi,?_,hl⟩
  exact ((inventory w hw v).placedChart_cells i (((codes w v).get i).2.chart w hw c) q).trans
    ((congrArg ((inventory w hw v).embedding i).cells hq).trans he)

/-- A concrete local source tile's WorldOwner is reindexed into the exact complete source inventory. -/
theorem worldOwner_lift (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (pos point : GridRouting.Point) (level : ℕ) (actual : Cell (width w v) (height w v))
    (ho : WorldOwner w hw (localCodes w (CellPlan.cell (v,pos))) point level)
    (hp : coordinates actual = macroShift w pos point) : InteriorOwner w hw v actual level := by
  obtain ⟨c,hc,p,hcp,howner⟩ := ho
  apply primitive_owner_lift w hw v (pos,c) (code_mem_of_local w v pos c hc) p actual level _ howner
  exact hp.trans (congrArg (macroShift w pos) hcp).symm

end PushPuzzle.PushS.FiniteSourceInventory
