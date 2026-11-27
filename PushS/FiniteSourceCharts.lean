/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FinitePrimitiveCharts
public import PushS.FiniteSourceInventory
public import PushFS.Reduction.InventoryCharts

/-! Every actual source primitive contributes its real placed rail and sink wall stencils. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting

attribute [local irreducible] codes width height InventoryAssembly.walls InventoryAssembly.board

abbrev Chart (w : ℕ) (v : CellPlan.Source) := (i : Fin (codes w v).length) × ((codes w v).get i).2.Charts

def chart (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source) (c : Chart w v) :
    TranslatedAxisChart (width w v) (height w v) :=
  (inventory w hw v).placedChart c.1 (((codes w v).get c.1).2.chart w hw c.2)

/-- All actual minimal chart walls occur in the complete emitted primitive wall union. -/
theorem chart_walls (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source) (c : Chart w v)
    (p : Cell (chart w hw v c).width (chart w hw v c).height)
    (hp : p ∈ (chart w hw v c).board.walls) :
    (chart w hw v c).embedding.cells p ∈ (inventory w hw v).walls :=
  (inventory w hw v).placedChart_walls c.1 _ (((codes w v).get c.1).2.chart_walls w hw c.2) p hp

/-- Every actual global source and target identity lies on one of the placed primitive stencils. -/
theorem chart_actor (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source) (goal : Bool)
    (l : (inventory w hw v).PhysicalLabel) :
    ∃ c q, (chart w hw v c).embedding.cells q =
        (if goal then (inventory w hw v).target l else (inventory w hw v).source l) ∧
      (chart w hw v c).classifier.name q ≠ .outside := by
  obtain ⟨c,q,hq,hn⟩ := (((codes w v).get l.1).2.chart_actor w hw goal l.2)
  refine ⟨⟨l.1,c⟩,q,?_,hn⟩
  refine ((inventory w hw v).placedChart_cells l.1 (((codes w v).get l.1).2.chart w hw c) q).trans ?_
  cases goal <;> exact congrArg ((inventory w hw v).embedding l.1).cells hq

theorem initial_covered (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (p : Cell (width w v) (height w v)) (hp : p ∈ (inventory w hw v).initial.boxes) :
    ∃ c q, (chart w hw v c).embedding.cells q = p ∧ (chart w hw v c).classifier.name q ≠ .outside := by
  obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hp
  exact chart_actor w hw v false l

def InteriorOwner (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (p : Cell (width w v) (height w v)) (level : ℕ) : Prop :=
  ∃ c q, Interior q ∧ (chart w hw v c).embedding.cells q = p ∧
    level ≤ ((chart w hw v c).classifier.name q).level

attribute [local irreducible] PrimitiveCode.instanceOf PrimitiveCode.chart

-- Normalize dependent chart dimensions against the concrete flattened inventory.
set_option maxHeartbeats 1000000 in
/-- Internal primitive owners lift directly to the actual complete source board. -/
theorem chart_owner_or_exit (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source) (c : Chart w v)
    (p : Cell (chart w hw v c).width (chart w hw v c).height)
    (hp : (chart w hw v c).classifier.name p ≠ .outside)
    (hf : (chart w hw v c).embedding.cells p ∉ (inventory w hw v).walls) :
    (((codes w v).get c.1).2).Exit w hw
        (((codes w v).get c.1).2.chart w hw c.2 |>.embedding.cells p) ∨
      InteriorOwner w hw v ((chart w hw v c).embedding.cells p) ((chart w hw v c).classifier.name p).level := by
  have he := (inventory w hw v).placedChart_cells c.1 (((codes w v).get c.1).2.chart w hw c.2) p
  have hlocal : (((codes w v).get c.1).2.chart w hw c.2).embedding.cells p ∉
      (((codes w v).get c.1).2.instanceOf w hw).board.walls := by
    intro hm
    have hmem : ((inventory w hw v).embedding c.1).cells
        ((((codes w v).get c.1).2.chart w hw c.2).embedding.cells p) ∈ (inventory w hw v).walls :=
      (inventory w hw v).wall_mem_of_piece c.1
        ((((codes w v).get c.1).2.chart w hw c.2).embedding.cells p) hm
    exact hf ((congrArg (fun q : Cell (width w v) (height w v) => q ∈ (inventory w hw v).walls) he).mpr hmem)
  rcases (((codes w v).get c.1).2).chart_owner_or_exit w hw c.2 p hp hlocal with hexit | ⟨d,q,hi,hq,hl⟩
  · exact Or.inl hexit
  · refine Or.inr ⟨⟨c.1,d⟩,q,hi,?_,hl⟩
    exact ((inventory w hw v).placedChart_cells c.1 (((codes w v).get c.1).2.chart w hw d) q).trans
      ((congrArg ((inventory w hw v).embedding c.1).cells hq).trans he.symm)

end PushPuzzle.PushS.FiniteSourceInventory
