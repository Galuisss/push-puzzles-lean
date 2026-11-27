/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalPlacements
public import PushFS.Reduction.PhysicalPorts

/-! Every actual used face has a concrete reciprocal physical macrocell owner. -/

@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory

open Cslib.Complexity.NCL PhysicalBitmap
attribute [local irreducible] Raster.width Raster.height

def indexAt (v : CellPlan.Source) (p : GridRouting.Point) (k : PhysicalTiles.Key)
    (hk : PhysicalTiles.key (CellPlan.cell (v,p))=some k) : Index v := by
  have hn : CellPlan.cell (v,p)≠none := by intro he; rw [he] at hk; cases hk
  exact ⟨((⟨p.1,(CellPlan.nonempty_bounds hn).1⟩,⟨p.2,(CellPlan.nonempty_bounds hn).2⟩),k),hk⟩

theorem used_neighbor (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (i : Index v) (d : Direction) (hu : PhysicalTiles.Used (tile i) d) :
    ∃j : Index v,neighbor d (position i)=some (position j) ∧PhysicalTiles.Used (tile j) d.opposite := by
  obtain ⟨p,hp,hused⟩:=CellPlan.used_neighbor v hP hT (position i) d
    ((PhysicalTiles.used_key (key_eq i) d).mp hu)
  cases hc : CellPlan.cell (v,p) with
  | none=>rw [hc] at hused; exact hused.elim
  | some c=>
    rcases c with g|w
    · let j:=indexAt v p (.inl g.2) (by rw [hc]; rfl)
      exact ⟨j,hp,(PhysicalTiles.used_key (key_eq j) d.opposite).mpr hused⟩
    · let j:=indexAt v p (.inr w.2) (by rw [hc]; rfl)
      exact ⟨j,hp,(PhysicalTiles.used_key (key_eq j) d.opposite).mpr hused⟩

end PushPuzzle.PushFS.Reduction.PhysicalInventory
