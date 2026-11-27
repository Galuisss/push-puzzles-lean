/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalSlotOwners

/-! The complete actual finite storage inventory and legal board of a checked source word. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory


open Cslib.Complexity.NCL PhysicalBitmap

/-- Exactly the nonempty physical cells emitted by the actual source compiler. -/
abbrev Index (v : CellPlan.Source) :=
  {t : Raster.Cell v.1×PhysicalTiles.Key //
    PhysicalTiles.key (CellPlan.cell (v,(t.1.1.val,t.1.2.val)))=some t.2}

instance (v : CellPlan.Source) : Fintype (Index v) := by unfold Index; infer_instance

def position {v : CellPlan.Source} (i : Index v) : GridRouting.Point := (i.val.1.1.val,i.val.1.2.val)
def tile {v : CellPlan.Source} (i : Index v) : PhysicalTiles.Key := i.val.2

theorem key_eq {v : CellPlan.Source} (i : Index v) : PhysicalTiles.key (CellPlan.cell (v,position i))=some (tile i) :=
  i.property

theorem position_injective {v : CellPlan.Source} : Function.Injective (position (v := v)) := by
  intro i j he
  apply Subtype.ext
  apply Prod.ext
  · apply Prod.ext <;> apply Fin.ext
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he
  · apply PhysicalTiles.same_position_key (key_eq i)
    rw [he]
    exact key_eq j

noncomputable def numbering (v : CellPlan.Source) : Index v≃Fin (Fintype.card (Index v)) := Fintype.equivFin _

noncomputable def Labels (v : CellPlan.Source) (i : Fin (Fintype.card (Index v))) : Type :=
  PhysicalTiles.Labels (tile ((numbering v).symm i))

noncomputable instance (v : CellPlan.Source) (i : Fin (Fintype.card (Index v))) : Fintype (Labels v i) :=
  inferInstanceAs (Fintype (PhysicalTiles.Labels (tile ((numbering v).symm i))))

/-- All complete actual tiles, with exact walls, source/target owners and the one exterior player. -/
noncomputable def atlas (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] []) :
    StorageAtlas (Fintype.card (Index v)) (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7) (Labels v) where
  piece i := PhysicalTiles.piece (tile ((numbering v).symm i))
  matching i := PhysicalTiles.matching (tile ((numbering v).symm i))
  dx i := (PhysicalTiles.offset (position ((numbering v).symm i)) (tile ((numbering v).symm i))).1
  dy i := (PhysicalTiles.offset (position ((numbering v).symm i)) (tile ((numbering v).symm i))).2
  fitsX i := (PhysicalTiles.fits v.1 ((numbering v).symm i).val.1 _).1
  fitsY i := (PhysicalTiles.fits v.1 ((numbering v).symm i).val.1 _).2
  walls_compatible i j p q he := PhysicalTiles.walls_compatible v hP hT
    (key_eq ((numbering v).symm i)) (key_eq ((numbering v).symm j)) p q he
  source_owners i j l k he := (numbering v).symm.injective (position_injective
    (PhysicalTiles.slot_owners v hP hT false (key_eq ((numbering v).symm i))
      (key_eq ((numbering v).symm j)) l k he))
  target_owners i j l k he := (numbering v).symm.injective (position_injective
    (PhysicalTiles.slot_owners v hP hT true (key_eq ((numbering v).symm i))
      (key_eq ((numbering v).symm j)) l k he))
  player := (⟨1,by omega⟩,⟨1,by omega⟩)
  player_floor i p _ := PhysicalTiles.player_outside (key_eq ((numbering v).symm i)) p
  player_empty i l := PhysicalTiles.player_outside (key_eq ((numbering v).symm i))
    ((PhysicalTiles.matching (tile ((numbering v).symm i))).source l)

/-- The complete legal unlabelled physical source puzzle, including every auxiliary box and target. -/
noncomputable def puzzle (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] []) : Instance :=
  (atlas v hP hT).puzzle

noncomputable def slotMatching (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] []) :
    SlotMatching (puzzle v hP hT) ((i : Fin (Fintype.card (Index v)))×Labels v i) :=
  (atlas v hP hT).slotMatching

end PushPuzzle.PushFS.Reduction.PhysicalInventory
