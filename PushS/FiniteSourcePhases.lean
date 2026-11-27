/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FinitePrimitivePhases
public import PushS.FiniteSourceInventory

/-! The complete actual source geometry is independent of the initial and target orientation lists. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting Gadgets.Wires
open Cslib.Complexity.NCL

attribute [local irreducible] Raster.width Raster.height Raster.vertexAt Raster.owner Raster.wireAt

private theorem localCodes_cell_erase_phases (w : ℕ) (word : Word) (a b a' b' : List Bool)
    (p : GridRouting.Point) :
    (localCodes w (CellPlan.cell ((word,(a,b)),p))).map PrimitiveCode.erasePhases =
      (localCodes w (CellPlan.cell ((word,(a',b')),p))).map PrimitiveCode.erasePhases := by
  cases hv : Raster.vertexAt (word,p) with
  | some v =>
    simp only [CellPlan.cell,hv,Option.elim_some,localCodes,Sum.elim_inl,gateTileState]
    exact gateCodes_erase_phases _ _ _ _ _ _ _ _ _
  | none =>
    simp only [CellPlan.cell,hv,Option.elim_none,CellPlan.ordinary]
    cases ho : Raster.owner (word,p) with
    | none => simp only [Option.elim_none,localCodes,List.map_nil]
    | some e =>
      simp only [Option.elim_some,CellPlan.wireData]
      cases hk : Raster.wireAt (word,(e,p)) with
      | none => simp only [Option.map_none,localCodes,Option.elim_none,List.map_nil]
      | some kind =>
        simp only [Option.map_some,localCodes,Option.elim_some,Sum.elim_inr]
        exact wireCodes_erase_phases _ _ _ _ _ _

def eraseCode (q : GridRouting.Point × PrimitiveCode) : GridRouting.Point × PrimitiveCode :=
  (q.1,q.2.erasePhases)

/-- Every routed primitive keeps its position, shape, orientation and ownership through rephasing. -/
private theorem codes_erase_phases (w : ℕ) (word : Word) (a b a' b' : List Bool) :
    (codes w (word,(a,b))).map eraseCode = (codes w (word,(a',b'))).map eraseCode := by
  simp only [codes,CellPlan.cells,List.map_flatMap,List.flatMap_assoc,List.flatMap_map,List.map_map,
    Function.comp_def,eraseCode]
  congr 1
  funext y
  congr 1
  funext x
  have h := congrArg (List.map (fun c => ((x,y),c))) (localCodes_cell_erase_phases w word a b a' b' (x,y))
  simpa only [List.map_map,Function.comp_def] using h

attribute [local irreducible] codes

def entryWallPoints (w : ℕ) (hw : 2 ≤ w) (q : GridRouting.Point × PrimitiveCode) : Finset (ℕ × ℕ) :=
  (q.2.wallPoints w hw).image fun p => (tileStride w*q.1.1+p.1,tileStride w*q.1.2+p.2)

def wallCloud (w : ℕ) (hw : 2 ≤ w) (entries : List (GridRouting.Point × PrimitiveCode)) : Finset (ℕ × ℕ) :=
  entries.foldr (fun q acc => entryWallPoints w hw q ∪ acc) ∅

private theorem mem_wallCloud (w : ℕ) (hw : 2 ≤ w) (entries : List (GridRouting.Point × PrimitiveCode))
    (p : ℕ × ℕ) : p ∈ wallCloud w hw entries ↔ ∃ q ∈ entries, p ∈ entryWallPoints w hw q := by
  induction entries with
  | nil => simp [wallCloud]
  | cons q qs ih =>
    change p ∈ entryWallPoints w hw q ∪ wallCloud w hw qs ↔ _
    rw [Finset.mem_union,ih]
    simp only [List.mem_cons,or_and_right,exists_or,exists_eq_left]

private theorem entryWallPoints_erase (w : ℕ) (hw : 2 ≤ w) (q : GridRouting.Point × PrimitiveCode) :
    entryWallPoints w hw (eraseCode q) = entryWallPoints w hw q := by
  unfold entryWallPoints eraseCode
  rw [PrimitiveCode.erasePhases_wallPoints]

private theorem wallCloud_erase (w : ℕ) (hw : 2 ≤ w) (entries : List (GridRouting.Point × PrimitiveCode)) :
    wallCloud w hw (entries.map eraseCode) = wallCloud w hw entries := by
  induction entries with
  | nil => rfl
  | cons q qs ih =>
    change entryWallPoints w hw (eraseCode q) ∪ wallCloud w hw (qs.map eraseCode) =
      entryWallPoints w hw q ∪ wallCloud w hw qs
    rw [entryWallPoints_erase,ih]

private theorem wallCloud_rephase (w : ℕ) (hw : 2 ≤ w) (word : Word) (a b a' b' : List Bool) :
    wallCloud w hw (codes w (word,(a,b))) = wallCloud w hw (codes w (word,(a',b'))) := by
  have h := congrArg (wallCloud w hw) (codes_erase_phases w word a b a' b')
  simpa only [wallCloud_erase] using h

theorem inventory_coordinates (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (i : Fin (codes w v).length)
    (p : Cell (((codes w v).get i).2.instanceOf w hw).width (((codes w v).get i).2.instanceOf w hw).height) :
    coordinates ((inventory w hw v).embedding i |>.cells p) =
      (tileStride w*((codes w v).get i).1.1+(((codes w v).get i).2.world w hw p).1,
       tileStride w*((codes w v).get i).1.2+(((codes w v).get i).2.world w hw p).2) := by
  apply Prod.ext
  · change (tileStride w*((codes w v).get i).1.1+((codes w v).get i).2.offsetX w)+p.1.val =
      tileStride w*((codes w v).get i).1.1+(((codes w v).get i).2.offsetX w+p.1.val)
    exact Nat.add_assoc _ _ _
  · change (tileStride w*((codes w v).get i).1.2+((codes w v).get i).2.offsetY w)+p.2.val =
      tileStride w*((codes w v).get i).1.2+(((codes w v).get i).2.offsetY w+p.2.val)
    exact Nat.add_assoc _ _ _

/-- The coordinate cloud is exactly the complete semantic inventory's actual wall union. -/
private theorem walls_cloud (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source) :
    ((inventory w hw v).walls.image coordinates) = wallCloud w hw (codes w v) := by
  ext p
  rw [mem_wallCloud]
  constructor
  · intro hp
    obtain ⟨p',hp',rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨i,_,hpi⟩ := Finset.mem_biUnion.mp hp'
    obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hpi
    refine ⟨(codes w v).get i,List.get_mem _ _,?_⟩
    refine Finset.mem_image.mpr ⟨((codes w v).get i).2.world w hw q,
      Finset.mem_image.mpr ⟨q,hq,rfl⟩,?_⟩
    exact (inventory_coordinates w hw v i q).symm
  · rintro ⟨entry,hentry,hp⟩
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hentry
    obtain ⟨p',hp',rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp'
    refine Finset.mem_image.mpr ⟨(inventory w hw v).embedding i |>.cells q,
      Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_map.mpr ⟨q,hq,rfl⟩⟩,?_⟩
    exact inventory_coordinates w hw v i q

/-- Changing either orientation list retains exactly the same complete physical wall set. -/
theorem walls_rephase (w : ℕ) (hw : 2 ≤ w) (word : Word) (a b a' b' : List Bool) :
    (inventory w hw (word,(a,b))).walls = (inventory w hw (word,(a',b'))).walls := by
  have hc : Function.Injective (coordinates :
      Cell (width w (word,(a,b))) (height w (word,(a,b))) → ℕ × ℕ) := by
    intro p q he
    apply Prod.ext <;> apply Fin.ext
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he
  apply Finset.image_injective hc
  exact (walls_cloud w hw (word,(a,b))).trans
    ((wallCloud_rephase w hw word a b a' b').trans (walls_cloud w hw (word,(a',b'))).symm)

end PushPuzzle.PushS.FiniteSourceInventory
