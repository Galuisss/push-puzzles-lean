/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourcePhases

/-! Canonical configurations change the actual boxes while retaining every target. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting Gadgets.Wires
open Cslib.Complexity.NCL

attribute [local irreducible] Raster.width Raster.height Raster.vertexAt Raster.owner Raster.wireAt

private theorem localCodes_cell_erase_initial (w : ℕ) (word : Word) (a a' b : List Bool)
    (p : GridRouting.Point) :
    (localCodes w (CellPlan.cell ((word,(a,b)),p))).map PrimitiveCode.eraseInitial =
      (localCodes w (CellPlan.cell ((word,(a',b)),p))).map PrimitiveCode.eraseInitial := by
  cases hv : Raster.vertexAt (word,p) with
  | some v =>
    simp only [CellPlan.cell,hv,Option.elim_some,localCodes,Sum.elim_inl,gateTileState]
    exact gateCodes_erase_initial _ _ _ _ _ _ _ _
  | none =>
    simp only [CellPlan.cell,hv,Option.elim_none,CellPlan.ordinary]
    cases Raster.owner (word,p) with
    | none => simp only [Option.elim_none,localCodes,List.map_nil]
    | some e =>
      simp only [Option.elim_some,CellPlan.wireData]
      cases Raster.wireAt (word,(e,p)) with
      | none => simp only [Option.map_none,localCodes,Option.elim_none,List.map_nil]
      | some kind =>
        simp only [Option.map_some,localCodes,Option.elim_some,Sum.elim_inr]
        exact wireCodes_erase_initial _ _ _ _ _

def eraseInitialCode (q : GridRouting.Point × PrimitiveCode) : GridRouting.Point × PrimitiveCode :=
  (q.1,q.2.eraseInitial)

private theorem codes_erase_initial (w : ℕ) (word : Word) (a a' b : List Bool) :
    (codes w (word,(a,b))).map eraseInitialCode = (codes w (word,(a',b))).map eraseInitialCode := by
  simp only [codes,CellPlan.cells,List.map_flatMap,List.flatMap_assoc,List.flatMap_map,List.map_map,
    Function.comp_def,eraseInitialCode]
  congr 1
  funext y
  congr 1
  funext x
  have h := congrArg (List.map (fun c => ((x,y),c))) (localCodes_cell_erase_initial w word a a' b (x,y))
  simpa only [List.map_map,Function.comp_def] using h

attribute [local irreducible] codes

def entryTargetPoints (w : ℕ) (hw : 2 ≤ w) (q : GridRouting.Point × PrimitiveCode) : Finset (ℕ × ℕ) :=
  (q.2.targetPoints w hw).image fun p => (tileStride w*q.1.1+p.1,tileStride w*q.1.2+p.2)

def targetCloud (w : ℕ) (hw : 2 ≤ w) (entries : List (GridRouting.Point × PrimitiveCode)) : Finset (ℕ × ℕ) :=
  entries.foldr (fun q acc => entryTargetPoints w hw q ∪ acc) ∅

private theorem mem_targetCloud (w : ℕ) (hw : 2 ≤ w) (entries : List (GridRouting.Point × PrimitiveCode))
    (p : ℕ × ℕ) : p ∈ targetCloud w hw entries ↔ ∃ q ∈ entries, p ∈ entryTargetPoints w hw q := by
  induction entries with
  | nil => simp [targetCloud]
  | cons q qs ih =>
    change p ∈ entryTargetPoints w hw q ∪ targetCloud w hw qs ↔ _
    rw [Finset.mem_union,ih]
    simp only [List.mem_cons,or_and_right,exists_or,exists_eq_left]

private theorem entryTargetPoints_erase (w : ℕ) (hw : 2 ≤ w)
    (q : GridRouting.Point × PrimitiveCode) :
    entryTargetPoints w hw (eraseInitialCode q) = entryTargetPoints w hw q := by
  unfold entryTargetPoints eraseInitialCode
  rw [PrimitiveCode.eraseInitial_targetPoints]

private theorem targetCloud_erase (w : ℕ) (hw : 2 ≤ w) (entries : List (GridRouting.Point × PrimitiveCode)) :
    targetCloud w hw (entries.map eraseInitialCode) = targetCloud w hw entries := by
  induction entries with
  | nil => rfl
  | cons q qs ih =>
    change entryTargetPoints w hw (eraseInitialCode q) ∪ targetCloud w hw (qs.map eraseInitialCode) =
      entryTargetPoints w hw q ∪ targetCloud w hw qs
    rw [entryTargetPoints_erase,ih]

private theorem targetCloud_rephase (w : ℕ) (hw : 2 ≤ w) (word : Word) (a a' b : List Bool) :
    targetCloud w hw (codes w (word,(a,b))) = targetCloud w hw (codes w (word,(a',b))) := by
  have h := congrArg (targetCloud w hw) (codes_erase_initial w word a a' b)
  simpa only [targetCloud_erase] using h

private theorem targets_cloud (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source) :
    ((inventory w hw v).board.goals.image coordinates) = targetCloud w hw (codes w v) := by
  ext p
  rw [mem_targetCloud]
  constructor
  · intro hp
    obtain ⟨p',hp',rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨i,q,hq,rfl⟩ := ((inventory w hw v).mem_goals_iff p').mp hp'
    refine ⟨(codes w v).get i,List.get_mem _ _,?_⟩
    refine Finset.mem_image.mpr ⟨((codes w v).get i).2.world w hw q,
      Finset.mem_image.mpr ⟨q,hq,rfl⟩,?_⟩
    exact (inventory_coordinates w hw v i q).symm
  · rintro ⟨entry,hentry,hp⟩
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hentry
    obtain ⟨p',hp',rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp'
    refine Finset.mem_image.mpr ⟨(inventory w hw v).embedding i |>.cells q,
      ((inventory w hw v).mem_goals_iff _).mpr ⟨i,q,hq,rfl⟩,?_⟩
    exact inventory_coordinates w hw v i q

/-- Every canonical orientation uses exactly the target set of the fixed final source configuration. -/
theorem targets_rephase (w : ℕ) (hw : 2 ≤ w) (word : Word) (a a' b : List Bool) :
    (inventory w hw (word,(a,b))).board.goals = (inventory w hw (word,(a',b))).board.goals := by
  have hc : Function.Injective (coordinates :
      Cell (width w (word,(a,b))) (height w (word,(a,b))) → ℕ × ℕ) := by
    intro p q he
    apply Prod.ext <;> apply Fin.ext
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he
  apply Finset.image_injective hc
  exact (targets_cloud w hw (word,(a,b))).trans
    ((targetCloud_rephase w hw word a a' b).trans (targets_cloud w hw (word,(a',b))).symm)

end PushPuzzle.PushS.FiniteSourceInventory
