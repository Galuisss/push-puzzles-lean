/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteNormalPhases

/-! The actual initial physical inventory is independent of the selected final orientation. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction Gadgets.Wires

/-- Erase only target phases while preserving each actual initial inventory and its geometry. -/
def PrimitiveCode.eraseTarget : PrimitiveCode → PrimitiveCode
  | .core g => .core {g with core := {g.core with target := ⟨false,false,false⟩}}
  | .line c => .line {c with target := false}
  | .turn c => .turn {c with target := false}

/-- Literal world coordinates of the complete actual initial primitive inventory. -/
def PrimitiveCode.initialPoints (w : ℕ) (hw : 2 ≤ w) (c : PrimitiveCode) : Finset (ℕ × ℕ) :=
  (c.instanceOf w hw).initial.boxes.image (c.world w hw)

private theorem PrimitiveCode.eraseTarget_initialPoints (w : ℕ) (hw : 2 ≤ w) (c : PrimitiveCode) :
    c.eraseTarget.initialPoints w hw = c.initialPoints w hw := by
  cases c with
  | core g =>
    rcases g with ⟨⟨kind,s,t⟩,incoming,pattern,rotation⟩
    cases kind <;> rfl
  | line c => rfl
  | turn c => rfl

private theorem pathCodes_erase_target (segments : List Segment)
    (initialSide targetSide keepEndpoint a b b' : Bool) :
    (pathCodes segments initialSide targetSide keepEndpoint a b).map PrimitiveCode.eraseTarget =
      (pathCodes segments initialSide targetSide keepEndpoint a b').map PrimitiveCode.eraseTarget := by
  simp only [pathCodes,List.map_flatMap,List.map_append]
  congr 1
  funext i
  split_ifs <;> rfl

private theorem gateCodes_erase_target (w : ℕ) (kind : Bool)
    (incoming : PushFS.Gadgets.Gates.Signals)
    (pattern rotation : Fin 3) (a b b' : PushFS.Gadgets.Gates.Signals) :
    (gateCodes w ⟨⟨kind,a,b⟩,incoming,pattern,rotation⟩).map PrimitiveCode.eraseTarget =
      (gateCodes w ⟨⟨kind,a,b'⟩,incoming,pattern,rotation⟩).map PrimitiveCode.eraseTarget := by
  simp only [gateCodes,List.map_cons,List.map_flatMap]
  congr 1
  congr 1
  funext role
  exact pathCodes_erase_target _ _ _ _ _ _ _

private theorem wireCodes_erase_target (w : ℕ) (kind : Catalog.Kind) (a b b' : Bool) :
    (wireCodes w (kind,a,b)).map PrimitiveCode.eraseTarget =
      (wireCodes w (kind,a,b')).map PrimitiveCode.eraseTarget :=
  pathCodes_erase_target _ _ _ _ _ _ _

end PushPuzzle.PushS.FiniteRouting

namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting Gadgets.Wires
open Cslib.Complexity.NCL

attribute [local irreducible] Raster.width Raster.height Raster.vertexAt Raster.owner Raster.wireAt

private theorem localCodes_cell_erase_target (w : ℕ) (word : Word)
    (target nextTarget current : List Bool) (p : GridRouting.Point) :
    (localCodes w (CellPlan.cell ((word,(current,target)),p))).map PrimitiveCode.eraseTarget =
      (localCodes w (CellPlan.cell ((word,(current,nextTarget)),p))).map PrimitiveCode.eraseTarget := by
  cases hv : Raster.vertexAt (word,p) with
  | some v =>
    simp only [CellPlan.cell,hv,Option.elim_some,localCodes,Sum.elim_inl,gateTileState]
    exact gateCodes_erase_target _ _ _ _ _ _ _ _
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
        exact wireCodes_erase_target _ _ _ _ _

def eraseTargetCode (q : GridRouting.Point × PrimitiveCode) : GridRouting.Point × PrimitiveCode :=
  (q.1,q.2.eraseTarget)

private theorem codes_erase_target (w : ℕ) (word : Word) (target nextTarget current : List Bool) :
    (codes w (word,(current,target))).map eraseTargetCode = (codes w (word,(current,nextTarget))).map eraseTargetCode := by
  simp only [codes,CellPlan.cells,List.map_flatMap,List.flatMap_assoc,List.flatMap_map,List.map_map,
    Function.comp_def,eraseTargetCode]
  congr 1
  funext y
  congr 1
  funext x
  have h := congrArg (List.map (fun c => ((x,y),c))) (localCodes_cell_erase_target w word target nextTarget current (x,y))
  simpa only [List.map_map,Function.comp_def] using h

attribute [local irreducible] codes

def entryInitialPoints (w : ℕ) (hw : 2 ≤ w) (q : GridRouting.Point × PrimitiveCode) : Finset (ℕ × ℕ) :=
  (q.2.initialPoints w hw).image fun p => (tileStride w*q.1.1+p.1,tileStride w*q.1.2+p.2)

def initialCloud (w : ℕ) (hw : 2 ≤ w) (entries : List (GridRouting.Point × PrimitiveCode)) : Finset (ℕ × ℕ) :=
  entries.foldr (fun q acc => entryInitialPoints w hw q ∪ acc) ∅

private theorem mem_initialCloud (w : ℕ) (hw : 2 ≤ w) (entries : List (GridRouting.Point × PrimitiveCode))
    (p : ℕ × ℕ) : p ∈ initialCloud w hw entries ↔ ∃ q ∈ entries, p ∈ entryInitialPoints w hw q := by
  induction entries with
  | nil => simp [initialCloud]
  | cons q qs ih =>
    change p ∈ entryInitialPoints w hw q ∪ initialCloud w hw qs ↔ _
    rw [Finset.mem_union,ih]
    simp only [List.mem_cons,or_and_right,exists_or,exists_eq_left]

private theorem entryInitialPoints_erase (w : ℕ) (hw : 2 ≤ w)
    (q : GridRouting.Point × PrimitiveCode) :
    entryInitialPoints w hw (eraseTargetCode q) = entryInitialPoints w hw q := by
  unfold entryInitialPoints eraseTargetCode
  rw [PrimitiveCode.eraseTarget_initialPoints]

private theorem initialCloud_erase (w : ℕ) (hw : 2 ≤ w) (entries : List (GridRouting.Point × PrimitiveCode)) :
    initialCloud w hw (entries.map eraseTargetCode) = initialCloud w hw entries := by
  induction entries with
  | nil => rfl
  | cons q qs ih =>
    change entryInitialPoints w hw (eraseTargetCode q) ∪ initialCloud w hw (qs.map eraseTargetCode) =
      entryInitialPoints w hw q ∪ initialCloud w hw qs
    rw [entryInitialPoints_erase,ih]

private theorem initialCloud_rephase (w : ℕ) (hw : 2 ≤ w) (word : Word)
    (target nextTarget current : List Bool) :
    initialCloud w hw (codes w (word,(current,target))) = initialCloud w hw (codes w (word,(current,nextTarget))) := by
  have h := congrArg (initialCloud w hw) (codes_erase_target w word target nextTarget current)
  simpa only [initialCloud_erase] using h

private theorem initials_cloud (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source) :
    ((inventory w hw v).initial.boxes.image coordinates) = initialCloud w hw (codes w v) := by
  ext p
  rw [mem_initialCloud]
  constructor
  · intro hp
    obtain ⟨p',hp',rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨i,q,hq,rfl⟩ := ((inventory w hw v).mem_boxes_iff p').mp hp'
    refine ⟨(codes w v).get i,List.get_mem _ _,?_⟩
    refine Finset.mem_image.mpr ⟨((codes w v).get i).2.world w hw q,
      Finset.mem_image.mpr ⟨q,hq,rfl⟩,?_⟩
    exact (inventory_coordinates w hw v i q).symm
  · rintro ⟨entry,hentry,hp⟩
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hentry
    obtain ⟨p',hp',rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp'
    refine Finset.mem_image.mpr ⟨(inventory w hw v).embedding i |>.cells q,
      ((inventory w hw v).mem_boxes_iff _).mpr ⟨i,q,hq,rfl⟩,?_⟩
    exact inventory_coordinates w hw v i q

/-- Changing the selected target leaves the complete actual initial inventory unchanged. -/
theorem initials_rephase (w : ℕ) (hw : 2 ≤ w) (word : Word) (target nextTarget current : List Bool) :
    (inventory w hw (word,(current,target))).initial.boxes = (inventory w hw (word,(current,nextTarget))).initial.boxes := by
  have hc : Function.Injective (coordinates :
      Cell (width w (word,(current,target))) (height w (word,(current,target))) → ℕ × ℕ) := by
    intro p q he
    apply Prod.ext <;> apply Fin.ext
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he
  apply Finset.image_injective hc
  exact (initials_cloud w hw (word,(current,target))).trans
    ((initialCloud_rephase w hw word target nextTarget current).trans (initials_cloud w hw (word,(current,nextTarget))).symm)

end PushPuzzle.PushS.FiniteSourceInventory
