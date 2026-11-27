/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingInventory

/-! Complete source primitive inventories and their standard dense polynomial-time renderer. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction Gadgets.Wires FiniteRouting
open Cslib.Complexity.NCL Turing.MultiTapeTM

/-- The complete actual primitive table underlying each source macrocell. -/
def table (w : ℕ) (hw : 2 ≤ w) : FiniteAssembly.PrimitiveTable where
  gate := gatePatches w hw
  wire := wirePatches w hw
  stride := tileStride w
  margin := 2*padding w+1

def localCodes (w : ℕ) (c : CellPlan.Code) : List PrimitiveCode :=
  c.elim [] fun code => code.elim (fun g => gateCodes w g.2) (fun q => wireCodes w q.2)

theorem localCodes_fits (w : ℕ) (hw : 2 ≤ w) (c : CellPlan.Code)
    {p : PrimitiveCode} (hp : p ∈ localCodes w c) : PatchFits w (p.patch w hw) := by
  cases c with
  | none => simp [localCodes] at hp
  | some c =>
    cases c with
    | inl g => exact gateCode_fits w hw g.2 hp
    | inr q => exact wireCode_fits w hw q.2 hp

private theorem localPatches_eq (w : ℕ) (hw : 2 ≤ w) (c : CellPlan.Code) :
    (table w hw).localPatches c = (localCodes w c).map (PrimitiveCode.patch w hw) := by
  cases c with
  | none => rfl
  | some c =>
    cases c with
    | inl g => exact gatePatches_eq_map w hw g.2
    | inr q => exact wirePatches_eq_map w hw q.2

/-- Every emitted primitive retains its actual source-grid coordinate. -/
def codes (w : ℕ) (v : CellPlan.Source) : List (GridRouting.Point × PrimitiveCode) :=
  (CellPlan.cells v).flatMap fun q => (localCodes w q.2).map fun p => (q.1,p)

def patch (w : ℕ) (hw : 2 ≤ w) (q : GridRouting.Point × PrimitiveCode) : Bitmap.Patch :=
  Bitmap.instancePatch (q.2.instanceOf w hw)
    (tileStride w*q.1.1+q.2.offsetX w) (tileStride w*q.1.2+q.2.offsetY w)

private theorem patches_eq (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source) :
    (table w hw).patches v = (codes w v).map (patch w hw) := by
  simp only [FiniteAssembly.PrimitiveTable.patches, codes, List.map_flatMap]
  congr 1
  funext q
  unfold FiniteAssembly.PrimitiveTable.entryPatches
  rw [localPatches_eq]
  simp only [List.map_map, Function.comp_def]
  rfl

def width (w : ℕ) (v : CellPlan.Source) : ℕ := tileStride w*Raster.width v.1+2*padding w+1
def height (w : ℕ) (v : CellPlan.Source) : ℕ := tileStride w*Raster.height v.1+2*padding w+1

attribute [local irreducible] width height codes

private theorem entry_bounds (v : CellPlan.Source) {q : GridRouting.Point × CellPlan.Code}
    (hq : q ∈ CellPlan.cells v) : q.1.1 < Raster.width v.1 ∧ q.1.2 < Raster.height v.1 := by
  rcases q with ⟨⟨x,y⟩,c⟩
  simp only [CellPlan.cells, List.mem_flatMap, List.mem_map, List.mem_range, Prod.mk.injEq] at hq
  obtain ⟨y',hy,x',hx,⟨⟨rfl,rfl⟩,_⟩⟩ := hq
  exact ⟨hx,hy⟩

/-- Every literal source primitive fits in the complete physical output rectangle. -/
theorem patch_fits (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    {q : GridRouting.Point × PrimitiveCode} (hq : q ∈ codes w v) :
    (patch w hw q).x+(patch w hw q).bitmap.width ≤ width w v ∧
      (patch w hw q).y+(patch w hw q).bitmap.height ≤ height w v := by
  unfold codes at hq
  obtain ⟨entry,hentry,hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hq
  have hb := entry_bounds v hentry
  have hf := localCodes_fits w hw entry.2 hp
  have hx := Nat.mul_le_mul_left (tileStride w) (Nat.succ_le_of_lt hb.1)
  have hy := Nat.mul_le_mul_left (tileStride w) (Nat.succ_le_of_lt hb.2)
  rw [Nat.mul_succ] at hx hy
  change p.offsetX w+(p.instanceOf w hw).width ≤ tileSide w ∧
    p.offsetY w+(p.instanceOf w hw).height ≤ tileSide w at hf
  dsimp only [patch, Bitmap.instancePatch, Encoding.data, width, height]
  unfold width height
  unfold tileSide at hf
  omega

def Label (w : ℕ) (v : CellPlan.Source) (i : Fin (codes w v).length) : Type :=
  ((codes w v).get i).2.Labels w

instance (w : ℕ) (v : CellPlan.Source) (i : Fin (codes w v).length) : Fintype (Label w v i) :=
  inferInstanceAs (Fintype (((codes w v).get i).2.Labels w))

/-- Every actual source primitive, including all its owned boxes and targets, on one physical board. -/
def inventory (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source) :
    InventoryAssembly (codes w v).length (width w v) (height w v) (Label w v) where
  piece i := (((codes w v).get i).2).instanceOf w hw
  matching i := (((codes w v).get i).2).matching w hw
  dx i := tileStride w*(((codes w v).get i).1).1+(((codes w v).get i).2).offsetX w
  dy i := tileStride w*(((codes w v).get i).1).2+(((codes w v).get i).2).offsetY w
  fitsX i := (patch_fits w hw v (q := (codes w v).get i) (List.get_mem (codes w v) i)).1
  fitsY i := (patch_fits w hw v (q := (codes w v).get i) (List.get_mem (codes w v) i)).2
  player := (⟨0, by unfold width; omega⟩, ⟨0, by unfold height; omega⟩)

private theorem inventory_input (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source) :
    (inventory w hw v).input = (table w hw).input v := by
  have hp : List.ofFn (fun i : Fin (codes w v).length => patch w hw ((codes w v).get i)) =
      (codes w v).map (patch w hw) := by
    simpa only [List.map_ofFn, Function.comp_def] using
      congrArg (List.map (patch w hw)) (List.ofFn_get (codes w v))
  rw [← patches_eq] at hp
  have hi : (inventory w hw v).input =
      ⟨width w v,height w v,0,0,
        List.ofFn fun i : Fin (codes w v).length => patch w hw ((codes w v).get i)⟩ := rfl
  have ht : (table w hw).input v =
      ⟨width w v,height w v,0,0,(table w hw).patches v⟩ := by
    unfold width height
    dsimp only [FiniteAssembly.PrimitiveTable.input, table]
    simp only [Nat.add_assoc]
  exact hi.trans ((congrArg (Bitmap.Input.mk (width w v) (height w v) 0 0) hp).trans ht.symm)

def puzzle (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (ha : (inventory w hw v).Admissible) : PushFS.Instance := (inventory w hw v).puzzle ha

theorem puzzle_data (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (ha : (inventory w hw v).Admissible) :
    Encoding.data (puzzle w hw v ha) = (table w hw).data v :=
  ((inventory w hw v).data_eq ha).trans (congrArg Bitmap.emit (inventory_input w hw v))

/-- The complete actual source-primitive bitmap uses the standard polynomial-time machine model. -/
theorem data_polyTime (w : ℕ) (hw : 2 ≤ w) :
    ComputableInPolyTime (table w hw).data CellPlan.encSource Encoding.encData :=
  (table w hw).data_polyTime

end PushPuzzle.PushS.FiniteSourceInventory
