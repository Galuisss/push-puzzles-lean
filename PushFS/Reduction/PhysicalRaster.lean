/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalInventory

/-! Exact equality of the actual complete semantic source puzzle and its machine-rendered bitmap. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory


open Cslib.Complexity.NCL PhysicalBitmap

private theorem patchList_mem (e : PhysicalBitmap.Entry) (p : Bitmap.Patch) :
    p∈PhysicalBitmap.patchList e ↔PhysicalBitmap.patch e=some p := by
  cases hp : PhysicalBitmap.patch e <;> simp [PhysicalBitmap.patchList,hp,eq_comm]

private theorem patch_some (p : GridRouting.Point) (c : CellPlan.Code) (t : Bitmap.Patch) :
    PhysicalBitmap.patch (p,c)=some t ↔∃k : PhysicalTiles.Key,PhysicalTiles.key c=some k ∧
      Bitmap.instancePatch (PhysicalTiles.piece k) (PhysicalTiles.offset p k).1 (PhysicalTiles.offset p k).2=t := by
  rcases c with _| (g|w)
  · constructor
    · intro h; cases h
    · rintro ⟨k,h,_⟩; cases h
  · rw [PhysicalBitmap.patch_gate,PhysicalTiles.gate_patch]
    constructor
    · intro h
      exact ⟨.inl g.2,rfl,Option.some.inj h⟩
    · rintro ⟨k,hk,he⟩
      cases hk
      exact congrArg some he
  · rw [PhysicalBitmap.patch_wire,PhysicalTiles.wire_patch]
    constructor
    · intro h
      exact ⟨.inr w.2,rfl,Option.some.inj h⟩
    · rintro ⟨k,hk,he⟩
      cases hk
      exact congrArg some he

private theorem cells_mem (v : CellPlan.Source) (p : GridRouting.Point) (c : CellPlan.Code) :
    (p,c)∈CellPlan.cells v ↔p.1<Raster.width v.1 ∧p.2<Raster.height v.1 ∧CellPlan.cell (v,p)=c := by
  rcases p with ⟨x,y⟩
  simp only [CellPlan.cells,List.mem_flatMap,List.mem_map,List.mem_range,Prod.mk.injEq]
  constructor
  · rintro ⟨y',hy,x',hx,⟨⟨rfl,rfl⟩,hc⟩⟩
    exact ⟨hx,hy,hc⟩
  · rintro ⟨hx,hy,hc⟩
    exact ⟨y,hy,x,hx,⟨⟨rfl,rfl⟩,hc⟩⟩

private theorem patches_mem (v : CellPlan.Source) (p : Bitmap.Patch) :
    p∈PhysicalBitmap.patches v ↔∃i : Index v,
      Bitmap.instancePatch (PhysicalTiles.piece (tile i))
        (PhysicalTiles.offset (position i) (tile i)).1 (PhysicalTiles.offset (position i) (tile i)).2=p := by
  simp only [PhysicalBitmap.patches,List.mem_flatMap]
  constructor
  · rintro ⟨⟨⟨x,y⟩,c⟩,hc,hp⟩
    obtain ⟨hx,hy,hcell⟩ := (cells_mem v (x,y) c).mp hc
    obtain ⟨k,hk,he⟩ := (patch_some (x,y) c p).mp ((patchList_mem ((x,y),c) p).mp hp)
    let i : Index v := ⟨((⟨x,hx⟩,⟨y,hy⟩),k),by rw [hcell]; exact hk⟩
    exact ⟨i,he⟩
  · rintro ⟨i,he⟩
    refine ⟨(position i,CellPlan.cell (v,position i)),?_,?_⟩
    · exact (cells_mem v (position i) _).mpr ⟨i.val.1.1.isLt,i.val.1.2.isLt,rfl⟩
    · exact (patchList_mem _ p).mpr ((patch_some _ _ p).mpr ⟨tile i,key_eq i,he⟩)

theorem atlas_patch (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (i : Fin (Fintype.card (Index v))) :
    Bitmap.instancePatch ((atlas v hP hT).piece i) ((atlas v hP hT).dx i) ((atlas v hP hT).dy i)=
      Bitmap.instancePatch (PhysicalTiles.piece (tile ((numbering v).symm i)))
        (PhysicalTiles.offset (position ((numbering v).symm i)) (tile ((numbering v).symm i))).1
        (PhysicalTiles.offset (position ((numbering v).symm i)) (tile ((numbering v).symm i))).2 := rfl

private theorem atlas_patch_membership (v : CellPlan.Source) (hP : v.1.checkPlane=true)
    (hT : v.1.WellTyped [] [])
    (p : Bitmap.Patch) : p∈(atlas v hP hT).input.patches ↔p∈(PhysicalBitmap.input v).patches := by
  change _↔p∈PhysicalBitmap.patches v
  rw [patches_mem]
  simp only [StorageAtlas.input,List.mem_ofFn,atlas_patch]
  constructor
  · rintro ⟨i,he⟩
    exact ⟨(numbering v).symm i,he⟩
  · rintro ⟨i,he⟩
    refine ⟨numbering v i,?_⟩
    rw [Equiv.symm_apply_apply]
    exact he

/-- Every actual wall, auxiliary box, goal and the exterior player has exactly its emitted machine flag. -/
theorem data_eq (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] []) :
    Encoding.data (puzzle v hP hT)=PhysicalBitmap.data v :=
  (atlas v hP hT).data_eq.trans (Bitmap.emit_ext (atlas v hP hT).input (PhysicalBitmap.input v)
    rfl rfl rfl rfl (atlas_patch_membership v hP hT))

end PushPuzzle.PushFS.Reduction.PhysicalInventory
