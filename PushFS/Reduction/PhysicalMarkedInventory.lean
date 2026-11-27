/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalWallPhases

/-! Exact actual source and goal membership indexed by complete physical glyphs. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction


namespace PhysicalTiles

noncomputable def marks (goal : Bool) (k : Key) : Finset (Cell (piece k).width (piece k).height) :=
  if goal then (piece k).board.goals else (piece k).initial.boxes

def MarkedAt (goal : Bool) (k : Key) (offset p : ℕ×ℕ) : Prop :=
  ∃q : Cell (piece k).width (piece k).height,q∈marks goal k ∧
    (offset.1+q.1.val,offset.2+q.2.val)=p

end PhysicalTiles

namespace PhysicalInventory

open Cslib.Complexity.NCL PhysicalBitmap
set_option maxRecDepth 65536
attribute [local irreducible] Raster.width Raster.height

noncomputable def marks (goal : Bool) (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] []) :
    Finset (Cell (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7)) :=
  if goal then (atlas v hP hT).board.goals else (atlas v hP hT).initial.boxes

/-- Every physical mark belongs to its actual complete source glyph at its literal offset. -/
theorem marked_membership (goal : Bool) (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (p : Cell (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7)) :
    p∈marks goal v hP hT ↔∃i : Index v,
      PhysicalTiles.MarkedAt goal (tile (v := v) i)
        (PhysicalTiles.offset (position (v := v) i) (tile (v := v) i)) (p.1.val,p.2.val) := by
  have hm : p∈marks goal v hP hT ↔∃j : Fin (Fintype.card (Index v)),
      ∃q : Cell ((atlas v hP hT).piece j).width ((atlas v hP hT).piece j).height,
        q∈PhysicalTiles.marks goal (tile (v := v) ((numbering v).symm j)) ∧
          ((atlas v hP hT).embedding j).cells q=p := by
    cases goal
    · exact (atlas v hP hT).mem_boxes_iff p
    · exact (atlas v hP hT).mem_goals_iff p
  apply hm.trans
  constructor
  · rintro ⟨j,q,hq,he⟩
    exact ⟨(numbering v).symm j,q,hq,congrArg (fun p=>(p.1.val,p.2.val)) he⟩
  · rintro ⟨i,q,hq,he⟩
    obtain ⟨j,rfl⟩ := (numbering v).symm.surjective i
    refine ⟨j,q,hq,?_⟩
    apply Prod.ext <;> apply Fin.ext
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he

/-- Reassigning the current source lists reproduces the exact original glyph. -/
theorem rephase_payload_self (v : CellPlan.Source) (i : Index v) :
    PhysicalTiles.rephase (payload v i) v.2.1 v.2.2=tile (v := v) i := by
  have hh := congrArg (fun c=>PhysicalTiles.key (PhysicalTiles.rephaseCode c v.2.1 v.2.2)) (payload_eq v i)
  rw [PhysicalTiles.rephase_cell,PhysicalTiles.key_rephaseCode_some] at hh
  exact Option.some.inj (hh.symm.trans (key_eq (v := v) i))

end PhysicalInventory
end PushPuzzle.PushFS.Reduction
