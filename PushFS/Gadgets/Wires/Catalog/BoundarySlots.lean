/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.SlotCoordinates
public import PushFS.Gadgets.Wires.Catalog.SlotBounds
public import PushFS.Gadgets.Wires.Catalog.BoundaryWalls

/-! Complete physical identity classification in every five-cell ordinary-cell face. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog

set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

/-- True source/target supports and actual gap-two separation determine every outer-frame canonical point. -/
theorem boundary_point (k : Kind) (a : Bool) (f : Face) (p : Cell)
    (hb : SlotRegion k a p) (hf : InFace f p)
    (hfirst : ∀d, ¬Adjacent d (firstPoint k a) p)
    (hlast : ∀d, ¬Adjacent d p (lastPoint k a)) :
    (f=sourceFace k ∧(p=firstPoint k a ∨a=false ∧p=secondPoint k a)) ∨
      (f=targetFace k ∧p=lastPoint k a) := by
  have hfe:=hfirst .east
  have hfw:=hfirst .west
  have hfn:=hfirst .north
  have hfs:=hfirst .south
  have hle:=hlast .east
  have hlw:=hlast .west
  have hln:=hlast .north
  have hls:=hlast .south
  cases k <;> cases f <;> cases a <;>
    simp_all [SlotRegion,SlotBounds,InFace,firstPoint,secondPoint,lastPoint,
      sourceFace,targetFace,Adjacent,Prod.ext_iff,Fin.ext_iff,width,height] <;> omega

/-- Actual injective canonical inventories are classified by their exact endpoints, coordinate bounds and genuine pair separation. -/
private theorem embedding_boundary (k : Kind) (a : Bool) (f : Face) (N :
    ((_i : Fin 1)×Labels k)↪Cell)
    (bounds : ∀l, SlotRegion k a (N l))
    (first : N (firstLabel k)=firstPoint k a) (second : N (secondLabel k)=secondPoint k a)
    (last : N (lastLabel k)=lastPoint k a)
    (sparse : ∀i j d, ¬Adjacent d (N i) (N j)) (l : (_i : Fin 1)×Labels k) (hf : InFace f (N l)) :
    (f=sourceFace k ∧(l=firstLabel k ∨a=false ∧l=secondLabel k)) ∨
      (f=targetFace k ∧l=lastLabel k) := by
  have hs d : ¬Adjacent d (firstPoint k a) (N l) := by
    rw [←first]
    exact sparse _ _ d
  have ht d : ¬Adjacent d (N l) (lastPoint k a) := by
    rw [←last]
    exact sparse _ _ d
  have hh:=boundary_point k a f _ (bounds l) hf hs ht
  rcases hh with ⟨hf,hh|⟨ha,hh⟩⟩|⟨hf,hh⟩
  · exact Or.inl ⟨hf,Or.inl (N.injective (hh.trans first.symm))⟩
  · exact Or.inl ⟨hf,Or.inr ⟨ha,N.injective (hh.trans second.symm)⟩⟩
  · exact Or.inr ⟨hf,N.injective (hh.trans last.symm)⟩

/-- Every actual canonical source label in the full five-cell frame is the true first, false-phase second, or true last identity. -/
theorem source_boundary (k : Kind) (a b : Bool) (f : Face) (l : (_i : Fin 1)×Labels k)
    (hf : InFace f ((slotMatching k a b).source l)) :
    (f=sourceFace k ∧(l=firstLabel k ∨a=false ∧l=secondLabel k)) ∨
      (f=targetFace k ∧l=lastLabel k) :=
  embedding_boundary k a f (slotMatching k a b).source (source_bounds k a b)
    (source_first k a b) (source_second k a b) (source_last k a b) (source_sparse k a b) l hf

/-- Exact canonical physical goals have the same full-frame identity classification at their own phase. -/
theorem target_boundary (k : Kind) (a b : Bool) (f : Face) (l : (_i : Fin 1)×Labels k)
    (hf : InFace f ((slotMatching k a b).target l)) :
    (f=sourceFace k ∧(l=firstLabel k ∨b=false ∧l=secondLabel k)) ∨
      (f=targetFace k ∧l=lastLabel k) :=
  embedding_boundary k b f (slotMatching k a b).target (target_bounds k a b)
    (target_first k a b) (target_second k a b) (target_last k a b) (target_sparse k a b) l hf

/-- The narrower four-cell face excludes the false-phase second box. -/
def InNarrowFace : Face→Cell→Prop
  | .west,p=>p.1.val<4
  | .east,p=>200001≤p.1.val
  | .north,p=>p.2.val<4
  | .south,p=>198062≤p.2.val

instance (f : Face) (p : Cell) : Decidable (InNarrowFace f p) := by
  cases f <;> dsimp [InNarrowFace] <;> infer_instance

end PushPuzzle.PushFS.Gadgets.Wires.Catalog
