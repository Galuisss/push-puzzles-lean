/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.PhaseWalls
public import PushFS.Gadgets.Wires.Catalog.Endpoints
public import PushFS.Gadgets.Wires.Catalog.Collars
public import PushFS.WallCongruence

/-! Exact canonical endpoint phases and the interior of every physical port collar lie in their true static SCC. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog

open Soundness
set_option maxRecDepth 65536
set_option maxHeartbeats 100000
attribute [local irreducible] Reduction.StorageAtlas.initial Reduction.StorageAtlas.board

private theorem matching_component {J : Instance} {A : Type} [Fintype A]
    (N : SlotMatching J A) (l : A) (p q : PushFS.Cell J.width J.height)
    (hs : N.source l=p) (ht : N.target l=q) : SameComponent J.board p q := hs ▸ht ▸N.connected l

theorem endpoint_component (k : Kind) (a b c z : Bool) (last : Bool) :
    @SameComponent width height (puzzle k a b).board
      (if last then lastPoint k c else firstPoint k c)
      (if last then lastPoint k z else firstPoint k z) := by
  cases last
  · have hp : @SameComponent width height (puzzle k c z).board (firstPoint k c) (firstPoint k z) :=
      matching_component (J:=puzzle k c z) (slotMatching k c z) (firstLabel k) (firstPoint k c) (firstPoint k z) (source_first k c z) (target_first k c z)
    exact SameComponent.reboard (w:=width) (h:=height) (B:=(puzzle k c z).board) (B':=(puzzle k a b).board) hp (puzzle_walls_eq k c z a b)
  · have hp : @SameComponent width height (puzzle k c z).board (lastPoint k c) (lastPoint k z) :=
      matching_component (J:=puzzle k c z) (slotMatching k c z) (lastLabel k) (lastPoint k c) (lastPoint k z) (source_last k c z) (target_last k c z)
    exact SameComponent.reboard (w:=width) (h:=height) (B:=(puzzle k c z).board) (B':=(puzzle k a b).board) hp (puzzle_walls_eq k c z a b)

def faceEmbedding : Face→GridEmbedding 5 21 width height
  | .west=>GridEmbedding.translate 0 99023 (by change _≤200005; omega) (by change _≤198066; omega)
  | .east=>GridEmbedding.translate 200000 99023 (by change _≤200005; omega) (by change _≤198066; omega)
  | .north=>(GridIsometry.clockwise 5 21).embedding.trans (GridEmbedding.translate 99992 0 (by change _≤200005; omega) (by change _≤198066; omega))
  | .south=>(GridIsometry.clockwise 5 21).embedding.trans (GridEmbedding.translate 99992 198061 (by change _≤200005; omega) (by change _≤198066; omega))

private theorem faceEmbedding_cells (f : Face) (p : PushFS.Cell 5 21) :
    (faceEmbedding f).cells p=faceCell f p := by
  cases f <;> apply Prod.ext <;> apply Fin.ext
  all_goals simp [faceEmbedding,faceCell,GridEmbedding.translate,GridEmbedding.trans,GridIsometry.embedding,
    GridIsometry.clockwise,GridIsometry.trans,GridIsometry.transpose,GridIsometry.reflectX,Fin.revPerm,Fin.rev]

def faceBoard : Board 5 21 := ⟨Finset.univ.filter (fun p=>p.2.val=11 ∨p.2.val=12),∅⟩

private theorem face_walls (k : Kind) (a b : Bool) (f : Face) (hu : FaceUsed k f) :
    (faceEmbedding f).WallsAgree faceBoard (puzzle k a b).board := by
  intro p
  rw [faceEmbedding_cells]
  exact (used_face_walls k a b f hu p).trans (by simp only [faceBoard,Finset.mem_filter,Finset.mem_univ,true_and])

private theorem face_component (k : Kind) (a b : Bool) (f : Face) (hu : FaceUsed k f)
    (x y : Fin 5) (hx : 0<x.val ∧x.val+1<5) (hy : 0<y.val ∧y.val+1<5) :
    SameComponent (puzzle k a b).board (faceCell f (x,10)) (faceCell f (y,10)) := by
  have hf : ∀z : Fin 5,(z,⟨10,by decide⟩)∉faceBoard.walls := by
    intro z
    simp only [faceBoard,Finset.mem_filter,Finset.mem_univ,true_and]
    decide
  have hc:=horizontal_component (B:=faceBoard) 10 hf x y hx hy
  have hw:=face_walls k a b f hu
  have hh : SameComponent (puzzle k a b).board ((faceEmbedding f).cells (x,10)) ((faceEmbedding f).cells (y,10)) :=
    ⟨GridEmbedding.staticReach hw hc.1,GridEmbedding.staticReach hw hc.2⟩
  simpa only [faceEmbedding_cells] using hh

def targetFaceIndex (k : Kind) : Fin 5 := if targetDirection k=.west then 3 else 1

private theorem last_true_face (k : Kind) : lastPoint k true=faceCell (targetFace k)
    (targetFaceIndex k,10) := by
  cases k <;> rfl

theorem last_to_face (k : Kind) (a b phase : Bool) :
    @SameComponent width height (puzzle k a b).board (lastPoint k phase) (faceCell (targetFace k) (2,10)) := by
  have hc : @SameComponent width height (puzzle k a b).board (lastPoint k phase) (lastPoint k true) :=
    endpoint_component k a b phase true true
  have hf:=face_component k a b (targetFace k) (Or.inr rfl) (targetFaceIndex k) 2
    (by cases k <;> decide) (by decide)
  have hf' : @SameComponent width height (puzzle k a b).board
      (lastPoint k true) (faceCell (targetFace k) (2,10)) := (last_true_face k).symm ▸hf
  exact ⟨hc.1.trans hf'.1,hf'.2.trans hc.2⟩

end PushPuzzle.PushFS.Gadgets.Wires.Catalog
