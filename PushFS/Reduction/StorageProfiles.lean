/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.StorageAtlas
public import PushFS.Gadgets.Wires.Chain.CoveredPlacement

/-! Exact intermediate full inventories while actual overlapping glyphs change phase one at a time. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.StorageAtlas


open scoped Classical
variable {n W H : ℕ} {Label : Fin n→Type} [∀i,Fintype (Label i)] (A : StorageAtlas n W H Label)

/-- A bit selects the real source or target inventory of this complete owned glyph. -/
def pieceMarks (f : Fin n→Bool) (i : Fin n) : Finset (Cell (A.piece i).width (A.piece i).height) :=
  if f i then (A.piece i).board.goals else (A.piece i).initial.boxes

def profileBoxes (f : Fin n→Bool) : Finset (Cell W H) :=
  Finset.univ.biUnion fun i=>(A.pieceMarks f i).map (A.embedding i).cells

def profileAt (f : Fin n→Bool) (player : Cell W H) : State W H := ⟨player,A.profileBoxes f⟩

/-- All actual foreign boxes stay present while one actual glyph is replayed. -/
def profileOutside (f : Fin n→Bool) (i : Fin n) : Finset (Cell W H) :=
  (Finset.univ.erase i).biUnion fun j=>(A.pieceMarks f j).map (A.embedding j).cells

theorem profile_initial : A.profileBoxes (fun _=>false)=A.initial.boxes := by
  ext p
  rw [A.mem_boxes_iff p]
  simp only [profileBoxes,pieceMarks,Bool.false_eq_true,ite_false,Finset.mem_biUnion,Finset.mem_univ,
    true_and,Finset.mem_map]

theorem profile_target : A.profileBoxes (fun _=>true)=A.board.goals := by
  ext p
  rw [A.mem_goals_iff p]
  simp only [profileBoxes,pieceMarks,ite_true,Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_map]

theorem profile_split (f : Fin n→Bool) (i : Fin n) :
    A.profileBoxes f=(A.pieceMarks f i).map (A.embedding i).cells∪A.profileOutside f i := by
  ext p
  simp only [profileBoxes,profileOutside,Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_union,
    Finset.mem_erase,and_true]
  constructor
  · rintro ⟨j,hj⟩
    by_cases he : j=i
    · exact Or.inl (he ▸ hj)
    · exact Or.inr ⟨j,he,hj⟩
  · rintro (hp|⟨j,_,hj⟩)
    · exact ⟨i,hp⟩
    · exact ⟨j,hj⟩

theorem profileOutside_update (f : Fin n→Bool) (i : Fin n) (b : Bool) :
    A.profileOutside (Function.update f i b) i=A.profileOutside f i := by
  apply Finset.biUnion_congr rfl
  intro j hj
  have hji : j≠i := (Finset.mem_erase.mp hj).1
  simp only [pieceMarks,Function.update_of_ne hji]

theorem profile_floor (f : Fin n→Bool) : Disjoint (A.profileBoxes f) A.board.walls := by
  apply Finset.disjoint_left.mpr
  intro p hp hw
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hi
  have hfloor : Disjoint (A.pieceMarks f i) (A.piece i).board.walls := by
    unfold pieceMarks
    split
    · exact (A.piece i).goals_floor.symm
    · exact (A.piece i).initial_valid.2.1
  exact Finset.disjoint_left.mp hfloor hq ((A.walls_agree i q).mp hw)

theorem profileOutside_floor (f : Fin n→Bool) (i : Fin n) :
    Disjoint (A.profileOutside f i) A.board.walls := by
  apply (A.profile_floor f).mono_left
  rw [A.profile_split f i]
  exact Finset.subset_union_right

def profileFixed (f : Fin n→Bool) (i : Fin n) : Finset (Cell (A.piece i).width (A.piece i).height) :=
  Finset.univ.filter fun p=>(A.embedding i).cells p∈A.profileOutside f i

end PushPuzzle.PushFS.Reduction.StorageAtlas
