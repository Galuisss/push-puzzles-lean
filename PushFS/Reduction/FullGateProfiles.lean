/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateRawLabels
public import PushFS.Reduction.AnnulusRawFrames
public import PushFS.Reduction.StorageReplay

/-! Actual independently selected primitive inventories of the complete physical gate. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting


open Gadgets.Wires
open scoped Classical
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] StorageAtlas.initial StorageAtlas.board

noncomputable def profileMask (g : GateTileState) (f : Inventory.Index g→Bool) :
    Fin (Fintype.card (Inventory.Index g))→Bool := fun i=>f ((Inventory.numbering g).symm i)

noncomputable def profile (g : GateTileState) (f : Inventory.Index g→Bool) (player : C) : State 200007 198068 :=
  (fullAtlas g).profileAt (profileMask g f) player

noncomputable def profileOutside (g : GateTileState) (f : Inventory.Index g→Bool) (i : Inventory.Index g) : Finset C :=
  (fullAtlas g).profileOutside (profileMask g f) ((Inventory.numbering g) i)

def selectedMarks (g : GateTileState) (b : Bool) (i : Inventory.Index g) :
    Finset (Cell (Inventory.piece g i).width (Inventory.piece g i).height) :=
  if b then (Inventory.piece g i).board.goals else (Inventory.piece g i).initial.boxes

theorem profileMask_at (g : GateTileState) (f : Inventory.Index g→Bool) (i : Inventory.Index g) :
    profileMask g f ((Inventory.numbering g) i)=f i := by
  simp only [profileMask,Equiv.symm_apply_apply]

private theorem selectedMarks_at (g : GateTileState) (f : Inventory.Index g→Bool)
    (j : Fin (Fintype.card (Inventory.Index g))) (i : Inventory.Index g) (hi : (Inventory.numbering g).symm j=i) :
    @Eq (Finset C) (((fullAtlas g).pieceMarks (profileMask g f) j).map ((fullAtlas g).embedding j).cells)
      ((selectedMarks g (f i) i).map (primitiveEmbedding g i).cells) := by
  subst i
  rfl

private theorem selectedMarks_numbering (g : GateTileState) (f : Inventory.Index g→Bool)
    (i : Inventory.Index g) :
    @Eq (Finset C) (((fullAtlas g).pieceMarks (profileMask g f) ((Inventory.numbering g) i)).map
      ((fullAtlas g).embedding ((Inventory.numbering g) i)).cells)
      ((selectedMarks g (f i) i).map (primitiveEmbedding g i).cells) :=
  selectedMarks_at g f _ _ (Equiv.symm_apply_apply _ _)

theorem profile_split (g : GateTileState) (f : Inventory.Index g→Bool) (i : Inventory.Index g) (player : C) :
    (profile g f player).boxes=(selectedMarks g (f i) i).map (primitiveEmbedding g i).cells∪profileOutside g f i := by
  change (fullAtlas g).profileBoxes (profileMask g f)=_
  rw [(fullAtlas g).profile_split (profileMask g f) ((Inventory.numbering g) i),selectedMarks_numbering]
  rfl

theorem profile_initial (g : GateTileState) : profile g (fun _=>false) (fullAtlas g).player=(fullPuzzle g).initial := by
  apply State.ext
  · change (fullAtlas g).player=(fullAtlas g).initial.player
    unfold StorageAtlas.initial
    rfl
  · exact (fullAtlas g).profile_initial

theorem profile_target (g : GateTileState) (player : C) :
    (profile g (fun _=>true) player).boxes=(fullPuzzle g).board.goals := (fullAtlas g).profile_target

theorem profileOutside_floor (g : GateTileState) (f : Inventory.Index g→Bool) (i : Inventory.Index g) :
    Disjoint (profileOutside g f i) (fullPuzzle g).board.walls :=
  (fullAtlas g).profileOutside_floor (profileMask g f) ((Inventory.numbering g) i)

attribute [local irreducible] StorageAtlas.profileOutside StorageAtlas.profileBoxes profile profileOutside

theorem mem_profileOutside (g : GateTileState) (f : Inventory.Index g→Bool) (i : Inventory.Index g) (p : C) :
    p∈profileOutside g f i ↔∃j : Inventory.Index g,j≠i ∧
      ∃q : Cell (Inventory.piece g j).width (Inventory.piece g j).height,
        q∈selectedMarks g (f j) j ∧(primitiveEmbedding g j).cells q=p := by
  unfold profileOutside
  have hm:=(fullAtlas g).mem_profileOutside_map (profileMask g f) ((Inventory.numbering g) i) p
  constructor
  · intro hp
    obtain ⟨j,hj,hp⟩:=hm.mp hp
    let k:=(Inventory.numbering g).symm j
    have hk : (Inventory.numbering g) k=j := Equiv.apply_symm_apply _ _
    rw [selectedMarks_at g f j k rfl] at hp
    obtain ⟨q,hq,he⟩:=Finset.mem_map.mp hp
    refine ⟨k,?_,q,hq,he⟩
    intro hki
    apply hj
    exact hk.symm.trans (congrArg (Inventory.numbering g) hki)
  · rintro ⟨j,hji,q,hq,he⟩
    apply hm.mpr
    refine ⟨(Inventory.numbering g) j,?_,?_⟩
    · exact fun h=>hji ((Inventory.numbering g).injective h)
    · rw [selectedMarks_numbering]
      exact Finset.mem_map.mpr ⟨q,hq,he⟩

def lineIndex (g : GateTileState) (r : Fin 3) (j : Fin (curve (key g r)).length) : Inventory.Index g :=
  .inr (.inl ⟨r,.inl j⟩)

def cornerIndex (g : GateTileState) (r : Fin 3) (j : Fin ((curve (key g r)).length-1)) : Inventory.Index g :=
  .inr (.inl ⟨r,.inr j⟩)

def cornerInLine (g : GateTileState) (r : Fin 3) (k : Fin ((curve (key g r)).length-1)) :
    Fin (curve (key g r)).length := ⟨k.val,by have :=k.isLt; omega⟩

def cornerOutLine (g : GateTileState) (r : Fin 3) (k : Fin ((curve (key g r)).length-1)) :
    Fin (curve (key g r)).length := ⟨k.val+1,by have :=k.isLt; omega⟩

def lineInput (g : GateTileState) (r : Fin 3) (j : Fin (curve (key g r)).length) : Instance :=
  lineBase (fillerFlip (key g r) j.val) (fillerSpan (key g r) j.val) (filler_shape (key g r) j.val j.isLt).2.1
    (Inventory.initialPhase g r) (Inventory.targetPhase g r)

def lineBaseCorner (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool) (i : Fin 4) :
    Cell (lineBase flip n hn a b).width (lineBase flip n hn a b).height :=
  match flip with
  | false=>Chain.corner n i
  | true=>FlippedChain.corner n i

def lineBaseHub (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool) :
    Cell (lineBase flip n hn a b).width (lineBase flip n hn a b).height :=
  match flip with
  | false=>Chain.hub n hn
  | true=>FlippedChain.player n

def lineCorner (g : GateTileState) (r : Fin 3) (j : Fin (curve (key g r)).length) (i : Fin 4) :
    Cell (lineInput g r j).width (lineInput g r j).height :=
  lineBaseCorner (fillerFlip (key g r) j.val) (fillerSpan (key g r) j.val) (filler_shape (key g r) j.val j.isLt).2.1
    (Inventory.initialPhase g r) (Inventory.targetPhase g r) i

def lineHub (g : GateTileState) (r : Fin 3) (j : Fin (curve (key g r)).length) :
    Cell (lineInput g r j).width (lineInput g r j).height :=
  lineBaseHub (fillerFlip (key g r) j.val) (fillerSpan (key g r) j.val) (filler_shape (key g r) j.val j.isLt).2.1
    (Inventory.initialPhase g r) (Inventory.targetPhase g r)

def lineEmbedding (g : GateTileState) (r : Fin 3) (j : Fin (curve (key g r)).length) :
    GridEmbedding (lineInput g r j).width (lineInput g r j).height 200007 198068 :=
  (lineRawIso (key g r) j.val j.isLt (Inventory.initialPhase g r) (Inventory.targetPhase g r)).embedding.trans
    (primitiveEmbedding g (lineIndex g r j))

theorem line_walls (g : GateTileState) (r : Fin 3) (j : Fin (curve (key g r)).length) :
    (lineEmbedding g r j).WallsAgree (lineInput g r j).board (fullPuzzle g).board := by
  intro p
  exact (primitive_walls_agree g (lineIndex g r j)
    ((lineRawIso (key g r) j.val j.isLt (Inventory.initialPhase g r) (Inventory.targetPhase g r)).cells p)).trans
    (line_raw_walls _ _ _ _ _ p)

theorem line_coordinates (g : GateTileState) (r : Fin 3) (j : Fin (curve (key g r)).length)
    (p : Cell (lineInput g r j).width (lineInput g r j).height) :
    (((lineEmbedding g r j).cells p).1.val,((lineEmbedding g r j).cells p).2.val)=
      (lineOrientation (original (key g r) j.val).travel (fillerFlip (key g r) j.val)).coordinates _ _
        (lineOffset (key g r) j.val).1 (lineOffset (key g r) j.val).2 p := rfl

private theorem map_reoriented {I : Instance} {w h W H : ℕ} (e : GridIsometry I.width I.height w h)
    (f : GridEmbedding w h W H) (b : Bool) :
    (if b then (e.reorientInstance I).board.goals else (e.reorientInstance I).initial.boxes).map f.cells=
      (if b then I.board.goals else I.initial.boxes).map (e.embedding.trans f).cells := by
  cases b
  · exact Finset.map_map e.cells.toEmbedding f.cells I.initial.boxes
  · exact Finset.map_map e.cells.toEmbedding f.cells I.board.goals

theorem line_marks_map (g : GateTileState) (b : Bool) (r : Fin 3) (j : Fin (curve (key g r)).length) :
    (selectedMarks g b (lineIndex g r j)).map (primitiveEmbedding g (lineIndex g r j)).cells=
      (if b then (lineInput g r j).board.goals else (lineInput g r j).initial.boxes).map (lineEmbedding g r j).cells := by
  exact map_reoriented (I:=lineInput g r j)
    (lineRawIso (key g r) j.val j.isLt (Inventory.initialPhase g r) (Inventory.targetPhase g r))
    (primitiveEmbedding g (lineIndex g r j)) b

theorem profile_line_split (g : GateTileState) (f : Inventory.Index g→Bool) (r : Fin 3)
    (j : Fin (curve (key g r)).length) (player : C) :
    (profile g f player).boxes=
      (if f (lineIndex g r j) then (lineInput g r j).board.goals else (lineInput g r j).initial.boxes).map
        (lineEmbedding g r j).cells∪profileOutside g f (lineIndex g r j) := by
  rw [profile_split g f (lineIndex g r j) player,line_marks_map]

def armCornerEmbedding (g : GateTileState) (r : Fin 3) (j : Fin ((curve (key g r)).length-1)) :
    GridEmbedding (ShortCorners.width (cornerKind (key g r) j.val)) (ShortCorners.height (cornerKind (key g r) j.val)) 200007 198068 :=
  (cornerIso (key g r) j.val).geometry.embedding.trans (primitiveEmbedding g (cornerIndex g r j))

theorem arm_corner_coordinates (g : GateTileState) (r : Fin 3) (j : Fin ((curve (key g r)).length-1))
    (p : Cell (ShortCorners.width (cornerKind (key g r) j.val)) (ShortCorners.height (cornerKind (key g r) j.val))) :
    (((armCornerEmbedding g r j).cells p).1.val,((armCornerEmbedding g r j).cells p).2.val)=
      (cornerOrientation (key g r) j.val).coordinates _ _
        (cornerOffset (key g r) j.val).1 (cornerOffset (key g r) j.val).2 p := rfl

theorem arm_corner_walls (g : GateTileState) (r : Fin 3) (j : Fin ((curve (key g r)).length-1)) :
    (armCornerEmbedding g r j).WallsAgree ((ShortCorners.template (cornerKind (key g r) j.val)).board ∅) (fullPuzzle g).board := by
  intro p
  exact (primitive_walls_agree g (cornerIndex g r j) ((cornerIso (key g r) j.val).geometry.cells p)).trans
    (corner_raw_walls _ _ _ _ p)

theorem corner_marks_map (g : GateTileState) (b : Bool) (r : Fin 3) (j : Fin ((curve (key g r)).length-1)) :
    (selectedMarks g b (cornerIndex g r j)).map (primitiveEmbedding g (cornerIndex g r j)).cells=
      ((ShortCorners.template (cornerKind (key g r) j.val)).boxes
        (if b then Inventory.targetPhase g r else Inventory.initialPhase g r)).map (armCornerEmbedding g r j).cells := by
  cases b
  · exact map_reoriented (I:=ShortCorners.puzzle (cornerKind (key g r) j.val) (Inventory.initialPhase g r) (Inventory.targetPhase g r))
      (cornerIso (key g r) j.val).geometry (primitiveEmbedding g (cornerIndex g r j)) false
  · exact map_reoriented (I:=ShortCorners.puzzle (cornerKind (key g r) j.val) (Inventory.initialPhase g r) (Inventory.targetPhase g r))
      (cornerIso (key g r) j.val).geometry (primitiveEmbedding g (cornerIndex g r j)) true

theorem profile_corner_split (g : GateTileState) (f : Inventory.Index g→Bool) (r : Fin 3)
    (j : Fin ((curve (key g r)).length-1)) (player : C) :
    (profile g f player).boxes=
      ((ShortCorners.template (cornerKind (key g r) j.val)).boxes
        (if f (cornerIndex g r j) then Inventory.targetPhase g r else Inventory.initialPhase g r)).map
          (armCornerEmbedding g r j).cells∪profileOutside g f (cornerIndex g r j) := by
  rw [profile_split g f (cornerIndex g r j) player,corner_marks_map]

end PushPuzzle.PushFS.Reduction.GateTileRouting
