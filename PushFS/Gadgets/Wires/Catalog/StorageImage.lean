/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.Statics
public import PushFS.Gadgets.Wires.Catalog.Collars

/-! Literal full-slot storage charts inside an arbitrary actual ambient instance. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog

variable {I J K : Instance} {L A D : Type} [Fintype L] [Fintype A] [Fintype D]

/-- Only exact physical walls and all real source/target identities specify an ambient glyph. -/
structure StorageImage (M : SlotMatching I L) (N : SlotMatching J A) where
  dx : ℕ
  dy : ℕ
  fit_x : dx+J.width≤I.width
  fit_y : dy+J.height≤I.height
  labels : A↪L
  walls : (GridEmbedding.translate dx dy fit_x fit_y).WallsAgree J.board I.board
  sources : ∀l, M.source (labels l)=(GridEmbedding.translate dx dy fit_x fit_y).cells (N.source l)
  targets : ∀l, M.target (labels l)=(GridEmbedding.translate dx dy fit_x fit_y).cells (N.target l)

namespace StorageImage

variable {M : SlotMatching I L} {N : SlotMatching J A} {P : SlotMatching K D}

def comp (g : StorageImage M N) (h : StorageImage N P) : StorageImage M P where
  dx:=g.dx+h.dx
  dy:=g.dy+h.dy
  fit_x:=by have:=g.fit_x; have:=h.fit_x; omega
  fit_y:=by have:=g.fit_y; have:=h.fit_y; omega
  labels:=h.labels.trans g.labels
  walls p:=by
    have he : (GridEmbedding.translate (g.dx+h.dx) (g.dy+h.dy) (by have:=g.fit_x; have:=h.fit_x; omega)
        (by have:=g.fit_y; have:=h.fit_y; omega)).cells p=
        (GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells
          ((GridEmbedding.translate h.dx h.dy h.fit_x h.fit_y).cells p) := by
      apply Prod.ext <;> apply Fin.ext
      · change g.dx+h.dx+p.1.val=g.dx+(h.dx+p.1.val); omega
      · change g.dy+h.dy+p.2.val=g.dy+(h.dy+p.2.val); omega
    rw [he,g.walls,h.walls]
  sources l:=by
    change M.source (g.labels (h.labels l))=_
    rw [g.sources,h.sources]
    apply Prod.ext <;> apply Fin.ext
    · change g.dx+(h.dx+(P.source l).1.val)=g.dx+h.dx+(P.source l).1.val; omega
    · change g.dy+(h.dy+(P.source l).2.val)=g.dy+h.dy+(P.source l).2.val; omega
  targets l:=by
    change M.target (g.labels (h.labels l))=_
    rw [g.targets,h.targets]
    apply Prod.ext <;> apply Fin.ext
    · change g.dx+(h.dx+(P.target l).1.val)=g.dx+h.dx+(P.target l).1.val; omega
    · change g.dy+(h.dy+(P.target l).2.val)=g.dy+h.dy+(P.target l).2.val; omega

/-- Reflecting the actual whole board straightens a genuinely reflected local chart. -/
def unreflectX (g : StorageImage M (N.reorient (GridIsometry.reflectX J.width J.height))) :
    StorageImage (M.reorient (GridIsometry.reflectX I.width I.height)) N := by
  have hg : g.dx+J.width≤I.width := g.fit_x
  have hx : I.width-g.dx-J.width+J.width≤I.width := by omega
  have he (p : PushFS.Cell J.width J.height) :
      (GridIsometry.reflectX I.width I.height).cells
        ((GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells ((GridIsometry.reflectX J.width J.height).cells p))=
      (GridEmbedding.translate (I.width-g.dx-J.width) g.dy hx g.fit_y).cells p := by
    apply Prod.ext <;> apply Fin.ext
    · change I.width-(g.dx+(J.width-(p.1.val+1))+1)=(I.width-g.dx-J.width)+p.1.val
      have:=p.1.isLt
      omega
    · rfl
  refine ⟨I.width-g.dx-J.width,g.dy,hx,g.fit_y,g.labels,?_,?_,?_⟩
  · intro p
    change (GridEmbedding.translate (I.width-g.dx-J.width) g.dy hx g.fit_y).cells p∈
      ((GridIsometry.reflectX I.width I.height).board I.board).walls ↔p∈J.board.walls
    rw [←he p]
    exact ((GridIsometry.reflectX I.width I.height).mem_walls I.board _).trans
      ((g.walls _).trans ((GridIsometry.reflectX J.width J.height).mem_walls J.board p))
  · intro l
    change (GridIsometry.reflectX I.width I.height).cells (M.source (g.labels l))=_
    rw [g.sources]
    exact he (N.source l)
  · intro l
    change (GridIsometry.reflectX I.width I.height).cells (M.target (g.labels l))=_
    rw [g.targets]
    exact he (N.target l)

/-- Swapping the actual whole-board coordinates straightens a genuinely transposed local chart. -/
def untranspose (g : StorageImage M (N.reorient (GridIsometry.transpose J.width J.height))) :
    StorageImage (M.reorient (GridIsometry.transpose I.width I.height)) N := by
  have he (p : PushFS.Cell J.width J.height) :
      (GridIsometry.transpose I.width I.height).cells
        ((GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells ((GridIsometry.transpose J.width J.height).cells p))=
      (GridEmbedding.translate g.dy g.dx g.fit_y g.fit_x).cells p := rfl
  refine ⟨g.dy,g.dx,g.fit_y,g.fit_x,g.labels,?_,?_,?_⟩
  · intro p
    change (GridEmbedding.translate g.dy g.dx g.fit_y g.fit_x).cells p∈
      ((GridIsometry.transpose I.width I.height).board I.board).walls ↔p∈J.board.walls
    rw [←he p]
    exact ((GridIsometry.transpose I.width I.height).mem_walls I.board _).trans
      ((g.walls _).trans ((GridIsometry.transpose J.width J.height).mem_walls J.board p))
  · intro l
    change (GridIsometry.transpose I.width I.height).cells (M.source (g.labels l))=_
    rw [g.sources]
    exact he (N.source l)
  · intro l
    change (GridIsometry.transpose I.width I.height).cells (M.target (g.labels l))=_
    rw [g.targets]
    exact he (N.target l)

end StorageImage

/-- The complete native physical glyph is an actual full-slot chart of its padded cell. -/
def baseImage (k : Kind) (a b : Bool) : StorageImage (slotMatching k a b) (baseMatching k a b) where
  dx:=dx k
  dy:=dy k
  fit_x:=fitsX k a b
  fit_y:=fitsY k a b
  labels:=⟨fun l=>⟨0,l⟩,by intro i j he; exact eq_of_heq ((Sigma.mk.inj_iff.mp he).2)⟩
  walls:=padding_walls k a b
  sources _:=rfl
  targets _:=rfl

end PushPuzzle.PushFS.Gadgets.Wires.Catalog
