/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.RectThresholds
public import PushFS.Gadgets.Wires.Catalog.ImageGlyphs

/-! Full-chain signals with independent travel direction and wall-side orientation. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog

open Soundness Polyline
set_option maxRecDepth 65536
set_option maxHeartbeats 100000

namespace StorageImage
variable {I J : Instance} {L A : Type} [Fintype L] [Fintype A]
    {M : SlotMatching I L} {N : SlotMatching J A}

def point (g : StorageImage M N) (p : PushFS.Cell J.width J.height) : PushFS.Cell I.width I.height :=
  (GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells p

theorem point_adjacent (g : StorageImage M N) {d : Direction} {p q : PushFS.Cell J.width J.height}
    (ha : Adjacent d p q) : Adjacent d (g.point p) (g.point q) :=
  (GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).adjacent d p q ha

def orientedPoint (o : RectOrientation)
    (g : StorageImage M (N.reorient (o.axis J.width J.height).geometry))
    (p : PushFS.Cell J.width J.height) : PushFS.Cell I.width I.height :=
  (GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells ((o.axis J.width J.height).geometry.cells p)

theorem orientedPoint_adjacent (o : RectOrientation)
    (g : StorageImage M (N.reorient (o.axis J.width J.height).geometry))
    {d : Direction} {p q : PushFS.Cell J.width J.height} (ha : Adjacent d p q) :
    Adjacent (o.direction d) (g.orientedPoint o p) (g.orientedPoint o q) := by
  have hh:=(o.axis J.width J.height).geometry.adjacent d p q |>.mpr ha
  rw [o.direction_eq] at hh
  exact (GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).adjacent _ _ _ hh

variable {K : Instance} {D : Type} [Fintype D] {P : SlotMatching K D}

theorem comp_orientedPoint (o : RectOrientation) (g : StorageImage M N)
    (h : StorageImage N (P.reorient (o.axis K.width K.height).geometry)) (p : PushFS.Cell K.width K.height) :
    (g.comp h).orientedPoint o p=
      (GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells (h.orientedPoint o p) := by
  apply Prod.ext <;> apply Fin.ext
  · change g.dx+h.dx+_=g.dx+(h.dx+_)
    omega
  · change g.dy+h.dy+_=g.dy+(h.dy+_)
    omega

end StorageImage

theorem adjacent_twice {W H : ℕ} {d : Direction} {p q r : PushFS.Cell W H}
    (hp : Adjacent d p q) (hq : Adjacent d q r) :
    DirectionalStep d (p.1.val,p.2.val) (r.1.val,r.2.val) := by
  cases d <;> simp only [Adjacent,DirectionalStep] at hp hq ⊢ <;> omega

def chainSourceAnchor (n : ℕ) : Chain.C n := (⟨3,by omega⟩,10)
def chainTargetAnchor (n : ℕ) : Chain.C n := (⟨n+1,by omega⟩,10)

variable {I : Instance} {L : Type} [Fintype L] {M : SlotMatching I L}

theorem rotated_chain_signal (n : ℕ) (hn : 2301≤n) (a b : Bool) (o : RectOrientation)
    (g : StorageImage M ((Chain.slotMatching n hn a b).reorient (o.axis (n+5) 21).geometry))
    {S T : LabelledState L I.width I.height} (hs : Successful M S T) (cert : Certificate I) (ordered : M.Ordered)
    (hin : TravelHigh (o.direction .east)
      ((g.orientedPoint o (chainSourceAnchor n)).1.val,(g.orientedPoint o (chainSourceAnchor n)).2.val)
      ((S.position (g.labels (ChainEnds.first n hn))).1.val,(S.position (g.labels (ChainEnds.first n hn))).2.val)) :
    TravelHigh (o.direction .east)
      ((g.orientedPoint o (chainTargetAnchor n)).1.val,(g.orientedPoint o (chainTargetAnchor n)).2.val)
      ((S.position (g.labels (ChainEnds.last n hn))).1.val,(S.position (g.labels (ChainEnds.last n hn))).2.val) := by
  let e:=o.undo I.width I.height
  let h:=g.straighten o
  have href (p : Chain.C n) :
      ((e.cells (g.orientedPoint o p)).1.val)=h.dx+p.1.val := by
    exact congrArg (fun z : PushFS.Cell (o.width I.width I.height) (o.height I.width I.height)=>z.1.val)
      (o.undo_cells I.width I.height (n+5) 21 g.dx g.dy g.fit_x g.fit_y p)
  have hi:=(undo_east_iff o (g.orientedPoint o (chainSourceAnchor n))
    (S.position (g.labels (ChainEnds.first n hn)))).mpr hin
  change ((e.cells (g.orientedPoint o (chainSourceAnchor n))).1.val)≤
    ((e.cells (S.position (g.labels (ChainEnds.first n hn)))).1.val) at hi
  rw [href] at hi
  have hi' : h.dx+3≤((orientLabels e S).position (h.labels (ChainEnds.first n hn))).1.val := hi
  have hout:=h.chainGlyph.signal (orient_successful M hs e) (rectCertificate M cert o.inverse)
    (rectOrdered M ordered o.inverse) hi'
  apply (undo_east_iff o (g.orientedPoint o (chainTargetAnchor n))
    (S.position (g.labels (ChainEnds.last n hn)))).mp
  change ((e.cells (g.orientedPoint o (chainTargetAnchor n))).1.val)≤
    ((e.cells (S.position (g.labels (ChainEnds.last n hn)))).1.val)
  rw [href]
  exact hout

end PushPuzzle.PushFS.Gadgets.Wires.Catalog
