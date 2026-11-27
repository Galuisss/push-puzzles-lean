/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateStatics.Cover
public import PushFS.Reduction.FullGateBoundary
public import PushFS.Gadgets.Gates.AxisGeometry
public import PushFS.Gadgets.Wires.ShortCorners.Statics
public import PushFS.Gadgets.Wires.FlippedChain.AxisGeometry

/-! Actual supported classifiers of every primitive in the complete physical gate inventory. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics

open Gadgets Gadgets.Wires
set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

def classifier_rebase {w h : ℕ} {B A : Board w h} (C : AxisClassifier B) (hw : B.walls=A.walls) : AxisClassifier A where
  name:=C.name
  supported:=C.supported
  displacement p q hd:=C.displacement p q (by simpa only [Displacement,hw] using hd)


def westAxis (kind : Bool) (n : ℕ) : AxisIsometry (n+5) 21 (n+5) 21 :=
  if kind then AxisIsometry.reflectX (n+5) 21
  else (AxisIsometry.reflectX (n+5) 21).trans (AxisIsometry.reflectY (n+5) 21)

theorem westAxis_geometry (kind : Bool) (n : ℕ) : (westAxis kind n).geometry=GateLead.westIso kind n := by
  cases kind <;> rfl

def northAxis (n : ℕ) : AxisIsometry (n+5) 21 21 (n+5) :=
  (AxisIsometry.clockwise (n+5) 21).trans (AxisIsometry.reflectY 21 (n+5))

def eastAxis (n : ℕ) : AxisIsometry (n+5) 21 (n+5) 21 := AxisIsometry.reflectY (n+5) 21

def westClassifier (kind : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool) :
    AxisClassifier ((GateLead.westIso kind n).board (Chain.puzzle n hn a b).board) := by
  have hc:=Polyline.axisClassifier ((Catalog.chainStrong n hn false false).rotate (westAxis kind n)).axes
  change AxisClassifier ((westAxis kind n).geometry.board (Chain.puzzle n hn false false).board) at hc
  rw [westAxis_geometry] at hc
  exact classifier_rebase hc rfl

def northClassifier (n : ℕ) (hn : 2301≤n) (a b : Bool) :
    AxisClassifier ((GateLead.northIso n).board (Chain.puzzle n hn a b).board) :=
  classifier_rebase (Polyline.axisClassifier ((Catalog.chainStrong n hn false false).rotate (northAxis n)).axes) rfl

def eastClassifier (n : ℕ) (hn : 2301≤n) (a b : Bool) :
    AxisClassifier ((GateLead.eastIso n).board (Chain.puzzle n hn a b).board) :=
  classifier_rebase (Polyline.axisClassifier ((Catalog.chainStrong n hn false false).rotate (eastAxis n)).axes) rfl

def bufferClassifier (kind : Bool) (n : ℕ) (hn : 2301≤n) (a b : Gates.Signals) :
    (i : Fin 4)→AxisClassifier (GateLead.piece kind n hn a b i).board :=
  Fin.cases (classifier_rebase (Gates.classifier kind ∅) rfl)
    (Fin.cases (westClassifier kind n hn a.left b.left)
      (Fin.cases (northClassifier n hn a.upper b.upper) (fun _=>eastClassifier n hn (!a.right) (!b.right))))

def lineBaseClassifier (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool) :
    AxisClassifier (lineBase flip n hn a b).board := by
  cases flip
  · exact Polyline.axisClassifier (Chain.axisTracks n hn a b)
  · exact Polyline.axisClassifier (FlippedChain.axisTracks n hn a b)

theorem lineBase_strong (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool)
    (p q : Cell (lineBase flip n hn a b).width (lineBase flip n hn a b).height)
    (hp : (lineBaseClassifier flip n hn a b).name p≠.outside)
    (hd : Displacement (lineBase flip n hn a b).board p q) :
    ((lineBaseClassifier flip n hn a b).name p).Strong ((lineBaseClassifier flip n hn a b).name q) := by
  cases flip
  · exact (Catalog.chainStrong n hn a b).strong p q hp hd
  · change (FlippedChain.axisName n p).Strong (FlippedChain.axisName n q)
    change FlippedChain.axisName n p≠.outside at hp
    change Displacement (FlippedChain.atlas n hn (FlippedChain.uniform a) (FlippedChain.uniform b)).board p q at hd
    rw [FlippedChain.board_eq] at hd
    exact FlippedChain.strong_displacement n hn _ hp hd

def lineClassifier (k : Key) (i : ℕ) (hi : i<(curve k).length) (a b : Bool) :
    AxisClassifier (linePiece k i hi a b).board :=
  ((lineOrientation (original k i).travel (fillerFlip k i)).axis _ _).classifier
    (lineBaseClassifier (fillerFlip k i) (fillerSpan k i) (filler_shape k i hi).2.1 a b)
    (lineBase_strong _ _ _ _ _)

theorem short_strong (kind : ShortCorners.Kind) (goals : Finset (Cell (ShortCorners.width kind) (ShortCorners.height kind)))
    (p q : Cell (ShortCorners.width kind) (ShortCorners.height kind)) (hp : ShortCorners.axisName kind p≠.outside)
    (hd : Displacement ((ShortCorners.template kind).board goals) p q) :
    (ShortCorners.axisName kind p).Strong (ShortCorners.axisName kind q) := by
  apply (AxisTrack.strongAllowed_iff (ShortCorners.axisName kind) p q).mp
  exact (checkDisplacements_correct ((ShortCorners.template kind).wall_correct goals) _ _).mp
    (ShortCorners.strong_checked kind) p (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩) q hd

def cornerClassifier (k : Key) (i : ℕ) (a b : Bool) : AxisClassifier (cornerPiece k i a b).board :=
  classifier_rebase
    (w:=(cornerOrientation k i).width (ShortCorners.width (cornerKind k i)) (ShortCorners.height (cornerKind k i)))
    (h:=(cornerOrientation k i).height (ShortCorners.width (cornerKind k i)) (ShortCorners.height (cornerKind k i)))
    (B:=(cornerIso k i).geometry.board ((ShortCorners.template (cornerKind k i)).board ∅))
    (A:=(cornerPiece k i a b).board)
    ((cornerIso k i).classifier (ShortCorners.classifier (cornerKind k i) ∅) (short_strong _ _))
    (by
      change (ShortCorners.template (cornerKind k i)).walls.map (cornerIso k i).geometry.cells.toEmbedding=
        (ShortCorners.template (cornerKind k i)).walls.map (cornerIso k i).geometry.cells.toEmbedding
      rfl)

def outsideClassifier {w h : ℕ} (B : Board w h) : AxisClassifier B where
  name _:=.outside
  supported _:=True.intro
  displacement _ _ _:=Or.inl rfl

def rawClassifier (g : GateTileState) : (i : Inventory.Index g)→AxisClassifier (Inventory.piece g i).board
  | .inl i => bufferClassifier g.core.isAND 2301 (by omega) g.core.initial g.core.target i
  | .inr (.inl ⟨role,.inl j⟩) => lineClassifier (key g role) j.val j.isLt (Inventory.initialPhase g role) (Inventory.targetPhase g role)
  | .inr (.inl ⟨role,.inr j⟩) => cornerClassifier (key g role) j.val (Inventory.initialPhase g role) (Inventory.targetPhase g role)
  | .inr (.inr _) => outsideClassifier _

def primitiveClassifier (g : GateTileState) (i : Inventory.Index g) : AxisClassifier (Inventory.piece g i).board :=
  rawClassifier g i

def primitiveChart (g : GateTileState) (i : Inventory.Index g) : TranslatedAxisChart 200007 198068 where
  width:=(Inventory.piece g i).width
  height:=(Inventory.piece g i).height
  board:=(Inventory.piece g i).board
  dx:=(Inventory.offset g i).1
  dy:=(Inventory.offset g i).2
  fits_x:=(Inventory.fits g i).1
  fits_y:=(Inventory.fits g i).2
  classifier:=primitiveClassifier g i

theorem primitive_walls (g : GateTileState) (i : Inventory.Index g) :
    (primitiveChart g i).embedding.WallsAgree (primitiveChart g i).board (fullPuzzle g).board := by
  obtain ⟨j,rfl⟩:=(Inventory.numbering g).symm.surjective i
  exact full_walls_agree g j

end PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics
