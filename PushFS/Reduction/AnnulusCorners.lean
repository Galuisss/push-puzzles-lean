/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.AnnulusFillers
public import PushFS.Gadgets.Wires.ShortCorners.Geometry

/-! Actual protected short-turn instances at every checked physical annular corner. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateTileRouting


open Gadgets.Wires

def cornerKindFor (d e : Direction) : ShortCorners.Kind :=
  match RectOrientation.nearFlip d e,RectOrientation.farFlip d e with
  | false,false => .plain
  | false,true => .outFlip
  | true,false => .inFlip
  | true,true => .both

def cornerKind (q : Key) (i : ℕ) : ShortCorners.Kind :=
  cornerKindFor (turnDirections q i).1 (turnDirections q i).2

def cornerOrientation (q : Key) (i : ℕ) : RectOrientation :=
  RectOrientation.choose (turnDirections q i).1 (turnDirections q i).2

def cornerIso (q : Key) (i : ℕ) :=
  (cornerOrientation q i).axis (ShortCorners.width (cornerKind q i)) (ShortCorners.height (cornerKind q i))

def cornerLocal (k : ShortCorners.Kind) : Cell (ShortCorners.width k) (ShortCorners.height k) :=
  (⟨10,by cases k <;> decide⟩,⟨10,by cases k <;> decide⟩)

def nearAnchor (k : ShortCorners.Kind) : Cell (ShortCorners.width k) (ShortCorners.height k) :=
  (⟨ShortCorners.sourceX k,by cases k <;> decide⟩,⟨10,by cases k <;> decide⟩)

def farAnchor (k : ShortCorners.Kind) : Cell (ShortCorners.width k) (ShortCorners.height k) :=
  (⟨10,by cases k <;> decide⟩,⟨ShortCorners.lastY k+2,by cases k <;> decide⟩)

def cornerOffset (q : Key) (i : ℕ) : ℕ×ℕ :=
  let p := (vertices q).getD (i+1) (0,0)
  let c := (cornerOrientation q i).point (ShortCorners.width (cornerKind q i))
    (ShortCorners.height (cornerKind q i)) (10,10)
  (p.1-c.1,p.2-c.2)

/-- Complete actual box/goal inventory after its chosen D4 transformation. -/
def cornerPiece (q : Key) (i : ℕ) (a b : Bool) : Instance :=
  GridIsometry.reorientInstance (ShortCorners.puzzle (cornerKind q i) a b) (cornerIso q i).geometry

def cornerMatching (q : Key) (i : ℕ) (a b : Bool) :
    SlotMatching (cornerPiece q i a b) (Fin (ShortCorners.count (cornerKind q i))) :=
  (ShortCorners.slotMatching (cornerKind q i) a b).reorient (cornerIso q i).geometry

private def cornerTest (q : Key) (i : ℕ) : Bool :=
  let k := cornerKind q i
  let o := cornerOrientation q i
  let w := ShortCorners.width k
  let h := ShortCorners.height k
  let dx := (cornerOffset q i).1
  let dy := (cornerOffset q i).2
  let c := o.point w h (10,10)
  let near := o.point w h (ShortCorners.sourceX k,10)
  let far := o.point w h (10,ShortCorners.lastY k+2)
  decide (dx+o.width w h≤200007 ∧ dy+o.height w h≤198068 ∧
    (dx+c.1,dy+c.2)=(vertices q).getD (i+1) (0,0) ∧
    (dx+near.1,dy+near.2)=fillerEnd q i ∧ (dx+far.1,dy+far.2)=fillerStart q (i+1))

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem corners_checked : ∀ q : Key,∀ i : Fin ((curve q).length-1),cornerTest q i.val=true := by decide +kernel

theorem corner_fits (q : Key) (i : ℕ) (hi : i+1<(curve q).length) :
    (cornerOffset q i).1+(cornerOrientation q i).width (ShortCorners.width (cornerKind q i)) (ShortCorners.height (cornerKind q i))≤200007 ∧
    (cornerOffset q i).2+(cornerOrientation q i).height (ShortCorners.width (cornerKind q i)) (ShortCorners.height (cornerKind q i))≤198068 := by
  have hh := of_decide_eq_true (corners_checked q ⟨i,by omega⟩)
  exact ⟨hh.1,hh.2.1⟩

def cornerRect (q : Key) (i : ℕ) (hi : i+1<(curve q).length) :
    GridEmbedding ((cornerOrientation q i).width (ShortCorners.width (cornerKind q i)) (ShortCorners.height (cornerKind q i)))
      ((cornerOrientation q i).height (ShortCorners.width (cornerKind q i)) (ShortCorners.height (cornerKind q i))) 200007 198068 :=
  GridEmbedding.translate (cornerOffset q i).1 (cornerOffset q i).2 (corner_fits q i hi).1 (corner_fits q i hi).2

def cornerEmbedding (q : Key) (i : ℕ) (hi : i+1<(curve q).length) :=
  (cornerIso q i).geometry.embedding.trans (cornerRect q i hi)

/-- Both literal physical endpoints meet their actual neighboring long-filler anchors exactly. -/
theorem corner_anchors (q : Key) (i : ℕ) (hi : i+1<(curve q).length) :
    (((cornerEmbedding q i hi).cells (nearAnchor (cornerKind q i))).1.val,
      ((cornerEmbedding q i hi).cells (nearAnchor (cornerKind q i))).2.val)=fillerEnd q i ∧
    (((cornerEmbedding q i hi).cells (farAnchor (cornerKind q i))).1.val,
      ((cornerEmbedding q i hi).cells (farAnchor (cornerKind q i))).2.val)=fillerStart q (i+1) := by
  have hh := of_decide_eq_true (corners_checked q ⟨i,by omega⟩)
  have hn := (cornerOrientation q i).point_cells _ _ (nearAnchor (cornerKind q i))
  have hf := (cornerOrientation q i).point_cells _ _ (farAnchor (cornerKind q i))
  change ((cornerOffset q i).1+((cornerIso q i).geometry.cells (nearAnchor (cornerKind q i))).1.val,
    (cornerOffset q i).2+((cornerIso q i).geometry.cells (nearAnchor (cornerKind q i))).2.val)=_ ∧
    ((cornerOffset q i).1+((cornerIso q i).geometry.cells (farAnchor (cornerKind q i))).1.val,
    (cornerOffset q i).2+((cornerIso q i).geometry.cells (farAnchor (cornerKind q i))).2.val)=_
  rw [show ((cornerIso q i).geometry.cells (nearAnchor (cornerKind q i))).1.val=_ from congrArg Prod.fst hn.symm,
    show ((cornerIso q i).geometry.cells (nearAnchor (cornerKind q i))).2.val=_ from congrArg Prod.snd hn.symm,
    show ((cornerIso q i).geometry.cells (farAnchor (cornerKind q i))).1.val=_ from congrArg Prod.fst hf.symm,
    show ((cornerIso q i).geometry.cells (farAnchor (cornerKind q i))).2.val=_ from congrArg Prod.snd hf.symm]
  exact ⟨hh.2.2.2.1,hh.2.2.2.2⟩

end PushPuzzle.PushFS.Reduction.GateTileRouting
