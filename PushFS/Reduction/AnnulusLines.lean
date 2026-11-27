/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.AnnulusFillers
public import PushFS.Gadgets.Wires.FlippedChain

/-! Actual complete long-chain storage pieces filling every trimmed annular segment. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateTileRouting


open Gadgets.Wires

def lineBase (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool) : Instance :=
  if flip then (FlippedChain.atlas n hn (FlippedChain.uniform a) (FlippedChain.uniform b)).puzzle
  else Chain.puzzle n hn a b

def lineLabels (flip : Bool) (n : ℕ) : Type :=
  match flip with
  | false => Chain.Label n
  | true => FlippedChain.Label n

instance (flip : Bool) (n : ℕ) : Fintype (lineLabels flip n) := by
  cases flip <;> unfold lineLabels <;> infer_instance

def lineMatching (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool) :
    SlotMatching (lineBase flip n hn a b) (lineLabels flip n) := by
  cases flip
  · exact Chain.slotMatching n hn a b
  · exact (FlippedChain.atlas n hn (FlippedChain.uniform a) (FlippedChain.uniform b)).slotMatching

theorem line_dimensions (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool) :
    (lineBase flip n hn a b).width=n+(if flip then 25 else 5) ∧ (lineBase flip n hn a b).height=21 := by
  cases flip <;> exact ⟨rfl,rfl⟩

/-- A flipped line starts with the opposite guard and ends with the shared ordinary guard. -/
def lineOrientation (d : Direction) (flip : Bool) : RectOrientation :=
  match d with
  | .east => ⟨false,false,flip⟩
  | .west => ⟨false,true,flip⟩
  | .south => ⟨true,!flip,false⟩
  | .north => ⟨true,!flip,true⟩

theorem line_direction : ∀ d : Direction,∀ f : Bool,(lineOrientation d f).direction .east=d := by decide +kernel

def lineWidth (q : Key) (i : ℕ) : ℕ := fillerSpan q i+(if fillerFlip q i then 25 else 5)

def lineOffset (q : Key) (i : ℕ) : ℕ×ℕ :=
  let c := (lineOrientation (original q i).travel (fillerFlip q i)).point (lineWidth q i) 21 (2,10)
  ((fillerStart q i).1-c.1,(fillerStart q i).2-c.2)

private def lineTest (q : Key) (i : ℕ) : Bool :=
  let w := lineWidth q i
  let o := lineOrientation (original q i).travel (fillerFlip q i)
  let p := o.point w 21 (2,10)
  let r := o.point w 21 ((filler q i).span+2,10)
  let dx := (lineOffset q i).1
  let dy := (lineOffset q i).2
  decide (dx+o.width w 21≤200007 ∧ dy+o.height w 21≤198068 ∧
    (dx+p.1,dy+p.2)=fillerStart q i ∧ (dx+r.1,dy+r.2)=fillerEnd q i)

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem lines_checked : ∀ q : Key,∀ i : Fin (curve q).length,lineTest q i.val=true := by decide +kernel

theorem line_fits (q : Key) (i : ℕ) (hi : i<(curve q).length) :
    (lineOffset q i).1+(lineOrientation (original q i).travel (fillerFlip q i)).width (lineWidth q i) 21≤200007 ∧
    (lineOffset q i).2+(lineOrientation (original q i).travel (fillerFlip q i)).height (lineWidth q i) 21≤198068 := by
  have hh := of_decide_eq_true (lines_checked q ⟨i,hi⟩)
  exact ⟨hh.1,hh.2.1⟩

def linePiece (q : Key) (i : ℕ) (hi : i<(curve q).length) (a b : Bool) : Instance :=
  let base := lineBase (fillerFlip q i) (fillerSpan q i) (filler_shape q i hi).2.1 a b
  GridIsometry.reorientInstance base
    ((lineOrientation (original q i).travel (fillerFlip q i)).axis base.width base.height).geometry

def lineSlotMatching (q : Key) (i : ℕ) (hi : i<(curve q).length) (a b : Bool) :
    SlotMatching (linePiece q i hi a b) (lineLabels (fillerFlip q i) (fillerSpan q i)) :=
  let base := lineBase (fillerFlip q i) (fillerSpan q i) (filler_shape q i hi).2.1 a b
  (lineMatching (fillerFlip q i) (fillerSpan q i) (filler_shape q i hi).2.1 a b).reorient
    ((lineOrientation (original q i).travel (fillerFlip q i)).axis base.width base.height).geometry

/-- The genuine oriented long-line piece has exactly the dimensions used by the checked physical placement. -/
theorem linePiece_dimensions (q : Key) (i : ℕ) (hi : i<(curve q).length) (a b : Bool) :
    (linePiece q i hi a b).width=(lineOrientation (original q i).travel (fillerFlip q i)).width (lineWidth q i) 21 ∧
    (linePiece q i hi a b).height=(lineOrientation (original q i).travel (fillerFlip q i)).height (lineWidth q i) 21 := by
  have hd := line_dimensions (fillerFlip q i) (fillerSpan q i) (filler_shape q i hi).2.1 a b
  change (lineOrientation (original q i).travel (fillerFlip q i)).width
      (lineBase (fillerFlip q i) (fillerSpan q i) (filler_shape q i hi).2.1 a b).width
      (lineBase (fillerFlip q i) (fillerSpan q i) (filler_shape q i hi).2.1 a b).height=_ ∧
    (lineOrientation (original q i).travel (fillerFlip q i)).height
      (lineBase (fillerFlip q i) (fillerSpan q i) (filler_shape q i hi).2.1 a b).width
      (lineBase (fillerFlip q i) (fillerSpan q i) (filler_shape q i hi).2.1 a b).height=_
  rw [hd.1,hd.2]
  exact ⟨rfl,rfl⟩

def lineRect (q : Key) (i : ℕ) (hi : i<(curve q).length) (a b : Bool) :
    GridEmbedding (linePiece q i hi a b).width (linePiece q i hi a b).height 200007 198068 :=
  GridEmbedding.translate (lineOffset q i).1 (lineOffset q i).2
    (by rw [(linePiece_dimensions q i hi a b).1]; exact (line_fits q i hi).1)
    (by rw [(linePiece_dimensions q i hi a b).2]; exact (line_fits q i hi).2)

end PushPuzzle.PushFS.Reduction.GateTileRouting
