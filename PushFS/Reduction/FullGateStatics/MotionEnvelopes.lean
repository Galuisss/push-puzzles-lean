/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateStatics.Envelopes

/-! Phase-independent motion intervals of the complete physical primitive inventory. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics

open Inventory Gadgets Gadgets.Wires
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

namespace Envelope

def MotionApart (r s : Envelope) : Prop :=
  r.hiX<s.loX ∨s.hiX<r.loX ∨r.hiY<s.loY ∨s.hiY<r.loY
instance (r s : Envelope) : Decidable (r.MotionApart s) := by unfold MotionApart; infer_instance

def motionRail (n : ℕ) (flip : Bool) : Envelope := ⟨2,n+(if flip then 20 else 0)+1,10,10⟩

def motionSlot (s : Gates.Slot) (dx dy : ℕ) : Envelope :=
  (point (dx+s.zero.1.val,dy+s.zero.2.val)).join (point (dx+s.one.1.val,dy+s.one.2.val))

end Envelope

def motionEnvelopes (g : GateTileState) : Inventory.Index g→List Envelope
  | .inl i =>
    let dx:=(Inventory.geometricOffset g (.inl i)).1
    let dy:=(Inventory.geometricOffset g (.inl i)).2
    Fin.cases
      ((Gates.slots g.core.isAND).map fun s=>Envelope.motionSlot s dx dy)
      (Fin.cases
        [Envelope.placed (westFrame g.core.isAND) 2306 21 dx dy (Envelope.motionRail 2301 false)]
        (Fin.cases
          [Envelope.placed northFrame 2306 21 dx dy (Envelope.motionRail 2301 false)]
          (fun _=>[Envelope.placed eastFrame 2306 21 dx dy (Envelope.motionRail 2301 false)]))) i
  | .inr (.inl ⟨role,.inl j⟩) =>
      [Envelope.placed (lineOrientation (original (key g role) j.val).travel (fillerFlip (key g role) j.val))
        (lineWidth (key g role) j.val) 21 (lineOffset (key g role) j.val).1 (lineOffset (key g role) j.val).2
        (Envelope.motionRail (fillerSpan (key g role) j.val) (fillerFlip (key g role) j.val))]
  | .inr (.inl ⟨role,.inr j⟩) =>
      (List.finRange (ShortCorners.count (cornerKind (key g role) j.val))).map fun l=>
        let k:=cornerKind (key g role) j.val
        let r:=(Envelope.point (((ShortCorners.template k).position false l).1.val,
          ((ShortCorners.template k).position false l).2.val)).join
          (Envelope.point (((ShortCorners.template k).position true l).1.val,
            ((ShortCorners.template k).position true l).2.val))
        Envelope.placed (cornerOrientation (key g role) j.val) (ShortCorners.width k) (ShortCorners.height k)
          (cornerOffset (key g role) j.val).1 (cornerOffset (key g role) j.val).2 r
  | .inr (.inr _) => []

def motionsApart (g : GateTileState) : Bool :=
  let rects:=((Inventory.indices g).map fun i=>let es:=motionEnvelopes g i; (es,Envelope.hull es)).zipIdx
  rects.all fun ((rs,r),i)=>rects.all fun ((ss,s),j)=>
    if i=j ∨r.MotionApart s then true else rs.all fun r=>ss.all fun s=>decide (r.MotionApart s)

end PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics
