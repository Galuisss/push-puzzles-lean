/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateStatics.Primitive
public import PushFS.Reduction.AnnulusSeamAnchors

/-! Exact finite slot points and phase-dependent rail intervals compress every physical goal inventory. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics

open Inventory Gadgets Gadgets.Wires
set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

structure Envelope where
  loX : ℕ
  hiX : ℕ
  loY : ℕ
  hiY : ℕ
  deriving DecidableEq, Repr

namespace Envelope

def Contains (r : Envelope) (p : ℕ×ℕ) : Prop :=
  r.loX≤p.1 ∧p.1≤r.hiX ∧r.loY≤p.2 ∧p.2≤r.hiY
instance (r : Envelope) (p : ℕ×ℕ) : Decidable (r.Contains p) := by unfold Contains; infer_instance

def point (p : ℕ×ℕ) : Envelope := ⟨p.1,p.1,p.2,p.2⟩
def rail (n : ℕ) (flip phase : Bool) : Envelope := ⟨2+phase.toNat,n+(if flip then 20 else 0)+phase.toNat,10,10⟩

def placed (o : RectOrientation) (w h dx dy : ℕ) (r : Envelope) : Envelope :=
  let a:=o.point w h (r.loX,r.loY)
  let b:=o.point w h (r.hiX,r.hiY)
  ⟨dx+min a.1 b.1,dx+max a.1 b.1,dy+min a.2 b.2,dy+max a.2 b.2⟩

def Apart (r s : Envelope) : Prop :=
  r.hiX+1<s.loX ∨s.hiX+1<r.loX ∨r.hiY+1<s.loY ∨s.hiY+1<r.loY
instance (r s : Envelope) : Decidable (r.Apart s) := by unfold Apart; infer_instance

theorem point_contains (p : ℕ×ℕ) : (point p).Contains p := ⟨le_refl _,le_refl _,le_refl _,le_refl _⟩

theorem placed_contains (o : RectOrientation) (w h dx dy : ℕ) (r : Envelope) (p : ℕ×ℕ)
    (hp : r.Contains p) :
    (r.placed o w h dx dy).Contains (dx+(o.point w h p).1,dy+(o.point w h p).2) := by
  rcases o with ⟨s,x,y⟩
  rcases p with ⟨px,py⟩
  cases s <;> cases x <;> cases y <;>
    simp only [Contains,placed,RectOrientation.point,RectOrientation.width,RectOrientation.height,Bool.false_eq_true,reduceIte] at hp ⊢ <;>
    omega

theorem apart_not_adjacent {W H : ℕ} (r s : Envelope) (p q : Cell W H)
    (hp : r.Contains (p.1.val,p.2.val)) (hq : s.Contains (q.1.val,q.2.val)) (hs : r.Apart s) (d : Direction) :
    ¬Adjacent d p q := by
  intro ha
  cases d <;> simp only [Adjacent] at ha <;> dsimp only [Contains,Apart] at hp hq hs <;> omega

def join (r s : Envelope) : Envelope := ⟨min r.loX s.loX,max r.hiX s.hiX,min r.loY s.loY,max r.hiY s.hiY⟩
def hull : List Envelope→Envelope
  | []=>point (0,0)
  | [r]=>r
  | r::s::rs=>r.join (hull (s::rs))

theorem join_contains_left (r s : Envelope) (p : ℕ×ℕ) (hp : r.Contains p) : (r.join s).Contains p := by
  dsimp only [Contains,join] at *
  omega

theorem join_contains_right (r s : Envelope) (p : ℕ×ℕ) (hp : s.Contains p) : (r.join s).Contains p := by
  dsimp only [Contains,join] at *
  omega

theorem hull_contains (rs : List Envelope) (r : Envelope) (hr : r∈rs) (p : ℕ×ℕ) (hp : r.Contains p) :
    (hull rs).Contains p := by
  induction rs with
  | nil=>cases hr
  | cons s rs ih=>
    cases rs with
    | nil=>
      have he:=List.mem_singleton.mp hr
      subst r
      exact hp
    | cons t rs=>
      rcases List.mem_cons.mp hr with rfl|hr
      · exact join_contains_left _ _ p hp
      · exact join_contains_right s _ p (ih hr)

end Envelope

def westFrame (kind : Bool) : RectOrientation := ⟨false,true,!kind⟩
def northFrame : RectOrientation := ⟨true,true,true⟩
def eastFrame : RectOrientation := ⟨false,false,true⟩

def envelopes (g : GateTileState) : Inventory.Index g→List Envelope
  | .inl i =>
    let dx:=(Inventory.geometricOffset g (.inl i)).1
    let dy:=(Inventory.geometricOffset g (.inl i)).2
    Fin.cases
      ((Gates.slots g.core.isAND).map fun s=>Envelope.point (dx+(s.position g.core.target).1.val,dy+(s.position g.core.target).2.val))
      (Fin.cases
        [Envelope.placed (westFrame g.core.isAND) 2306 21 dx dy (Envelope.rail 2301 false g.core.target.left)]
        (Fin.cases
          [Envelope.placed northFrame 2306 21 dx dy (Envelope.rail 2301 false g.core.target.upper)]
          (fun _=>[Envelope.placed eastFrame 2306 21 dx dy (Envelope.rail 2301 false (!g.core.target.right))]))) i
  | .inr (.inl ⟨role,.inl j⟩) =>
      [Envelope.placed (lineOrientation (original (key g role) j.val).travel (fillerFlip (key g role) j.val))
        (lineWidth (key g role) j.val) 21 (lineOffset (key g role) j.val).1 (lineOffset (key g role) j.val).2
        (Envelope.rail (fillerSpan (key g role) j.val) (fillerFlip (key g role) j.val) (targetPhase g role))]
  | .inr (.inl ⟨role,.inr j⟩) =>
      (List.finRange (ShortCorners.count (cornerKind (key g role) j.val))).map fun l=>
        let p:=(ShortCorners.template (cornerKind (key g role) j.val)).position (targetPhase g role) l
        let q:=(cornerOrientation (key g role) j.val).point (ShortCorners.width (cornerKind (key g role) j.val))
          (ShortCorners.height (cornerKind (key g role) j.val)) (p.1.val,p.2.val)
        Envelope.point ((cornerOffset (key g role) j.val).1+q.1,(cornerOffset (key g role) j.val).2+q.2)
  | .inr (.inr _) => []

def envelopesApart (g : GateTileState) : Bool :=
  let rects:=((Inventory.indices g).map fun i=>let es:=envelopes g i; (es,Envelope.hull es)).zipIdx
  rects.all fun ((rs,r),i)=>rects.all fun ((ss,s),j)=>
    if i=j ∨r.Apart s then true else rs.all fun r=>ss.all fun s=>decide (r.Apart s)

def goalGeometry (k : Geometry) (b : Gates.Signals) : GateTileState :=
  {ofGeometry k with core:={ (ofGeometry k).core with target:=b}}

private theorem envelopes_geometry (g : GateTileState) (i : Inventory.Index g) :
    envelopes (goalGeometry (geometry g) g.core.target) i=envelopes g i := by
  rcases i with i|(⟨role,j|j⟩|role) <;> rfl

theorem envelopesApart_geometry (g : GateTileState) :
    envelopesApart (goalGeometry (geometry g) g.core.target)=envelopesApart g := by
  have hh:=funext (envelopes_geometry g)
  unfold envelopesApart
  rw [hh]
  rfl

end PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics
