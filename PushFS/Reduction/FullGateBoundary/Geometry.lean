/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.AnnulusRectangles
public import PushFS.Reduction.AnnulusLineCollars

/-! Literal outer-frame geometry of the complete finite gate inventory. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateBoundary

open Gadgets Gadgets.Wires
open Inventory
set_option maxRecDepth 65536
set_option maxHeartbeats 0

def InFrame : Direction→(ℕ×ℕ)→Prop
  | .west,p => p.1<7
  | .east,p => 200000≤p.1
  | .north,p => p.2<7
  | .south,p => 198061≤p.2

def Guard : Direction→(ℕ×ℕ)→Prop
  | .west,p | .east,p => p.2=99035 ∨p.2=99036
  | .north,p | .south,p => p.1=100001 ∨p.1=100002

def Used (g : GateTileState) (face : Direction) : Prop :=
  ∃role : Fin 3,PortAnnulus.outerDirection (g.key role).2=face

instance (f : Direction) (p : ℕ×ℕ) : Decidable (InFrame f p) := by cases f <;> unfold InFrame <;> infer_instance
instance (f : Direction) (p : ℕ×ℕ) : Decidable (Guard f p) := by cases f <;> unfold Guard <;> infer_instance
instance (g : GateTileState) (f : Direction) : Decidable (Used g f) := by unfold Used; infer_instance

def Touches (f : Direction) (r : Rectangle) : Prop :=
  match f with
  | .west => r.x<7
  | .east => 200000<r.x+r.width
  | .north => r.y<7
  | .south => 198061<r.y+r.height

instance (f : Direction) (r : Rectangle) : Decidable (Touches f r) := by cases f <;> unfold Touches <;> infer_instance

def EndPiece (g : GateTileState) (i : Index g) (f : Direction) : Prop :=
  match i with
  | .inl _ => False
  | .inr (.inl ⟨role,.inl j⟩) => j.val+1=(curve (key g role)).length ∧PortAnnulus.outerDirection (g.key role).2=f
  | .inr (.inl ⟨_,.inr _⟩) => False
  | .inr (.inr role) => PortAnnulus.outerDirection (g.key role.val).2=f

instance (g : GateTileState) (i : Index g) (f : Direction) : Decidable (EndPiece g i f) := by
  rcases i with i | (⟨r,j | j⟩ | r) <;> unfold EndPiece <;> infer_instance

private def ownerTest (k : Geometry) : Bool :=
  let g:=ofGeometry k
  (indices g).all fun i=>[Direction.north,.east,.south,.west].all fun f=>
    decide (Touches f (rectangle g i)→EndPiece g i f)

private theorem owners_checked : ∀k : Geometry,ownerTest k=true := by
  rintro ⟨kind,pattern,rotation,signals⟩
  cases kind <;> fin_cases pattern <;> fin_cases rotation
  all_goals revert signals; decide +kernel

private theorem rectangle_geometry (g : GateTileState) (i : Index g) :
    rectangle (ofGeometry (geometry g)) i=rectangle g i := by
  rcases i with i | (⟨r,s | t⟩ | u) <;> rfl

private theorem endPiece_geometry (g : GateTileState) (i : Index g) (f : Direction) :
    EndPiece (ofGeometry (geometry g)) i f=EndPiece g i f := by
  rcases i with i | (⟨r,s | t⟩ | u) <;> rfl

/-- Only a true last line or an output cap reaches any seven-cell exterior frame. -/
private theorem outer_owner (g : GateTileState) (i : Index g) (f : Direction)
    (ht : Touches f (rectangle g i)) : EndPiece g i f := by
  change Index (ofGeometry (geometry g)) at i
  have hh:=owners_checked (geometry g)
  have hp:=List.all_eq_true.mp (List.all_eq_true.mp hh i (mem_indices (ofGeometry (geometry g)) i)) f (by cases f <;> simp)
  have hp' : Touches f (rectangle (ofGeometry (geometry g)) i)→EndPiece (ofGeometry (geometry g)) i f :=
    of_decide_eq_true hp
  rw [rectangle_geometry g i,endPiece_geometry g i] at hp'
  exact hp' ht

theorem raw_owner (g : GateTileState) (i : Index g) (f : Direction)
    (q : Cell (piece g i).width (piece g i).height)
    (hf : InFrame f ((offset g i).1+q.1.val,(offset g i).2+q.2.val)) : EndPiece g i f := by
  apply outer_owner
  have hx:=q.1.isLt
  have hy:=q.2.isLt
  have hd:=piece_dimensions g i
  unfold rectangle
  rw [geometricOffset_eq]
  cases f <;> dsimp only [Touches,InFrame] at * <;> omega

/-- Exact normal-line endpoint placement, including the extra input padding cell. -/
def EndPlacement (d : Direction) (incoming : Bool) (n dx dy : ℕ) : Prop :=
  match d with
  | .west => dx=1-incoming.toNat ∧dy=99024
  | .east => dx+n+5=200006+incoming.toNat ∧dy=99024
  | .north => dx=99993 ∧dy=1-incoming.toNat
  | .south => dx=99993 ∧dy+n+5=198067+incoming.toNat

instance (d : Direction) (b : Bool) (n x y : ℕ) : Decidable (EndPlacement d b n x y) := by
  cases d <;> unfold EndPlacement <;> infer_instance

theorem last_line_metadata : ∀q : Key,∀j : Fin (curve q).length,
    j.val+1=(curve q).length→
    fillerFlip q j.val=false ∧(original q j.val).travel=PortAnnulus.outerDirection q.1.2 ∧
    EndPlacement (PortAnnulus.outerDirection q.1.2) q.2 (fillerSpan q j.val)
      (lineOffset q j.val).1 (lineOffset q j.val).2 := by decide +kernel

theorem last_valid : ∀q : Key,0<(curve q).length := by decide +kernel

end PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateBoundary
