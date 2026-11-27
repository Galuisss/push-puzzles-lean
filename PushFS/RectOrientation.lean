/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.AxisIsometry

/-! Executable eight-way rectangular geometry with literal coordinate and guarded-turn direction contracts. -/

@[expose] public section

namespace PushPuzzle.PushFS


structure RectOrientation where
  swapAxes : Bool
  flipX : Bool
  flipY : Bool
  deriving DecidableEq

instance : Fintype RectOrientation where
  elems := {⟨false,false,false⟩,⟨false,true,false⟩,⟨false,false,true⟩,⟨false,true,true⟩,
    ⟨true,false,false⟩,⟨true,true,false⟩,⟨true,false,true⟩,⟨true,true,true⟩}
  complete o := by
    rcases o with ⟨s,x,y⟩
    cases s <;> cases x <;> cases y <;> simp

namespace RectOrientation

def width (o : RectOrientation) (w h : ℕ) : ℕ := if o.swapAxes then h else w
def height (o : RectOrientation) (w h : ℕ) : ℕ := if o.swapAxes then w else h

/-- The actual grid isometry and literal rail/sink coordinate transport for each orientation. -/
def axis (o : RectOrientation) (w h : ℕ) : AxisIsometry w h (o.width w h) (o.height w h) :=
  match o with
  | ⟨false,false,false⟩ => AxisIsometry.refl w h
  | ⟨false,true,false⟩ => AxisIsometry.reflectX w h
  | ⟨false,false,true⟩ => AxisIsometry.reflectY w h
  | ⟨false,true,true⟩ => (AxisIsometry.reflectX w h).trans (AxisIsometry.reflectY w h)
  | ⟨true,false,false⟩ => AxisIsometry.transpose w h
  | ⟨true,true,false⟩ => (AxisIsometry.transpose w h).trans (AxisIsometry.reflectX h w)
  | ⟨true,false,true⟩ => (AxisIsometry.transpose w h).trans (AxisIsometry.reflectY h w)
  | ⟨true,true,true⟩ => ((AxisIsometry.transpose w h).trans (AxisIsometry.reflectX h w)).trans (AxisIsometry.reflectY h w)

def direction (o : RectOrientation) : Direction→Direction := (o.axis 1 1).geometry.directions

theorem direction_eq (o : RectOrientation) (w h : ℕ) (d : Direction) :
    (o.axis w h).geometry.directions d=o.direction d := by
  rcases o with ⟨s,x,y⟩
  cases s <;> cases x <;> cases y <;> rfl

/-- Literal natural-coordinate evaluation of the same finite rectangle transformation. -/
def point (o : RectOrientation) (w h : ℕ) (p : ℕ×ℕ) : ℕ×ℕ :=
  let q := if o.swapAxes then (p.2,p.1) else p
  (if o.flipX then o.width w h-(q.1+1) else q.1,
   if o.flipY then o.height w h-(q.2+1) else q.2)

theorem point_cells (o : RectOrientation) (w h : ℕ) (p : Cell w h) :
    o.point w h (p.1.val,p.2.val)=
      (((o.axis w h).geometry.cells p).1.val,((o.axis w h).geometry.cells p).2.val) := by
  rcases o with ⟨s,x,y⟩
  cases s <;> cases x <;> cases y <;> rfl

/-- Horizontal travel uses the shared south wall; vertical travel uses the shared west wall. -/
def guardSide : Direction→Direction
  | .east | .west => .south
  | .north | .south => .west

def Perpendicular (d e : Direction) : Prop :=
  ((d=.east ∨ d=.west) ∧ (e=.north ∨ e=.south)) ∨
    ((d=.north ∨ d=.south) ∧ (e=.east ∨ e=.west))

instance (d e : Direction) : Decidable (Perpendicular d e) := by unfold Perpendicular; infer_instance

def all : List RectOrientation :=
  [⟨false,false,false⟩,⟨false,true,false⟩,⟨false,false,true⟩,⟨false,true,true⟩,
   ⟨true,false,false⟩,⟨true,true,false⟩,⟨true,false,true⟩,⟨true,true,true⟩]

/-- Select the actual D4 image carrying the base west-to-south turn to the requested travel directions. -/
def choose (d e : Direction) : RectOrientation :=
  (all.find? fun o=>o.direction .west==d && o.direction .south==e).getD ⟨false,false,false⟩

theorem choose_correct : ∀ d e : Direction,Perpendicular d e →
    (choose d e).direction .west=d ∧ (choose d e).direction .south=e := by decide +kernel

def nearFlip (d e : Direction) : Bool := decide ((choose d e).direction .south≠guardSide d)
def farFlip (d e : Direction) : Bool := decide ((choose d e).direction .west≠guardSide e)

end RectOrientation
end PushPuzzle.PushFS
