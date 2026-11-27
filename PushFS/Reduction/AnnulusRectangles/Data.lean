/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.AnnulusInventory
import Mathlib.Tactic.FinCases

/-! Literal rectangles and possible overlap contacts of the complete finite annular piece inventory. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateTileRouting.Inventory


open Gadgets Gadgets.Wires

structure Rectangle where
  x : ℕ
  y : ℕ
  width : ℕ
  height : ℕ
  deriving DecidableEq,Repr

def dimensions (g : GateTileState) : Index g→ℕ×ℕ
  | .inl i => if i=0 then (81,107) else if i=2 then (21,2306) else (2306,21)
  | .inr (.inl ⟨role,.inl j⟩) =>
      let q := key g role
      let o := lineOrientation (original q j.val).travel (fillerFlip q j.val)
      (o.width (lineWidth q j.val) 21,o.height (lineWidth q j.val) 21)
  | .inr (.inl ⟨role,.inr j⟩) =>
      let q := key g role
      let o := cornerOrientation q j.val
      let k := cornerKind q j.val
      (o.width (ShortCorners.width k) (ShortCorners.height k),o.height (ShortCorners.width k) (ShortCorners.height k))
  | .inr (.inr role) =>
      let o := capOrientation (PortAnnulus.outerDirection (g.key role.val).2)
      (o.width 1 3,o.height 1 3)

/-- Dimensions refer to the genuine complete storage pieces, including every helper box. -/
theorem piece_dimensions (g : GateTileState) (i : Index g) :
    (piece g i).width=(dimensions g i).1 ∧ (piece g i).height=(dimensions g i).2 := by
  rcases i with i | (⟨role,j | j⟩ | role)
  · fin_cases i <;> exact ⟨rfl,rfl⟩
  · exact linePiece_dimensions _ _ j.isLt _ _
  · exact ⟨rfl,rfl⟩
  · exact ⟨rfl,rfl⟩

def geometricOffset (g : GateTileState) : Index g→ℕ×ℕ
  | .inl i => ((bufferOffset g.core.isAND).1+GateLead.dx g.core.isAND 2301 i,
      (bufferOffset g.core.isAND).2+GateLead.dy g.core.isAND 2301 i)
  | .inr (.inl ⟨role,.inl j⟩) => lineOffset (key g role) j.val
  | .inr (.inl ⟨role,.inr j⟩) => cornerOffset (key g role) j.val
  | .inr (.inr role) => capOffset (g.key role.val)

theorem geometricOffset_eq (g : GateTileState) (i : Index g) : geometricOffset g i=offset g i := by
  rcases i with i | (⟨role,j | j⟩ | role) <;> rfl

def rectangle (g : GateTileState) (i : Index g) : Rectangle :=
  ⟨(geometricOffset g i).1,(geometricOffset g i).2,(dimensions g i).1,(dimensions g i).2⟩

def Rectangle.Disjoint (r s : Rectangle) : Prop :=
  r.x+r.width≤s.x ∨ s.x+s.width≤r.x ∨ r.y+r.height≤s.y ∨ s.y+s.height≤r.y

instance (r s : Rectangle) : Decidable (r.Disjoint s) := by unfold Rectangle.Disjoint; infer_instance

theorem Rectangle.no_common {r s : Rectangle} (h : r.Disjoint s) {p q : ℕ×ℕ}
    (hp : p.1<r.width ∧ p.2<r.height) (hq : q.1<s.width ∧ q.2<s.height)
    (he : (r.x+p.1,r.y+p.2)=(s.x+q.1,s.y+q.2)) : False := by
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  unfold Rectangle.Disjoint at h
  dsimp only at hx hy
  omega

/-- Core overlaps, the three true buffered frontiers, and the two contacts of each protected corner. -/
def contact (g : GateTileState) (i j : Index g) : Bool :=
  match i,j with
  | .inl _,.inl _ => true
  | .inl i,.inr (.inl ⟨role,.inl j⟩) => decide (i.val=role.val+1 ∧ j.val=0)
  | .inr (.inl ⟨role,.inl j⟩),.inl i => decide (i.val=role.val+1 ∧ j.val=0)
  | .inr (.inl ⟨role,.inl j⟩),.inr (.inl ⟨role',.inr k⟩) =>
      decide (role=role' ∧ (j.val=k.val ∨ j.val=k.val+1))
  | .inr (.inl ⟨role,.inr k⟩),.inr (.inl ⟨role',.inl j⟩) =>
      decide (role=role' ∧ (j.val=k.val ∨ j.val=k.val+1))
  | _,_ => false

abbrev Geometry := Bool×(Fin 3×(Fin 3×Gates.Signals))

def ofGeometry (k : Geometry) : GateTileState :=
  ⟨⟨k.1,⟨false,false,false⟩,⟨false,false,false⟩⟩,k.2.2.2,k.2.1,k.2.2.1⟩

def geometry (g : GateTileState) : Geometry := (g.core.isAND,g.pattern,g.rotation,g.incoming)

def separationTest (k : Geometry) : Bool :=
  let g := ofGeometry k
  let rects := (indices g).map fun i=>(i,rectangle g i)
  rects.all fun (i,r) => rects.all fun (j,s) =>
    if i=j ∨ contact g i j=true then true else decide (r.Disjoint s)

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem separated_checked : ∀ k : Geometry,separationTest k=true := by
  rintro ⟨kind,pattern,rotation,signals⟩
  cases kind <;> fin_cases pattern <;> fin_cases rotation
  all_goals
    rcases signals with ⟨left, upper, right⟩
    cases left <;> cases upper <;> cases right <;> decide +kernel

end PushPuzzle.PushFS.Reduction.GateTileRouting.Inventory
