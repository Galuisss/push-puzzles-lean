/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateStatics.Cover
public import PushFS.Reduction.FullGateBoundary

/-! Constant actual exterior rail charts cover the true whole-board boundary and output guard caps. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics

set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def ribbonWidth : Direction→ℕ
  | .east | .west => 7
  | .north | .south => 5
def ribbonHeight : Direction→ℕ
  | .east | .west => 5
  | .north | .south => 7
def ribbonOffset : Direction→ℕ×ℕ
  | .west => (0,99032)
  | .east => (200000,99032)
  | .north => (100001,0)
  | .south => (100001,198061)

def ribbonWall (d : Direction) (p : Cell (ribbonWidth d) (ribbonHeight d)) : Bool :=
  match d with
  | .west | .east => decide (p.2.val=3 ∨p.2.val=4)
  | .north | .south => decide (p.1.val=0 ∨p.1.val=1)

def ribbonName (d : Direction) (p : Cell (ribbonWidth d) (ribbonHeight d)) : AxisTrack :=
  match d with
  | .west | .east => if p.2.val=2 then .horizontal 2 else .outside
  | .north | .south => if p.1.val=2 then .vertical 2 else .outside

def ribbonBoard (d : Direction) : Board (ribbonWidth d) (ribbonHeight d) :=
  ⟨Finset.univ.filter (fun p=>ribbonWall d p=true),∅⟩

theorem ribbon_wall_correct (d : Direction) (p : Cell (ribbonWidth d) (ribbonHeight d)) :
    ribbonWall d p=true ↔p∈(ribbonBoard d).walls := by simp only [ribbonBoard,Finset.mem_filter,Finset.mem_univ,true_and]

theorem ribbon_supported : ∀d : Direction,∀p,AxisTrack.supportTest (ribbonName d) p=true := by decide +kernel

theorem ribbon_checked : ∀d : Direction,
    checkDisplacements (ribbonWall d) (AxisTrack.activeSources (ribbonName d))
      (AxisTrack.strongAllowed (ribbonName d))=true := by decide +kernel

def ribbonClassifier (d : Direction) : AxisClassifier (ribbonBoard d) :=
  AxisClassifier.of_strong_check (ribbon_wall_correct d) (ribbonName d) (ribbon_supported d) (ribbon_checked d)

theorem ribbon_fits : ∀d : Direction,
    (ribbonOffset d).1+ribbonWidth d≤200007 ∧(ribbonOffset d).2+ribbonHeight d≤198068 := by decide +kernel

def ribbonChart (d : Direction) : TranslatedAxisChart 200007 198068 where
  width:=ribbonWidth d
  height:=ribbonHeight d
  board:=ribbonBoard d
  dx:=(ribbonOffset d).1
  dy:=(ribbonOffset d).2
  fits_x:=(ribbon_fits d).1
  fits_y:=(ribbon_fits d).2
  classifier:=ribbonClassifier d

private theorem ribbon_frame (d : Direction) (p : Cell (ribbonWidth d) (ribbonHeight d)) :
    FullGateBoundary.InFrame d (((ribbonChart d).embedding.cells p).1.val,((ribbonChart d).embedding.cells p).2.val) := by
  have hx:=p.1.isLt
  have hy:=p.2.isLt
  cases d <;>
    change FullGateBoundary.InFrame _ ((ribbonOffset _).1+p.1.val,(ribbonOffset _).2+p.2.val) <;>
    dsimp only [FullGateBoundary.InFrame,ribbonWidth,ribbonHeight,ribbonOffset] at * <;> omega

theorem ribbon_walls (g : GateTileState) (d : Direction) (hu : FullGateBoundary.Used g d) :
    (ribbonChart d).embedding.WallsAgree (ribbonBoard d) (fullPuzzle g).board := by
  intro p
  apply (FullGateBoundary.walls g d _ (ribbon_frame d p)).trans
  apply Iff.trans ?_ (ribbon_wall_correct d p)
  simp only [hu,true_and]
  have hx:=p.1.isLt
  have hy:=p.2.isLt
  change FullGateBoundary.Guard d ((ribbonOffset d).1+p.1.val,(ribbonOffset d).2+p.2.val)↔ribbonWall d p=true
  cases d <;> simp only [FullGateBoundary.Guard,ribbonOffset,ribbonWall,decide_eq_true_eq] <;> omega

def outerChart (g : GateTileState) (role : Fin 3) : TranslatedAxisChart 200007 198068 :=
  ribbonChart (PortAnnulus.outerDirection (g.key role).2)

theorem outer_walls (g : GateTileState) (role : Fin 3) :
    (outerChart g role).embedding.WallsAgree (outerChart g role).board (fullPuzzle g).board :=
  ribbon_walls g _ ⟨role,rfl⟩

end PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics
