/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.OutMovement
public import PushFS.Gadgets.Wires.Catalog.InMovement
public import PushFS.Gadgets.Wires.Catalog.PlacedSemantics
public import PushFS.Gadgets.Wires.Catalog.OutThinFrame
public import PushFS.Gadgets.Wires.Catalog.InThinFrame

/-! Literal five-column endpoint wall stencils of all seven full physical ordinary cells. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog

set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

inductive Face | west | east | north | south
  deriving DecidableEq

/-- The common actual 5×21 seam chart: the vertical charts are clockwise images. -/
def faceCell (f : Face) (p : PushFS.Cell 5 21) : Cell :=
  match f with
  | .west => (⟨p.1.val,by change _<200005; have:=p.1.isLt; omega⟩,⟨99023+p.2.val,by change _<198066; have:=p.2.isLt; omega⟩)
  | .east => (⟨200000+p.1.val,by change _<200005; have:=p.1.isLt; omega⟩,⟨99023+p.2.val,by change _<198066; have:=p.2.isLt; omega⟩)
  | .north => (⟨99992+(20-p.2.val),by change _<200005; have:=p.2.isLt; omega⟩,⟨p.1.val,by change _<198066; have:=p.1.isLt; omega⟩)
  | .south => (⟨99992+(20-p.2.val),by change _<200005; have:=p.2.isLt; omega⟩,⟨198061+p.1.val,by change _<198066; have:=p.1.isLt; omega⟩)

def sourceFace : Kind→Face
  | .east | .eastSouth=>.west
  | .west | .westSouth=>.east
  | .south | .southEast | .southWest=>.north

def targetFace : Kind→Face
  | .east | .southEast=>.east
  | .west | .southWest=>.west
  | .south | .westSouth | .eastSouth=>.south

def padding (k : Kind) (a b : Bool) := GridEmbedding.translate (dx k) (dy k) (fitsX k a b) (fitsY k a b)

theorem padding_walls (k : Kind) (a b : Bool) :
    (padding k a b).WallsAgree (base k a b).board (puzzle k a b).board :=
  placed_walls (baseMatching k a b) (dx k) (dy k) (fitsX k a b) (fitsY k a b)

@[simp] theorem padding_x (k : Kind) (a b : Bool) (p : PushFS.Cell (base k a b).width (base k a b).height) :
    ((padding k a b).cells p).1.val=dx k+p.1.val := rfl
@[simp] theorem padding_y (k : Kind) (a b : Bool) (p : PushFS.Cell (base k a b).width (base k a b).height) :
    ((padding k a b).cells p).2.val=dy k+p.2.val := rfl
@[simp] theorem reflect_x {w h : ℕ} (p : PushFS.Cell w h) :
    ((GridIsometry.reflectX w h).cells p).1.val=w-(p.1.val+1) := rfl
@[simp] theorem reflect_y {w h : ℕ} (p : PushFS.Cell w h) :
    ((GridIsometry.reflectX w h).cells p).2.val=p.2.val := rfl
@[simp] theorem transpose_x {w h : ℕ} (p : PushFS.Cell w h) :
    ((GridIsometry.transpose w h).cells p).1.val=p.2.val := rfl
@[simp] theorem transpose_y {w h : ℕ} (p : PushFS.Cell w h) :
    ((GridIsometry.transpose w h).cells p).2.val=p.1.val := rfl
private theorem east_west_walls (a b : Bool) (p : PushFS.Cell 5 21) :
    faceCell .west p∈(puzzle .east a b).board.walls ↔p.2.val=11 ∨p.2.val=12 := by
  let q : Chain.C 200000 := (⟨p.1.val,by have:=p.1.isLt; omega⟩,⟨p.2.val,by have:=p.2.isLt; omega⟩)
  have he : faceCell .west p=(padding .east a b).cells (q) := by
    have hx0 : (q).1.val=q.1.val := by rfl
    have hy0 : (q).2.val=q.2.val := by rfl
    dsimp only [q] at hx0 hy0
    apply Prod.ext <;> apply Fin.ext
    · change p.1.val=0+(q.1.val)
      dsimp only [q]; omega
    · rfl
  rw [he]
  apply Iff.trans (padding_walls .east a b (q))
  change q∈((Chain.board 200000 (by decide) (Chain.boxes 200000 (by decide) (Chain.uniform 200000 b)))).walls↔_
  change q∈Chain.walls 200000 (by decide)↔_
  rw [Polyline.chain_left5 200000 (by decide) q (by dsimp only [q]; have:=p.1.isLt; omega)]

private theorem east_east_walls (a b : Bool) (p : PushFS.Cell 5 21) :
    faceCell .east p∈(puzzle .east a b).board.walls ↔p.2.val=11 ∨p.2.val=12 := by
  let q : Chain.C 200000 := (⟨200000+p.1.val,by have:=p.1.isLt; omega⟩,⟨p.2.val,by have:=p.2.isLt; omega⟩)
  have he : faceCell .east p=(padding .east a b).cells (q) := by
    have hx0 : (q).1.val=q.1.val := by rfl
    have hy0 : (q).2.val=q.2.val := by rfl
    dsimp only [q] at hx0 hy0
    apply Prod.ext <;> apply Fin.ext
    · change 200000+p.1.val=0+(q.1.val)
      dsimp only [q]; omega
    · rfl
  rw [he]
  apply Iff.trans (padding_walls .east a b (q))
  change q∈((Chain.board 200000 (by decide) (Chain.boxes 200000 (by decide) (Chain.uniform 200000 b)))).walls↔_
  change q∈Chain.walls 200000 (by decide)↔_
  rw [Polyline.chain_right7 200000 (by decide) q (by dsimp only [q]; have:=p.1.isLt; omega)]

private theorem west_west_walls (a b : Bool) (p : PushFS.Cell 5 21) :
    faceCell .west p∈(puzzle .west a b).board.walls ↔p.2.val=11 ∨p.2.val=12 := by
  let q : Chain.C 200000 := (⟨200004-p.1.val,by have:=p.1.isLt; omega⟩,⟨p.2.val,by have:=p.2.isLt; omega⟩)
  have he : faceCell .west p=(padding .west a b).cells ((GridIsometry.reflectX 200005 21).cells (q)) := by
    have hx0 : (q).1.val=q.1.val := by rfl
    have hy0 : (q).2.val=q.2.val := by rfl
    dsimp only [q] at hx0 hy0
    apply Prod.ext <;> apply Fin.ext
    · change p.1.val=0+(200005-(q.1.val+1))
      dsimp only [q]; omega
    · rfl
  rw [he]
  apply Iff.trans (padding_walls .west a b ((GridIsometry.reflectX 200005 21).cells (q)))
  change (GridIsometry.reflectX 200005 21).cells (q)∈((GridIsometry.reflectX 200005 21).board ((Chain.board 200000 (by decide) (Chain.boxes 200000 (by decide) (Chain.uniform 200000 b))))).walls↔_
  repeat rw [GridIsometry.mem_walls]
  change q∈Chain.walls 200000 (by decide)↔_
  rw [Polyline.chain_right7 200000 (by decide) q (by dsimp only [q]; have:=p.1.isLt; omega)]

private theorem west_east_walls (a b : Bool) (p : PushFS.Cell 5 21) :
    faceCell .east p∈(puzzle .west a b).board.walls ↔p.2.val=11 ∨p.2.val=12 := by
  let q : Chain.C 200000 := (⟨4-p.1.val,by have:=p.1.isLt; omega⟩,⟨p.2.val,by have:=p.2.isLt; omega⟩)
  have he : faceCell .east p=(padding .west a b).cells ((GridIsometry.reflectX 200005 21).cells (q)) := by
    have hx0 : (q).1.val=q.1.val := by rfl
    have hy0 : (q).2.val=q.2.val := by rfl
    dsimp only [q] at hx0 hy0
    apply Prod.ext <;> apply Fin.ext
    · change 200000+p.1.val=0+(200005-(q.1.val+1))
      dsimp only [q]; omega
    · rfl
  rw [he]
  apply Iff.trans (padding_walls .west a b ((GridIsometry.reflectX 200005 21).cells (q)))
  change (GridIsometry.reflectX 200005 21).cells (q)∈((GridIsometry.reflectX 200005 21).board ((Chain.board 200000 (by decide) (Chain.boxes 200000 (by decide) (Chain.uniform 200000 b))))).walls↔_
  repeat rw [GridIsometry.mem_walls]
  change q∈Chain.walls 200000 (by decide)↔_
  rw [Polyline.chain_left5 200000 (by decide) q (by dsimp only [q]; have:=p.1.isLt; omega)]

private theorem south_north_walls (a b : Bool) (p : PushFS.Cell 5 21) :
    faceCell .north p∈(puzzle .south a b).board.walls ↔p.2.val=11 ∨p.2.val=12 := by
  let q : Chain.C 198061 := (⟨p.1.val,by have:=p.1.isLt; omega⟩,⟨p.2.val,by have:=p.2.isLt; omega⟩)
  have he : faceCell .north p=(padding .south a b).cells ((GridIsometry.reflectX 21 198066).cells ((GridIsometry.transpose 198066 21).cells (q))) := by
    have hx0 : (q).1.val=q.1.val := by rfl
    have hy0 : (q).2.val=q.2.val := by rfl
    dsimp only [q] at hx0 hy0
    apply Prod.ext <;> apply Fin.ext
    · change 99992+(20-p.2.val)=99992+(21-(q.2.val+1))
      dsimp only [q]; omega
    · change p.1.val=0+(q.1.val)
      dsimp only [q]; omega
  rw [he]
  apply Iff.trans (padding_walls .south a b ((GridIsometry.reflectX 21 198066).cells ((GridIsometry.transpose 198066 21).cells (q))))
  change (GridIsometry.reflectX 21 198066).cells ((GridIsometry.transpose 198066 21).cells (q))∈((GridIsometry.reflectX 21 198066).board ((GridIsometry.transpose 198066 21).board ((Chain.board 198061 (by decide) (Chain.boxes 198061 (by decide) (Chain.uniform 198061 b)))))).walls↔_
  repeat rw [GridIsometry.mem_walls]
  change q∈Chain.walls 198061 (by decide)↔_
  rw [Polyline.chain_left5 198061 (by decide) q (by dsimp only [q]; have:=p.1.isLt; omega)]

private theorem south_south_walls (a b : Bool) (p : PushFS.Cell 5 21) :
    faceCell .south p∈(puzzle .south a b).board.walls ↔p.2.val=11 ∨p.2.val=12 := by
  let q : Chain.C 198061 := (⟨198061+p.1.val,by have:=p.1.isLt; omega⟩,⟨p.2.val,by have:=p.2.isLt; omega⟩)
  have he : faceCell .south p=(padding .south a b).cells ((GridIsometry.reflectX 21 198066).cells ((GridIsometry.transpose 198066 21).cells (q))) := by
    have hx0 : (q).1.val=q.1.val := by rfl
    have hy0 : (q).2.val=q.2.val := by rfl
    dsimp only [q] at hx0 hy0
    apply Prod.ext <;> apply Fin.ext
    · change 99992+(20-p.2.val)=99992+(21-(q.2.val+1))
      dsimp only [q]; omega
    · change 198061+p.1.val=0+(q.1.val)
      dsimp only [q]; omega
  rw [he]
  apply Iff.trans (padding_walls .south a b ((GridIsometry.reflectX 21 198066).cells ((GridIsometry.transpose 198066 21).cells (q))))
  change (GridIsometry.reflectX 21 198066).cells ((GridIsometry.transpose 198066 21).cells (q))∈((GridIsometry.reflectX 21 198066).board ((GridIsometry.transpose 198066 21).board ((Chain.board 198061 (by decide) (Chain.boxes 198061 (by decide) (Chain.uniform 198061 b)))))).walls↔_
  repeat rw [GridIsometry.mem_walls]
  change q∈Chain.walls 198061 (by decide)↔_
  rw [Polyline.chain_right7 198061 (by decide) q (by dsimp only [q]; have:=p.1.isLt; omega)]

private theorem westSouth_east_walls (a b : Bool) (p : PushFS.Cell 5 21) :
    faceCell .east p∈(puzzle .westSouth a b).board.walls ↔p.2.val=11 ∨p.2.val=12 := by
  let q : Chain.C 99970 := (⟨4-p.1.val,by have:=p.1.isLt; omega⟩,⟨p.2.val,by have:=p.2.isLt; omega⟩)
  have he : faceCell .east p=(padding .westSouth a b).cells ((Polyline.L.inEmbed 99970 98999 (by decide) (by decide)).cells q) := by
    have hx0 : ((Polyline.L.inEmbed 99970 98999 (by decide) (by decide)).cells q).1.val=38+(99974-q.1.val) := by exact Polyline.L.in_x 99970 98999 (by decide) (by decide) q
    have hy0 : ((Polyline.L.inEmbed 99970 98999 (by decide) (by decide)).cells q).2.val=q.2.val := by exact Polyline.L.in_y 99970 98999 (by decide) (by decide) q
    dsimp only [q] at hx0 hy0
    apply Prod.ext <;> apply Fin.ext
    · change 200000+p.1.val=99992+(((Polyline.L.inEmbed 99970 98999 (by decide) (by decide)).cells q).1.val)
      dsimp only [q]; omega
    · change 99023+p.2.val=99023+(((Polyline.L.inEmbed 99970 98999 (by decide) (by decide)).cells q).2.val)
      dsimp only [q]; omega
  rw [he]
  apply Iff.trans (padding_walls .westSouth a b ((Polyline.L.inEmbed 99970 98999 (by decide) (by decide)).cells q))
  change (Polyline.L.inEmbed 99970 98999 (by decide) (by decide)).cells q∈((Polyline.L.atlas 99970 98999 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).board).walls↔_
  rw [Polyline.L.board_eq,Polyline.L.in_walls_agree]
  change q∈Chain.walls 99970 (by decide)↔_
  rw [Polyline.chain_left5 99970 (by decide) q (by dsimp only [q]; have:=p.1.isLt; omega)]

private theorem westSouth_south_walls (a b : Bool) (p : PushFS.Cell 5 21) :
    faceCell .south p∈(puzzle .westSouth a b).board.walls ↔p.2.val=11 ∨p.2.val=12 := by
  let q : Chain.C 98999 := (⟨98999+p.1.val,by have:=p.1.isLt; omega⟩,⟨p.2.val,by have:=p.2.isLt; omega⟩)
  have he : faceCell .south p=(padding .westSouth a b).cells ((Polyline.L.outEmbed 99970 98999 (by decide) (by decide)).cells q) := by
    have hx0 : ((Polyline.L.outEmbed 99970 98999 (by decide) (by decide)).cells q).1.val=20-q.2.val := by exact Polyline.L.out_x 99970 98999 (by decide) (by decide) q
    have hy0 : ((Polyline.L.outEmbed 99970 98999 (by decide) (by decide)).cells q).2.val=39+q.1.val := by exact Polyline.L.out_y 99970 98999 (by decide) (by decide) q
    dsimp only [q] at hx0 hy0
    apply Prod.ext <;> apply Fin.ext
    · change 99992+(20-p.2.val)=99992+(((Polyline.L.outEmbed 99970 98999 (by decide) (by decide)).cells q).1.val)
      dsimp only [q]; omega
    · change 198061+p.1.val=99023+(((Polyline.L.outEmbed 99970 98999 (by decide) (by decide)).cells q).2.val)
      dsimp only [q]; omega
  rw [he]
  apply Iff.trans (padding_walls .westSouth a b ((Polyline.L.outEmbed 99970 98999 (by decide) (by decide)).cells q))
  change (Polyline.L.outEmbed 99970 98999 (by decide) (by decide)).cells q∈((Polyline.L.atlas 99970 98999 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).board).walls↔_
  rw [Polyline.L.board_eq,Polyline.L.out_walls_agree]
  change q∈Chain.walls 98999 (by decide)↔_
  rw [Polyline.chain_right7 98999 (by decide) q (by dsimp only [q]; have:=p.1.isLt; omega)]

private theorem eastSouth_west_walls (a b : Bool) (p : PushFS.Cell 5 21) :
    faceCell .west p∈(puzzle .eastSouth a b).board.walls ↔p.2.val=11 ∨p.2.val=12 := by
  let q : Chain.C 99970 := (⟨p.1.val,by have:=p.1.isLt; omega⟩,⟨p.2.val,by have:=p.2.isLt; omega⟩)
  have he : faceCell .west p=(padding .eastSouth a b).cells ((GridIsometry.reflectX 100013 99043).cells ((Out.inEmbed 99970 98979 (by decide) (by decide)).cells q)) := by
    have hx0 : ((Out.inEmbed 99970 98979 (by decide) (by decide)).cells q).1.val=38+(99974-q.1.val) := by exact Out.in_x 99970 98979 (by decide) (by decide) q
    have hy0 : ((Out.inEmbed 99970 98979 (by decide) (by decide)).cells q).2.val=q.2.val := by exact Out.in_y 99970 98979 (by decide) (by decide) q
    dsimp only [q] at hx0 hy0
    apply Prod.ext <;> apply Fin.ext
    · change p.1.val=0+(100013-(((Out.inEmbed 99970 98979 (by decide) (by decide)).cells q).1.val+1))
      dsimp only [q]; omega
    · change 99023+p.2.val=99023+(((Out.inEmbed 99970 98979 (by decide) (by decide)).cells q).2.val)
      dsimp only [q]; omega
  rw [he]
  apply Iff.trans (padding_walls .eastSouth a b ((GridIsometry.reflectX 100013 99043).cells ((Out.inEmbed 99970 98979 (by decide) (by decide)).cells q)))
  change (GridIsometry.reflectX 100013 99043).cells ((Out.inEmbed 99970 98979 (by decide) (by decide)).cells q)∈((GridIsometry.reflectX 100013 99043).board ((Out.atlas 99970 98979 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).board)).walls↔_
  repeat rw [GridIsometry.mem_walls]
  rw [Out.board_eq,Out.in_walls_agree]
  change q∈Chain.walls 99970 (by decide)↔_
  rw [Polyline.chain_left5 99970 (by decide) q (by dsimp only [q]; have:=p.1.isLt; omega)]

private theorem eastSouth_south_walls (a b : Bool) (p : PushFS.Cell 5 21) :
    faceCell .south p∈(puzzle .eastSouth a b).board.walls ↔p.2.val=11 ∨p.2.val=12 := by
  let q : FlippedChain.C 98979 := (⟨98999+p.1.val,by have:=p.1.isLt; omega⟩,⟨20-p.2.val,by have:=p.2.isLt; omega⟩)
  have he : faceCell .south p=(padding .eastSouth a b).cells ((GridIsometry.reflectX 100013 99043).cells ((Out.outEmbed 99970 98979 (by decide) (by decide)).cells q)) := by
    have hx0 : ((Out.outEmbed 99970 98979 (by decide) (by decide)).cells q).1.val=20-q.2.val := by exact Out.out_x 99970 98979 (by decide) (by decide) q
    have hy0 : ((Out.outEmbed 99970 98979 (by decide) (by decide)).cells q).2.val=39+q.1.val := by exact Out.out_y 99970 98979 (by decide) (by decide) q
    dsimp only [q] at hx0 hy0
    apply Prod.ext <;> apply Fin.ext
    · change 99992+(20-p.2.val)=0+(100013-(((Out.outEmbed 99970 98979 (by decide) (by decide)).cells q).1.val+1))
      dsimp only [q]; omega
    · change 198061+p.1.val=99023+(((Out.outEmbed 99970 98979 (by decide) (by decide)).cells q).2.val)
      dsimp only [q]; omega
  rw [he]
  apply Iff.trans (padding_walls .eastSouth a b ((GridIsometry.reflectX 100013 99043).cells ((Out.outEmbed 99970 98979 (by decide) (by decide)).cells q)))
  change (GridIsometry.reflectX 100013 99043).cells ((Out.outEmbed 99970 98979 (by decide) (by decide)).cells q)∈((GridIsometry.reflectX 100013 99043).board ((Out.atlas 99970 98979 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).board)).walls↔_
  repeat rw [GridIsometry.mem_walls]
  rw [Out.board_eq,Out.out_walls_agree]
  change q∈FlippedChain.walls 98979 (by decide)↔_
  rw [FlippedChain.right_collar 98979 (by decide) q (by dsimp only [q]; have:=p.1.isLt; omega)]
  dsimp only [q]
  have:=p.2.isLt
  omega

private theorem southEast_north_walls (a b : Bool) (p : PushFS.Cell 5 21) :
    faceCell .north p∈(puzzle .southEast a b).board.walls ↔p.2.val=11 ∨p.2.val=12 := by
  let q : FlippedChain.C 98981 := (⟨p.1.val,by have:=p.1.isLt; omega⟩,⟨p.2.val,by have:=p.2.isLt; omega⟩)
  have he : faceCell .north p=(padding .southEast a b).cells ((GridIsometry.transpose 99044 100013).cells ((GridIsometry.reflectX 99044 100013).cells ((In.inEmbed 98981 99969 (by decide) (by decide)).cells q))) := by
    have hx0 : ((In.inEmbed 98981 99969 (by decide) (by decide)).cells q).1.val=38+(99005-q.1.val) := by exact In.in_x 98981 99969 (by decide) (by decide) q
    have hy0 : ((In.inEmbed 98981 99969 (by decide) (by decide)).cells q).2.val=20-q.2.val := by exact In.in_y 98981 99969 (by decide) (by decide) q
    dsimp only [q] at hx0 hy0
    apply Prod.ext <;> apply Fin.ext
    · change 99992+(20-p.2.val)=99992+(((In.inEmbed 98981 99969 (by decide) (by decide)).cells q).2.val)
      dsimp only [q]; omega
    · change p.1.val=0+(99044-(((In.inEmbed 98981 99969 (by decide) (by decide)).cells q).1.val+1))
      dsimp only [q]; omega
  rw [he]
  apply Iff.trans (padding_walls .southEast a b ((GridIsometry.transpose 99044 100013).cells ((GridIsometry.reflectX 99044 100013).cells ((In.inEmbed 98981 99969 (by decide) (by decide)).cells q))))
  change (GridIsometry.transpose 99044 100013).cells ((GridIsometry.reflectX 99044 100013).cells ((In.inEmbed 98981 99969 (by decide) (by decide)).cells q))∈((GridIsometry.transpose 99044 100013).board ((GridIsometry.reflectX 99044 100013).board ((In.atlas 98981 99969 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).board))).walls↔_
  repeat rw [GridIsometry.mem_walls]
  rw [In.board_eq,In.in_walls_agree]
  change q∈FlippedChain.walls 98981 (by decide)↔_
  rw [FlippedChain.left_collar 98981 (by decide) q (by dsimp only [q]; have:=p.1.isLt; omega)]

private theorem southEast_east_walls (a b : Bool) (p : PushFS.Cell 5 21) :
    faceCell .east p∈(puzzle .southEast a b).board.walls ↔p.2.val=11 ∨p.2.val=12 := by
  let q : Chain.C 99969 := (⟨99969+p.1.val,by have:=p.1.isLt; omega⟩,⟨p.2.val,by have:=p.2.isLt; omega⟩)
  have he : faceCell .east p=(padding .southEast a b).cells ((GridIsometry.transpose 99044 100013).cells ((GridIsometry.reflectX 99044 100013).cells ((In.outEmbed 98981 99969 (by decide) (by decide)).cells q))) := by
    have hx0 : ((In.outEmbed 98981 99969 (by decide) (by decide)).cells q).1.val=20-q.2.val := by exact In.out_x 98981 99969 (by decide) (by decide) q
    have hy0 : ((In.outEmbed 98981 99969 (by decide) (by decide)).cells q).2.val=39+q.1.val := by exact In.out_y 98981 99969 (by decide) (by decide) q
    dsimp only [q] at hx0 hy0
    apply Prod.ext <;> apply Fin.ext
    · change 200000+p.1.val=99992+(((In.outEmbed 98981 99969 (by decide) (by decide)).cells q).2.val)
      dsimp only [q]; omega
    · change 99023+p.2.val=0+(99044-(((In.outEmbed 98981 99969 (by decide) (by decide)).cells q).1.val+1))
      dsimp only [q]; omega
  rw [he]
  apply Iff.trans (padding_walls .southEast a b ((GridIsometry.transpose 99044 100013).cells ((GridIsometry.reflectX 99044 100013).cells ((In.outEmbed 98981 99969 (by decide) (by decide)).cells q))))
  change (GridIsometry.transpose 99044 100013).cells ((GridIsometry.reflectX 99044 100013).cells ((In.outEmbed 98981 99969 (by decide) (by decide)).cells q))∈((GridIsometry.transpose 99044 100013).board ((GridIsometry.reflectX 99044 100013).board ((In.atlas 98981 99969 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).board))).walls↔_
  repeat rw [GridIsometry.mem_walls]
  rw [In.board_eq,In.out_walls_agree]
  change q∈Chain.walls 99969 (by decide)↔_
  rw [Polyline.chain_right7 99969 (by decide) q (by dsimp only [q]; have:=p.1.isLt; omega)]

private theorem southWest_north_walls (a b : Bool) (p : PushFS.Cell 5 21) :
    faceCell .north p∈(puzzle .southWest a b).board.walls ↔p.2.val=11 ∨p.2.val=12 := by
  let q : Chain.C 99001 := (⟨p.1.val,by have:=p.1.isLt; omega⟩,⟨p.2.val,by have:=p.2.isLt; omega⟩)
  have he : faceCell .north p=(padding .southWest a b).cells ((GridIsometry.reflectX 100013 99044).cells ((GridIsometry.transpose 99044 100013).cells ((GridIsometry.reflectX 99044 100013).cells ((Polyline.L.inEmbed 99001 99969 (by decide) (by decide)).cells q)))) := by
    have hx0 : ((Polyline.L.inEmbed 99001 99969 (by decide) (by decide)).cells q).1.val=38+(99005-q.1.val) := by exact Polyline.L.in_x 99001 99969 (by decide) (by decide) q
    have hy0 : ((Polyline.L.inEmbed 99001 99969 (by decide) (by decide)).cells q).2.val=q.2.val := by exact Polyline.L.in_y 99001 99969 (by decide) (by decide) q
    dsimp only [q] at hx0 hy0
    apply Prod.ext <;> apply Fin.ext
    · change 99992+(20-p.2.val)=0+(100013-(((Polyline.L.inEmbed 99001 99969 (by decide) (by decide)).cells q).2.val+1))
      dsimp only [q]; omega
    · change p.1.val=0+(99044-(((Polyline.L.inEmbed 99001 99969 (by decide) (by decide)).cells q).1.val+1))
      dsimp only [q]; omega
  rw [he]
  apply Iff.trans (padding_walls .southWest a b ((GridIsometry.reflectX 100013 99044).cells ((GridIsometry.transpose 99044 100013).cells ((GridIsometry.reflectX 99044 100013).cells ((Polyline.L.inEmbed 99001 99969 (by decide) (by decide)).cells q)))))
  change (GridIsometry.reflectX 100013 99044).cells ((GridIsometry.transpose 99044 100013).cells ((GridIsometry.reflectX 99044 100013).cells ((Polyline.L.inEmbed 99001 99969 (by decide) (by decide)).cells q)))∈((GridIsometry.reflectX 100013 99044).board ((GridIsometry.transpose 99044 100013).board ((GridIsometry.reflectX 99044 100013).board ((Polyline.L.atlas 99001 99969 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).board)))).walls↔_
  repeat rw [GridIsometry.mem_walls]
  rw [Polyline.L.board_eq,Polyline.L.in_walls_agree]
  change q∈Chain.walls 99001 (by decide)↔_
  rw [Polyline.chain_left5 99001 (by decide) q (by dsimp only [q]; have:=p.1.isLt; omega)]

private theorem southWest_west_walls (a b : Bool) (p : PushFS.Cell 5 21) :
    faceCell .west p∈(puzzle .southWest a b).board.walls ↔p.2.val=11 ∨p.2.val=12 := by
  let q : Chain.C 99969 := (⟨99973-p.1.val,by have:=p.1.isLt; omega⟩,⟨p.2.val,by have:=p.2.isLt; omega⟩)
  have he : faceCell .west p=(padding .southWest a b).cells ((GridIsometry.reflectX 100013 99044).cells ((GridIsometry.transpose 99044 100013).cells ((GridIsometry.reflectX 99044 100013).cells ((Polyline.L.outEmbed 99001 99969 (by decide) (by decide)).cells q)))) := by
    have hx0 : ((Polyline.L.outEmbed 99001 99969 (by decide) (by decide)).cells q).1.val=20-q.2.val := by exact Polyline.L.out_x 99001 99969 (by decide) (by decide) q
    have hy0 : ((Polyline.L.outEmbed 99001 99969 (by decide) (by decide)).cells q).2.val=39+q.1.val := by exact Polyline.L.out_y 99001 99969 (by decide) (by decide) q
    dsimp only [q] at hx0 hy0
    apply Prod.ext <;> apply Fin.ext
    · change p.1.val=0+(100013-(((Polyline.L.outEmbed 99001 99969 (by decide) (by decide)).cells q).2.val+1))
      dsimp only [q]; omega
    · change 99023+p.2.val=0+(99044-(((Polyline.L.outEmbed 99001 99969 (by decide) (by decide)).cells q).1.val+1))
      dsimp only [q]; omega
  rw [he]
  apply Iff.trans (padding_walls .southWest a b ((GridIsometry.reflectX 100013 99044).cells ((GridIsometry.transpose 99044 100013).cells ((GridIsometry.reflectX 99044 100013).cells ((Polyline.L.outEmbed 99001 99969 (by decide) (by decide)).cells q)))))
  change (GridIsometry.reflectX 100013 99044).cells ((GridIsometry.transpose 99044 100013).cells ((GridIsometry.reflectX 99044 100013).cells ((Polyline.L.outEmbed 99001 99969 (by decide) (by decide)).cells q)))∈((GridIsometry.reflectX 100013 99044).board ((GridIsometry.transpose 99044 100013).board ((GridIsometry.reflectX 99044 100013).board ((Polyline.L.atlas 99001 99969 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).board)))).walls↔_
  repeat rw [GridIsometry.mem_walls]
  rw [Polyline.L.board_eq,Polyline.L.out_walls_agree]
  change q∈Chain.walls 99969 (by decide)↔_
  rw [Polyline.chain_right7 99969 (by decide) q (by dsimp only [q]; have:=p.1.isLt; omega)]

/-- Every actual used source face has the common complete south/west wall stencil. -/
theorem source_walls (k : Kind) (a b : Bool) (p : PushFS.Cell 5 21) :
    faceCell (sourceFace k) p∈(puzzle k a b).board.walls ↔p.2.val=11 ∨p.2.val=12 := by
  cases k
  · exact east_west_walls a b p
  · exact west_east_walls a b p
  · exact south_north_walls a b p
  · exact westSouth_east_walls a b p
  · exact eastSouth_west_walls a b p
  · exact southEast_north_walls a b p
  · exact southWest_north_walls a b p

/-- Every actual used target face has the identical complete five-column seam stencil. -/
theorem target_walls (k : Kind) (a b : Bool) (p : PushFS.Cell 5 21) :
    faceCell (targetFace k) p∈(puzzle k a b).board.walls ↔p.2.val=11 ∨p.2.val=12 := by
  cases k
  · exact east_east_walls a b p
  · exact west_west_walls a b p
  · exact south_south_walls a b p
  · exact westSouth_south_walls a b p
  · exact eastSouth_south_walls a b p
  · exact southEast_east_walls a b p
  · exact southWest_west_walls a b p

end PushPuzzle.PushFS.Gadgets.Wires.Catalog
