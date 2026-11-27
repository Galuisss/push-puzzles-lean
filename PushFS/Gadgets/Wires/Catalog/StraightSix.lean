/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.BoundaryWalls

/-! Complete six-cell exterior wall frames of the three true straight ordinary cells. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog

set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

private theorem tile_left6 : ∀(kind : Bool) (p : Chain.Tile.C kind),p.1.val<6→
    (p∈Chain.Tile.walls kind ↔p.2.val=11 ∨p.2.val=12) := by decide +kernel

private theorem chain_left6 (n : ℕ) (hn : 2301≤n) (p : Chain.C n) (hx : p.1.val<6) :
    p∈Chain.walls n hn ↔p.2.val=11 ∨p.2.val=12 := by
  let i:=Chain.firstBlock n hn
  have hw : 6≤Chain.Tile.width (Chain.kind n i) := by cases Chain.kind n i <;> decide
  let q : Chain.Tile.C (Chain.kind n i) := (⟨p.1.val,by omega⟩,p.2)
  have he : Chain.embed n hn i q=p := by
    apply Prod.ext <;> apply Fin.ext
    · rw [Chain.embed_x,Chain.first_offset]
      simp only [Nat.zero_add,q]
    · exact Chain.embed_y n hn i q
  rw [←he,Chain.walls_exact,Chain.embed_y]
  exact tile_left6 _ q hx

def faceCell6 (f : Face) (p : PushFS.Cell 6 21) : Cell :=
  match f with
  | .west => (⟨p.1.val,by change _<200005; have:=p.1.isLt; omega⟩,⟨99023+p.2.val,by change _<198066; have:=p.2.isLt; omega⟩)
  | .east => (⟨199999+p.1.val,by change _<200005; have:=p.1.isLt; omega⟩,⟨99023+p.2.val,by change _<198066; have:=p.2.isLt; omega⟩)
  | .north => (⟨99992+(20-p.2.val),by change _<200005; have:=p.2.isLt; omega⟩,⟨p.1.val,by change _<198066; have:=p.1.isLt; omega⟩)
  | .south => (⟨99992+(20-p.2.val),by change _<200005; have:=p.2.isLt; omega⟩,⟨198060+p.1.val,by change _<198066; have:=p.1.isLt; omega⟩)

private theorem east_west_walls6 (a b : Bool) (p : PushFS.Cell 6 21) :
    faceCell6 .west p∈(puzzle .east a b).board.walls ↔p.2.val=11 ∨p.2.val=12 := by
  let q : Chain.C 200000 := (⟨p.1.val,by have:=p.1.isLt; omega⟩,⟨p.2.val,by have:=p.2.isLt; omega⟩)
  have he : faceCell6 .west p=(padding .east a b).cells (q) := by
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
  rw [chain_left6 200000 (by decide) q (by dsimp only [q]; have:=p.1.isLt; omega)]

private theorem east_east_walls6 (a b : Bool) (p : PushFS.Cell 6 21) :
    faceCell6 .east p∈(puzzle .east a b).board.walls ↔p.2.val=11 ∨p.2.val=12 := by
  let q : Chain.C 200000 := (⟨199999+p.1.val,by have:=p.1.isLt; omega⟩,⟨p.2.val,by have:=p.2.isLt; omega⟩)
  have he : faceCell6 .east p=(padding .east a b).cells (q) := by
    have hx0 : (q).1.val=q.1.val := by rfl
    have hy0 : (q).2.val=q.2.val := by rfl
    dsimp only [q] at hx0 hy0
    apply Prod.ext <;> apply Fin.ext
    · change 199999+p.1.val=0+(q.1.val)
      dsimp only [q]; omega
    · rfl
  rw [he]
  apply Iff.trans (padding_walls .east a b (q))
  change q∈((Chain.board 200000 (by decide) (Chain.boxes 200000 (by decide) (Chain.uniform 200000 b)))).walls↔_
  change q∈Chain.walls 200000 (by decide)↔_
  rw [Polyline.chain_right7 200000 (by decide) q (by dsimp only [q]; have:=p.1.isLt; omega)]

private theorem west_west_walls6 (a b : Bool) (p : PushFS.Cell 6 21) :
    faceCell6 .west p∈(puzzle .west a b).board.walls ↔p.2.val=11 ∨p.2.val=12 := by
  let q : Chain.C 200000 := (⟨200004-p.1.val,by have:=p.1.isLt; omega⟩,⟨p.2.val,by have:=p.2.isLt; omega⟩)
  have he : faceCell6 .west p=(padding .west a b).cells ((GridIsometry.reflectX 200005 21).cells (q)) := by
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

private theorem west_east_walls6 (a b : Bool) (p : PushFS.Cell 6 21) :
    faceCell6 .east p∈(puzzle .west a b).board.walls ↔p.2.val=11 ∨p.2.val=12 := by
  let q : Chain.C 200000 := (⟨5-p.1.val,by have:=p.1.isLt; omega⟩,⟨p.2.val,by have:=p.2.isLt; omega⟩)
  have he : faceCell6 .east p=(padding .west a b).cells ((GridIsometry.reflectX 200005 21).cells (q)) := by
    have hx0 : (q).1.val=q.1.val := by rfl
    have hy0 : (q).2.val=q.2.val := by rfl
    dsimp only [q] at hx0 hy0
    apply Prod.ext <;> apply Fin.ext
    · change 199999+p.1.val=0+(200005-(q.1.val+1))
      dsimp only [q]; omega
    · rfl
  rw [he]
  apply Iff.trans (padding_walls .west a b ((GridIsometry.reflectX 200005 21).cells (q)))
  change (GridIsometry.reflectX 200005 21).cells (q)∈((GridIsometry.reflectX 200005 21).board ((Chain.board 200000 (by decide) (Chain.boxes 200000 (by decide) (Chain.uniform 200000 b))))).walls↔_
  repeat rw [GridIsometry.mem_walls]
  change q∈Chain.walls 200000 (by decide)↔_
  rw [chain_left6 200000 (by decide) q (by dsimp only [q]; have:=p.1.isLt; omega)]

private theorem south_north_walls6 (a b : Bool) (p : PushFS.Cell 6 21) :
    faceCell6 .north p∈(puzzle .south a b).board.walls ↔p.2.val=11 ∨p.2.val=12 := by
  let q : Chain.C 198061 := (⟨p.1.val,by have:=p.1.isLt; omega⟩,⟨p.2.val,by have:=p.2.isLt; omega⟩)
  have he : faceCell6 .north p=(padding .south a b).cells ((GridIsometry.reflectX 21 198066).cells ((GridIsometry.transpose 198066 21).cells (q))) := by
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
  rw [chain_left6 198061 (by decide) q (by dsimp only [q]; have:=p.1.isLt; omega)]

private theorem south_south_walls6 (a b : Bool) (p : PushFS.Cell 6 21) :
    faceCell6 .south p∈(puzzle .south a b).board.walls ↔p.2.val=11 ∨p.2.val=12 := by
  let q : Chain.C 198061 := (⟨198060+p.1.val,by have:=p.1.isLt; omega⟩,⟨p.2.val,by have:=p.2.isLt; omega⟩)
  have he : faceCell6 .south p=(padding .south a b).cells ((GridIsometry.reflectX 21 198066).cells ((GridIsometry.transpose 198066 21).cells (q))) := by
    have hx0 : (q).1.val=q.1.val := by rfl
    have hy0 : (q).2.val=q.2.val := by rfl
    dsimp only [q] at hx0 hy0
    apply Prod.ext <;> apply Fin.ext
    · change 99992+(20-p.2.val)=99992+(21-(q.2.val+1))
      dsimp only [q]; omega
    · change 198060+p.1.val=0+(q.1.val)
      dsimp only [q]; omega
  rw [he]
  apply Iff.trans (padding_walls .south a b ((GridIsometry.reflectX 21 198066).cells ((GridIsometry.transpose 198066 21).cells (q))))
  change (GridIsometry.reflectX 21 198066).cells ((GridIsometry.transpose 198066 21).cells (q))∈((GridIsometry.reflectX 21 198066).board ((GridIsometry.transpose 198066 21).board ((Chain.board 198061 (by decide) (Chain.boxes 198061 (by decide) (Chain.uniform 198061 b)))))).walls↔_
  repeat rw [GridIsometry.mem_walls]
  change q∈Chain.walls 198061 (by decide)↔_
  rw [Polyline.chain_right7 198061 (by decide) q (by dsimp only [q]; have:=p.1.isLt; omega)]


def Straight (k : Kind) : Prop := k=.east ∨k=.west ∨k=.south

instance (k : Kind) : Decidable (Straight k) := by unfold Straight; infer_instance

def InFace6 : Face→Cell→Prop
  | .west,p => p.1.val<6
  | .east,p => 199999≤p.1.val
  | .north,p => p.2.val<6
  | .south,p => 198060≤p.2.val

instance (f : Face) (p : Cell) : Decidable (InFace6 f p) := by cases f <;> unfold InFace6 <;> infer_instance

private theorem region_face6 (k : Kind) (hk : Straight k) (f : Face) (p : Cell)
    (hp : WallRegion k p) (hf : InFace6 f p) : FaceUsed k f ∧FaceBand f p := by
  rcases hk with rfl|rfl|rfl
  all_goals cases f <;>
    simp_all [WallRegion,InFace6,FaceUsed,FaceBand,sourceFace,targetFace,HorizontalBand,VerticalBand] <;> omega

private theorem faceCell6_preimage (f : Face) (p : Cell) (hf : InFace6 f p) (hb : FaceBand f p) :
    ∃q : PushFS.Cell 6 21, faceCell6 f q=p := by
  have hx : p.1.val<200005 := p.1.isLt
  have hy : p.2.val<198066 := p.2.isLt
  cases f
  · change p.1.val<6 at hf
    change 99031≤p.2.val ∧p.2.val≤99035 at hb
    refine ⟨(⟨p.1.val,hf⟩,⟨p.2.val-99023,by omega⟩),?_⟩
    apply Prod.ext <;> apply Fin.ext
    · rfl
    · change 99023+(p.2.val-99023)=p.2.val; omega
  · change 199999≤p.1.val at hf
    change 99031≤p.2.val ∧p.2.val≤99035 at hb
    refine ⟨(⟨p.1.val-199999,by omega⟩,⟨p.2.val-99023,by omega⟩),?_⟩
    apply Prod.ext <;> apply Fin.ext
    · change 199999+(p.1.val-199999)=p.1.val; omega
    · change 99023+(p.2.val-99023)=p.2.val; omega
  · change p.2.val<6 at hf
    change 100000≤p.1.val ∧p.1.val≤100004 at hb
    refine ⟨(⟨p.2.val,hf⟩,⟨100012-p.1.val,by omega⟩),?_⟩
    apply Prod.ext <;> apply Fin.ext
    · change 99992+(20-(100012-p.1.val))=p.1.val; omega
    · rfl
  · change 198060≤p.2.val at hf
    change 100000≤p.1.val ∧p.1.val≤100004 at hb
    refine ⟨(⟨p.2.val-198060,by omega⟩,⟨100012-p.1.val,by omega⟩),?_⟩
    apply Prod.ext <;> apply Fin.ext
    · change 99992+(20-(100012-p.1.val))=p.1.val; omega
    · change 198060+(p.2.val-198060)=p.2.val; omega

private theorem faceCell6_guard (f : Face) (p : PushFS.Cell 6 21) :
    FaceGuard f (faceCell6 f p) ↔p.2.val=11 ∨p.2.val=12 := by
  have hy:=p.2.isLt
  cases f <;> dsimp [FaceGuard,faceCell6] <;> omega

private theorem used_face_walls6 (k : Kind) (hk : Straight k) (a b : Bool) (f : Face)
    (hu : FaceUsed k f) (p : PushFS.Cell 6 21) :
    faceCell6 f p∈(puzzle k a b).board.walls ↔p.2.val=11 ∨p.2.val=12 := by
  rcases hk with rfl|rfl|rfl
  · rcases hu with rfl|rfl
    · exact east_west_walls6 a b p
    · exact east_east_walls6 a b p
  · rcases hu with rfl|rfl
    · exact west_east_walls6 a b p
    · exact west_west_walls6 a b p
  · rcases hu with rfl|rfl
    · exact south_north_walls6 a b p
    · exact south_south_walls6 a b p

/-- The whole six-cell outer frame, including every unused face and all transverse floor. -/
theorem six_walls (k : Kind) (hk : Straight k) (a b : Bool) (f : Face) (p : Cell) (hf : InFace6 f p) :
    p∈(puzzle k a b).board.walls ↔FaceUsed k f ∧FaceGuard f p := by
  constructor
  · intro hw
    have hc:=region_face6 k hk f p (wall_bounds k a b hw) hf
    obtain ⟨q,rfl⟩:=faceCell6_preimage f p hf hc.2
    exact ⟨hc.1,(faceCell6_guard f q).mpr ((used_face_walls6 k hk a b f hc.1 q).mp hw)⟩
  · rintro ⟨hu,hg⟩
    obtain ⟨q,rfl⟩:=faceCell6_preimage f p hf (guard_band f p hg)
    exact (used_face_walls6 k hk a b f hu q).mpr ((faceCell6_guard f q).mp hg)

end PushPuzzle.PushFS.Gadgets.Wires.Catalog
