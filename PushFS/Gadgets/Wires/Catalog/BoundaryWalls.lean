/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.WallBounds

/-! Exact full four-face five-cell outer wall frames of every ordinary logic cell. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog

set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

/-- A full five-column or five-row face, with no transverse strip restriction. -/
def InFace : Face→Cell→Prop
  | .west,p=>p.1.val<5
  | .east,p=>200000≤p.1.val
  | .north,p=>p.2.val<5
  | .south,p=>198061≤p.2.val

def FaceUsed (k : Kind) (f : Face) : Prop := f=sourceFace k ∨f=targetFace k

def FaceBand : Face→Cell→Prop
  | .west | .east=>HorizontalBand
  | .north | .south=>VerticalBand

/-- The exact two true south/west protective rows or columns. -/
def FaceGuard : Face→Cell→Prop
  | .west,p | .east,p=>p.2.val=99034 ∨p.2.val=99035
  | .north,p | .south,p=>p.1.val=100000 ∨p.1.val=100001

instance (f : Face) (p : Cell) : Decidable (InFace f p) := by
  cases f <;> dsimp [InFace] <;> infer_instance

instance (k : Kind) (f : Face) : Decidable (FaceUsed k f) := by
  unfold FaceUsed
  infer_instance

instance (f : Face) (p : Cell) : Decidable (FaceBand f p) := by
  cases f <;> dsimp [FaceBand,HorizontalBand,VerticalBand] <;> infer_instance

instance (f : Face) (p : Cell) : Decidable (FaceGuard f p) := by
  cases f <;> dsimp [FaceGuard] <;> infer_instance

/-- Actual wall supports meet an outer face only at a genuine used physical port. -/
private theorem region_face (k : Kind) (f : Face) (p : Cell) (hp : WallRegion k p)
    (hf : InFace f p) :
    FaceUsed k f ∧FaceBand f p := by
  cases k <;> cases f <;>
    simp_all [WallRegion,InFace,FaceUsed,FaceBand,sourceFace,targetFace,HorizontalBand,VerticalBand] <;> omega

theorem guard_band (f : Face) (p : Cell) (hp : FaceGuard f p) : FaceBand f p := by
  cases f <;> dsimp [FaceGuard,FaceBand,HorizontalBand,VerticalBand] at * <;> omega

/-- Every actual outer-frame wall has a cell in the previously checked complete endpoint chart. -/
private theorem faceCell_preimage (f : Face) (p : Cell) (hf : InFace f p) (hb : FaceBand f p) :
    ∃q : PushFS.Cell 5 21, faceCell f q=p := by
  have hx : p.1.val<200005 := p.1.isLt
  have hy : p.2.val<198066 := p.2.isLt
  cases f
  · change p.1.val<5 at hf
    change 99031≤p.2.val ∧p.2.val≤99035 at hb
    refine ⟨(⟨p.1.val,hf⟩,⟨p.2.val-99023,by omega⟩),?_⟩
    apply Prod.ext <;> apply Fin.ext
    · rfl
    · change 99023+(p.2.val-99023)=p.2.val; omega
  · change 200000≤p.1.val at hf
    change 99031≤p.2.val ∧p.2.val≤99035 at hb
    refine ⟨(⟨p.1.val-200000,by omega⟩,⟨p.2.val-99023,by omega⟩),?_⟩
    apply Prod.ext <;> apply Fin.ext
    · change 200000+(p.1.val-200000)=p.1.val; omega
    · change 99023+(p.2.val-99023)=p.2.val; omega
  · change p.2.val<5 at hf
    change 100000≤p.1.val ∧p.1.val≤100004 at hb
    refine ⟨(⟨p.2.val,hf⟩,⟨100012-p.1.val,by omega⟩),?_⟩
    apply Prod.ext <;> apply Fin.ext
    · change 99992+(20-(100012-p.1.val))=p.1.val; omega
    · rfl
  · change 198061≤p.2.val at hf
    change 100000≤p.1.val ∧p.1.val≤100004 at hb
    refine ⟨(⟨p.2.val-198061,by omega⟩,⟨100012-p.1.val,by omega⟩),?_⟩
    apply Prod.ext <;> apply Fin.ext
    · change 99992+(20-(100012-p.1.val))=p.1.val; omega
    · change 198061+(p.2.val-198061)=p.2.val; omega

private theorem faceCell_guard (f : Face) (p : PushFS.Cell 5 21) :
    FaceGuard f (faceCell f p) ↔p.2.val=11 ∨p.2.val=12 := by
  have hy:=p.2.isLt
  cases f <;> dsimp [FaceGuard,faceCell] <;> omega

theorem used_face_walls (k : Kind) (a b : Bool) (f : Face) (hu : FaceUsed k f) (p : PushFS.Cell 5 21) :
    faceCell f p∈(puzzle k a b).board.walls ↔p.2.val=11 ∨p.2.val=12 := by
  rcases hu with rfl|rfl
  · exact source_walls k a b p
  · exact target_walls k a b p

/-- On the entire outer face, the true bitmap has exactly the two guard lines of a used port and floor everywhere else. -/
theorem boundary_walls (k : Kind) (a b : Bool) (f : Face) (p : Cell) (hf : InFace f p) :
    p∈(puzzle k a b).board.walls ↔FaceUsed k f ∧FaceGuard f p := by
  constructor
  · intro hw
    have hc:=region_face k f p (wall_bounds k a b hw) hf
    obtain ⟨q,rfl⟩:=faceCell_preimage f p hf hc.2
    exact ⟨hc.1,(faceCell_guard f q).mpr ((used_face_walls k a b f hc.1 q).mp hw)⟩
  · rintro ⟨hu,hg⟩
    obtain ⟨q,rfl⟩:=faceCell_preimage f p hf (guard_band f p hg)
    exact (used_face_walls k a b f hu q).mpr ((faceCell_guard f q).mp hg)

end PushPuzzle.PushFS.Gadgets.Wires.Catalog
