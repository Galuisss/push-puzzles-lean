/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGeometry
public import PushFS.Isometry

/-! Full square covers transported through the actual primitive placements. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteFreeze

open PushFS

/-- Filled squares contained in the source rectangle, so placement retains every square cell. -/
def BoundedSquares {W H : ℕ} (side : ℕ) (walls : Finset (Cell W H)) : Prop :=
  ∀ p ∈ walls, ∃ x y : ℕ,
    x+side ≤ W ∧ y+side ≤ H ∧
    x ≤ p.1.val ∧ p.1.val < x+side ∧ y ≤ p.2.val ∧ p.2.val < y+side ∧
    ∀ q : Cell W H, x ≤ q.1.val → q.1.val < x+side →
      y ≤ q.2.val → q.2.val < y+side → q ∈ walls

namespace BoundedSquares

variable {w h W H side : ℕ} {walls : Finset (Cell w h)}

private theorem squareCovered (hs : BoundedSquares side walls) : SquareCovered side walls := by
  intro p hp
  obtain ⟨x,y,_,_,hx,hx',hy,hy',hf⟩ := hs p hp
  exact ⟨x,y,hx,hx',hy,hy',hf⟩

theorem thick {k : ℕ} (hs : BoundedSquares side walls) (hk : k < side) : Thick k walls :=
  thick_of_squareCovered hk hs.squareCovered

theorem biUnion {ι : Type} [DecidableEq ι] (indices : Finset ι)
    (pieces : ι → Finset (Cell w h)) (hs : ∀ i ∈ indices, BoundedSquares side (pieces i)) :
    BoundedSquares side (indices.biUnion pieces) := by
  intro p hp
  obtain ⟨i,hi,hp⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨x,y,hx,hy,hpx,hpx',hpy,hpy',hf⟩ := hs i hi p hp
  refine ⟨x,y,hx,hy,hpx,hpx',hpy,hpy',?_⟩
  intro q hqx hqx' hqy hqy'
  exact Finset.mem_biUnion.mpr ⟨i,hi,hf q hqx hqx' hqy hqy'⟩

theorem translate (hs : BoundedSquares side walls) (dx dy : ℕ)
    (hx : dx+w ≤ W) (hy : dy+h ≤ H) :
    BoundedSquares side (walls.map (GridEmbedding.translate dx dy hx hy).cells) := by
  intro p hp
  obtain ⟨p',hp',rfl⟩ := Finset.mem_map.mp hp
  obtain ⟨x,y,hx',hy',hpx,hpx',hpy,hpy',hf⟩ := hs p' hp'
  refine ⟨dx+x,dy+y,by omega,by omega,?_,?_,?_,?_,?_⟩
  · change dx+x ≤ dx+p'.1.val; omega
  · change dx+p'.1.val < dx+x+side; omega
  · change dy+y ≤ dy+p'.2.val; omega
  · change dy+p'.2.val < dy+y+side; omega
  · intro q hqx hqx' hqy hqy'
    let r : Cell w h := (⟨q.1.val-dx,by omega⟩,⟨q.2.val-dy,by omega⟩)
    have hr := hf r (by dsimp [r]; omega) (by dsimp [r]; omega)
      (by dsimp [r]; omega) (by dsimp [r]; omega)
    refine Finset.mem_map.mpr ⟨r,hr,?_⟩
    apply Prod.ext <;> apply Fin.ext <;> dsimp [r,GridEmbedding.translate] <;> omega

private theorem transpose (hs : BoundedSquares side walls) :
    BoundedSquares side (walls.map (GridIsometry.transpose w h).cells.toEmbedding) := by
  intro p hp
  obtain ⟨p',hp',rfl⟩ := Finset.mem_map.mp hp
  obtain ⟨x,y,hx,hy,hpx,hpx',hpy,hpy',hf⟩ := hs p' hp'
  refine ⟨y,x,hy,hx,hpy,hpy',hpx,hpx',?_⟩
  intro q hqx hqx' hqy hqy'
  exact Finset.mem_map.mpr ⟨(q.2,q.1),hf (q.2,q.1) hqy hqy' hqx hqx',rfl⟩

theorem reflectX (hs : BoundedSquares side walls) :
    BoundedSquares side (walls.map (GridIsometry.reflectX w h).cells.toEmbedding) := by
  intro p hp
  obtain ⟨p',hp',rfl⟩ := Finset.mem_map.mp hp
  obtain ⟨x,y,hx,hy,hpx,hpx',hpy,hpy',hf⟩ := hs p' hp'
  have hpl := p'.1.isLt
  refine ⟨w-(x+side),y,by omega,hy,?_,?_,hpy,hpy',?_⟩
  · change w-(x+side) ≤ w-(p'.1.val+1); omega
  · change w-(p'.1.val+1) < w-(x+side)+side; omega
  · intro q hqx hqx' hqy hqy'
    let r : Cell w h := (Fin.rev q.1,q.2)
    have hql := q.1.isLt
    have hr := hf r (by dsimp [r,Fin.rev]; omega) (by dsimp [r,Fin.rev]; omega) hqy hqy'
    refine Finset.mem_map.mpr ⟨r,hr,?_⟩
    apply Prod.ext <;> apply Fin.ext
    · change w-(w-(q.1.val+1)+1) = q.1.val; omega
    · rfl

theorem reflectY (hs : BoundedSquares side walls) :
    BoundedSquares side (walls.map (GridIsometry.reflectY w h).cells.toEmbedding) := by
  simpa only [GridIsometry.reflectY,GridIsometry.trans,Equiv.trans_toEmbedding,Finset.map_map]
    using hs.transpose.reflectX.transpose

theorem clockwise (hs : BoundedSquares side walls) :
    BoundedSquares side (walls.map (GridIsometry.clockwise w h).cells.toEmbedding) := by
  simpa only [GridIsometry.clockwise,GridIsometry.trans,Equiv.trans_toEmbedding,Finset.map_map]
    using hs.transpose.reflectX

theorem counterclockwise (hs : BoundedSquares side walls) :
    BoundedSquares side (walls.map (GridIsometry.clockwise h w).symm.cells.toEmbedding) := by
  have he : (GridIsometry.clockwise h w).symm.cells.toEmbedding =
      (GridIsometry.reflectX w h).cells.toEmbedding.trans
        (GridIsometry.transpose w h).cells.toEmbedding := by
    ext p <;> rfl
  rw [he, ← Finset.map_map]
  exact hs.reflectX.transpose

end BoundedSquares
end PushPuzzle.PushS.FiniteFreeze

namespace PushPuzzle.PushS.FiniteGeometry

open PushFS

/-- Actual in-board thick rectangles retain complete square blocks under placement. -/
theorem Rectangle.boundedSquares (r : Rectangle) (W H side : ℕ)
    (hs : 0 < side) (hx : side ≤ r.width) (hy : side ≤ r.height)
    (hW : r.x+r.width ≤ W) (hH : r.y+r.height ≤ H) :
    FiniteFreeze.BoundedSquares side (r.cells W H) := by
  intro p hp
  obtain ⟨hpx,hpx',hpy,hpy'⟩ := (r.mem_cells W H p).mp hp
  let x := min p.1.val (r.x+r.width-side)
  let y := min p.2.val (r.y+r.height-side)
  refine ⟨x,y,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals dsimp [x,y]
  all_goals try omega
  intro q hqx hqx' hqy hqy'
  apply (r.mem_cells W H q).mpr
  omega

end PushPuzzle.PushS.FiniteGeometry
