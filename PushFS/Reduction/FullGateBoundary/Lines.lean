/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateBoundary.EndWalls

/-! The complete true last-line stencil has exactly the common exterior guard. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateBoundary

open Gadgets Gadgets.Wires
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

private theorem normal_piece_wall (d : Direction) (incoming : Bool) (n : ℕ) (hn : 2301≤n)
    (a b : Bool)
    (dx dy : ℕ) (hd : EndPlacement d incoming n dx dy)
    (q : Cell ((lineOrientation d false).width (n+5) 21) ((lineOrientation d false).height (n+5) 21))
    (p : ℕ×ℕ) (he : (dx+q.1.val,dy+q.2.val)=p) (hf : InFrame d p) :
    q∈(((lineOrientation d false).axis (n+5) 21).geometry.board (Chain.puzzle n hn a b).board).walls ↔Guard d p := by
  let e:=((lineOrientation d false).axis (n+5) 21).geometry
  obtain ⟨r,rfl⟩:=e.cells.surjective q
  exact (e.mem_walls (Chain.puzzle n hn a b).board r).trans (normal_far_wall d incoming n hn dx dy hd r p he hf)

theorem last_line_wall (k : Key) (j : Fin (curve k).length) (hj : j.val+1=(curve k).length) (a b : Bool)
    (q : Cell (linePiece k j.val j.isLt a b).width (linePiece k j.val j.isLt a b).height)
    (p : ℕ×ℕ) (he : ((lineOffset k j.val).1+q.1.val,(lineOffset k j.val).2+q.2.val)=p)
    (hf : InFrame (PortAnnulus.outerDirection k.1.2) p) :
    q∈(linePiece k j.val j.isLt a b).board.walls ↔Guard (PortAnnulus.outerDirection k.1.2) p := by
  obtain ⟨hflip,htravel,hd⟩:=last_line_metadata k j hj
  revert q
  unfold linePiece
  rw [hflip,htravel]
  intro q he
  exact normal_piece_wall _ k.2 _ (filler_shape k j.val j.isLt).2.1 a b
    (lineOffset k j.val).1 (lineOffset k j.val).2 hd q p he hf

private theorem normal_piece_covers (d : Direction) (incoming : Bool) (n : ℕ) (hn : 2301≤n)
    (a b : Bool)
    (dx dy : ℕ) (hd : EndPlacement d incoming n dx dy) (p : ℕ×ℕ)
    (hpx : p.1<200007) (hpy : p.2<198068) (hf : InFrame d p) (hg : Guard d p)
    (hc : incoming=true ∨¬CapPoint d p) :
    ∃q : Cell ((lineOrientation d false).width (n+5) 21) ((lineOrientation d false).height (n+5) 21),
      q∈(((lineOrientation d false).axis (n+5) 21).geometry.board (Chain.puzzle n hn a b).board).walls ∧
      (dx+q.1.val,dy+q.2.val)=p := by
  have h:=normal_contains d incoming n hn dx dy hd p hpx hpy hf hg hc
  let q : Cell ((lineOrientation d false).width (n+5) 21) ((lineOrientation d false).height (n+5) 21) :=
    (⟨p.1-dx,by omega⟩,⟨p.2-dy,by omega⟩)
  have he : (dx+q.1.val,dy+q.2.val)=p := by apply Prod.ext <;> dsimp only [q] <;> omega
  exact ⟨q,(normal_piece_wall d incoming n hn a b dx dy hd q p he hf).mpr hg,he⟩

theorem last_line_covers (k : Key) (j : Fin (curve k).length) (hj : j.val+1=(curve k).length) (a b : Bool)
    (p : ℕ×ℕ) (hpx : p.1<200007) (hpy : p.2<198068)
    (hf : InFrame (PortAnnulus.outerDirection k.1.2) p) (hg : Guard (PortAnnulus.outerDirection k.1.2) p)
    (hc : k.2=true ∨¬CapPoint (PortAnnulus.outerDirection k.1.2) p) :
    ∃q : Cell (linePiece k j.val j.isLt a b).width (linePiece k j.val j.isLt a b).height,
      q∈(linePiece k j.val j.isLt a b).board.walls ∧((lineOffset k j.val).1+q.1.val,(lineOffset k j.val).2+q.2.val)=p := by
  obtain ⟨hflip,htravel,hd⟩:=last_line_metadata k j hj
  unfold linePiece
  rw [hflip,htravel]
  exact normal_piece_covers _ k.2 _ (filler_shape k j.val j.isLt).2.1 a b
    (lineOffset k j.val).1 (lineOffset k j.val).2 hd p hpx hpy hf hg hc

end PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateBoundary
