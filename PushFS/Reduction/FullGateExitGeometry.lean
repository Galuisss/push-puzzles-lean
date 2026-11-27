/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateOuterFrame

/-! Actual final long-line corners enter every exterior corner's free frame component. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting

open Gadgets.Wires FullGateBoundary
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] StorageAtlas.initial StorageAtlas.board profile profileOutside annularProfileBoxes annularBoxes

def lastLineIndex (g : GateTileState) (r : Fin 3) : Fin (curve (key g r)).length :=
  ⟨(curve (key g r)).length-1,by have :=last_valid (key g r); omega⟩

def exitCorner : Direction→Fin 4→Fin 4
  | .west,i | .east,i=>if i.val<2 then 1 else 3
  | .north,i | .south,i=>if i.val%2=0 then 3 else 1

private theorem normal_exit_geometry (d : Direction) (inc : Bool) (n : ℕ) (_hn : 2301≤n)
    (dx dy : ℕ) (hd : EndPlacement d inc n dx dy) (i : Fin 4) (p : C)
    (he : (p.1.val,p.2.val)=(lineOrientation d false).coordinates (n+5) 21 dx dy
      (Chain.corner n (exitCorner d i)))
    (hi : InFrame d ((outerCorner i).1.val,(outerCorner i).2.val)) :
    InFrame d (p.1.val,p.2.val) ∧SameFrameSide d p (outerCorner i) := by
  rw [RectOrientation.coordinates_point] at he
  cases d <;> fin_cases i <;> cases inc
  all_goals simp_all [EndPlacement,InFrame,SameFrameSide,outerCorner,exitCorner,lineOrientation,
    Chain.corner,RectOrientation.point,RectOrientation.width,RectOrientation.height]
  all_goals omega

private theorem line_exit_geometry (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool)
    (d : Direction) (inc : Bool) (dx dy : ℕ) (hflip : flip=false)
    (hd : EndPlacement d inc n dx dy) (i : Fin 4) (p : C)
    (he : (p.1.val,p.2.val)=(lineOrientation d flip).coordinates _ _ dx dy
      (lineBaseCorner flip n hn a b (exitCorner d i)))
    (hi : InFrame d ((outerCorner i).1.val,(outerCorner i).2.val)) :
    InFrame d (p.1.val,p.2.val) ∧SameFrameSide d p (outerCorner i) := by
  subst flip
  exact normal_exit_geometry d inc n hn dx dy hd i p he hi

/-- Every corner adjoins at least one of the three actual used faces. -/
theorem used_corner_face (g : GateTileState) (i : Fin 4) :
    ∃r : Fin 3,InFrame (PortAnnulus.outerDirection (g.key r).2)
      ((outerCorner i).1.val,(outerCorner i).2.val) := by
  have check : ∀p t : Fin 3,∀i : Fin 4,∃r : Fin 3,
      InFrame (PortAnnulus.boundaryDirection p ((t.val+r.val)%3))
        ((outerCorner i).1.val,(outerCorner i).2.val) := by decide +kernel
  exact check g.pattern g.rotation i

/-- The literal selected far corner of the true last line lies in the same safe exterior corridor as the requested macrocell corner. -/
theorem last_line_exit_geometry (g : GateTileState) (r : Fin 3) (i : Fin 4)
    (hi : InFrame (PortAnnulus.outerDirection (g.key r).2) ((outerCorner i).1.val,(outerCorner i).2.val)) :
    let p:=(lineEmbedding g r (lastLineIndex g r)).cells
      (lineCorner g r (lastLineIndex g r) (exitCorner (PortAnnulus.outerDirection (g.key r).2) i))
    InFrame (PortAnnulus.outerDirection (g.key r).2) (p.1.val,p.2.val) ∧
      SameFrameSide (PortAnnulus.outerDirection (g.key r).2) p (outerCorner i) := by
  let j:=lastLineIndex g r
  have hj : j.val+1=(curve (key g r)).length:=by dsimp only [j,lastLineIndex]; have :=last_valid (key g r); omega
  obtain ⟨hflip,htravel,hd⟩:=last_line_metadata (key g r) j hj
  have he:=line_coordinates g r j (lineCorner g r j (exitCorner (PortAnnulus.outerDirection (g.key r).2) i))
  rw [htravel] at he
  exact line_exit_geometry _ _ (filler_shape (key g r) j.val j.isLt).2.1 _ _ _ _ _ _ hflip hd i _ he hi

end PushPuzzle.PushFS.Reduction.GateTileRouting
