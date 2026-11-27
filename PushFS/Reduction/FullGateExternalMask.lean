/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateExitGeometry

/-! The nine actual far-end collar cells containing every neighboring macrocell's possible endpoint boxes. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting

open Gadgets Gadgets.Wires FullGateBoundary
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] StorageAtlas.initial StorageAtlas.board profile profileOutside annularProfileBoxes annularBoxes

def farLineMask (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool) :
    Finset (Cell (lineBase flip n hn a b).width (lineBase flip n hn a b).height) :=
  (lineAllNeighbors flip n hn a b).filter (fun p=>n+(if flip then 20 else 0)+2≤p.1.val)

/-- Three literal far collar cells at each of the three true external port lines. -/
def RawOuterMask (g : GateTileState) (p : C) : Prop :=
  ∃r : Fin 3,∃q : Cell (lineInput g r (lastLineIndex g r)).width (lineInput g r (lastLineIndex g r)).height,
    q∈farLineMask (fillerFlip (key g r) (lastLineIndex g r).val)
      (fillerSpan (key g r) (lastLineIndex g r).val) (filler_shape _ _ (lastLineIndex g r).isLt).2.1
      (Inventory.initialPhase g r) (Inventory.targetPhase g r) ∧
      (lineEmbedding g r (lastLineIndex g r)).cells q=p

private theorem normal_far_mask_frame (d : Direction) (inc : Bool) (n : ℕ) (_hn : 2301≤n)
    (dx dy : ℕ) (hd : EndPlacement d inc n dx dy) (q : Chain.C n)
    (hq : q.2.val=10 ∧n+2≤q.1.val) (p : C)
    (he : (p.1.val,p.2.val)=(lineOrientation d false).coordinates (n+5) 21 dx dy q) :
    InFrame d (p.1.val,p.2.val) ∧OuterRail p := by
  rw [RectOrientation.coordinates_point] at he
  have hx:=q.1.isLt
  cases d <;> cases inc
  all_goals simp_all [EndPlacement,InFrame,OuterRail,lineOrientation,RectOrientation.point,RectOrientation.width,RectOrientation.height]
  all_goals omega

private theorem far_mask_frame (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool)
    (d : Direction) (inc : Bool) (dx dy : ℕ) (hflip : flip=false) (hd : EndPlacement d inc n dx dy)
    (q : Cell (lineBase flip n hn a b).width (lineBase flip n hn a b).height)
    (hq : q∈farLineMask flip n hn a b) (p : C)
    (he : (p.1.val,p.2.val)=(lineOrientation d flip).coordinates _ _ dx dy q) :
    InFrame d (p.1.val,p.2.val) ∧OuterRail p := by
  subst flip
  obtain ⟨hq,hx⟩:=Finset.mem_filter.mp hq
  have hy:=(lineAllNeighbors_iff false n hn a b q).mp hq
  exact normal_far_mask_frame d inc n hn dx dy hd q ⟨hy.1,hx⟩ p he

private theorem outer_mask_frame (g : GateTileState) (r : Fin 3)
    (q : Cell (lineInput g r (lastLineIndex g r)).width (lineInput g r (lastLineIndex g r)).height)
    (hq : q∈farLineMask (fillerFlip (key g r) (lastLineIndex g r).val)
      (fillerSpan (key g r) (lastLineIndex g r).val) (filler_shape _ _ (lastLineIndex g r).isLt).2.1
      (Inventory.initialPhase g r) (Inventory.targetPhase g r)) :
    let p:=(lineEmbedding g r (lastLineIndex g r)).cells q
    InFrame (PortAnnulus.outerDirection (g.key r).2) (p.1.val,p.2.val) ∧OuterRail p := by
  let j:=lastLineIndex g r
  have hj : j.val+1=(curve (key g r)).length:=by dsimp only [j,lastLineIndex]; have :=last_valid (key g r); omega
  obtain ⟨hflip,htravel,hd⟩:=last_line_metadata (key g r) j hj
  have he:=line_coordinates g r j q
  rw [htravel] at he
  exact far_mask_frame _ _ (filler_shape (key g r) j.val j.isLt).2.1 _ _ _ _ _ _ hflip hd q hq _ he

private theorem raw_outer_mask_rail (g : GateTileState) (p : C)
    (hp : RawOuterMask g p) : OuterRail p := by
  obtain ⟨r,q,hq,rfl⟩:=hp
  exact (outer_mask_frame g r q hq).2

private theorem direction_injective (g : GateTileState) :
    Function.Injective (fun r : Fin 3=>PortAnnulus.outerDirection (g.key r).2) := by
  have hh : ∀p t : Fin 3,Function.Injective (fun r : Fin 3=>PortAnnulus.boundaryDirection p ((t.val+r.val)%3)):=by decide +kernel
  exact hh g.pattern g.rotation

/-- The complete external mask has empty preimage in every short protected turn. -/
private theorem raw_outer_mask_corner_empty (g : GateTileState) (r : Fin 3) (j : Fin ((curve
    (key g r)).length-1))
    (p : Cell (ShortCorners.width (cornerKind (key g r) j.val)) (ShortCorners.height (cornerKind (key g r) j.val))) :
    ¬RawOuterMask g ((armCornerEmbedding g r j).cells p) := by
  rintro ⟨s,q,hq,he⟩
  have hf:=(outer_mask_frame g s q hq).1
  rw [he] at hf
  have ho:=raw_owner g (cornerIndex g r j) (PortAnnulus.outerDirection (g.key s).2)
    ((cornerIso (key g r) j.val).geometry.cells p) hf
  exact ho

/-- An external mask can meet a line only at that very port's last-line far collar. -/
private theorem raw_outer_mask_line_collar (g : GateTileState) (r : Fin 3) (j : Fin (curve
    (key g r)).length)
    (p : Cell (lineInput g r j).width (lineInput g r j).height)
    (hp : RawOuterMask g ((lineEmbedding g r j).cells p)) :
    p∈lineAllNeighbors (fillerFlip (key g r) j.val) (fillerSpan (key g r) j.val)
      (filler_shape _ _ j.isLt).2.1 (Inventory.initialPhase g r) (Inventory.targetPhase g r) := by
  obtain ⟨s,q,hq,he⟩:=hp
  have hf:=(outer_mask_frame g s q hq).1
  rw [he] at hf
  have ho:=raw_owner g (lineIndex g r j) (PortAnnulus.outerDirection (g.key s).2)
    ((lineRawIso (key g r) j.val j.isLt (Inventory.initialPhase g r) (Inventory.targetPhase g r)).cells p) hf
  obtain ⟨hj,hd⟩:=ho
  have hrs : r=s:=direction_injective g hd
  subst s
  have hj' : j=lastLineIndex g r:=Fin.ext (by dsimp only [lastLineIndex]; omega)
  subst j
  have he':= (lineEmbedding g r (lastLineIndex g r)).cells.injective he
  rw [he'] at hq
  exact (Finset.mem_filter.mp hq).1

/-- No external endpoint cell meets any of the four buffered core primitives. -/
private theorem raw_outer_mask_buffer_empty (g : GateTileState) (i : Fin 4)
    (p : Cell (Inventory.piece g (.inl i)).width (Inventory.piece g (.inl i)).height) :
    ¬RawOuterMask g ((primitiveEmbedding g (.inl i)).cells p) := by
  rintro ⟨s,q,hq,he⟩
  have hf:=(outer_mask_frame g s q hq).1
  rw [he] at hf
  exact raw_owner g (.inl i) (PortAnnulus.outerDirection (g.key s).2) p hf

/-- The outermost padding cell on each real boundary rail. -/
def paddingPoint : Direction→(ℕ×ℕ)
  | .west=>(0,99034)
  | .east=>(200006,99034)
  | .north=>(100003,0)
  | .south=>(100003,198067)

def OuterPadding (p : C) : Prop := ∃d,(p.1.val,p.2.val)=paddingPoint d

/-- Actual foreign endpoints use the three far collar cells and, for an output's second high-phase box, the outermost padding cell. -/
def OuterMask (g : GateTileState) (p : C) : Prop := RawOuterMask g p ∨OuterPadding p

private theorem padding_frame (d : Direction) (p : C) (hp : (p.1.val,p.2.val)=paddingPoint d) :
    InFrame d (p.1.val,p.2.val) ∧OuterRail p := by
  cases d <;> dsimp only [paddingPoint,InFrame,OuterRail] at * <;> obtain ⟨hx,hy⟩:=Prod.mk.inj hp <;> omega

theorem outer_mask_rail (g : GateTileState) (p : C) (hp : OuterMask g p) : OuterRail p := by
  rcases hp with hp|⟨d,hp⟩
  · exact raw_outer_mask_rail g p hp
  · exact (padding_frame d p hp).2

theorem outer_mask_floor (g : GateTileState) (p : C) (hp : OuterMask g p) : p∉(fullPuzzle g).board.walls :=
  outer_rail_floor g p (outer_mask_rail g p hp)

private theorem normal_padding_collar (n : ℕ) (d : Direction) (inc : Bool) (dx dy : ℕ)
    (hd : EndPlacement d inc n dx dy) (q : Chain.C n)
    (he : (lineOrientation d false).coordinates (n+5) 21 dx dy q=paddingPoint d) :
    q.2.val=10 ∧n+2≤q.1.val := by
  rw [RectOrientation.coordinates_point] at he
  have hx:=q.1.isLt
  have hy:=q.2.isLt
  have hex:=congrArg Prod.fst he
  have hey:=congrArg Prod.snd he
  cases d <;> cases inc
  all_goals simp only [EndPlacement,paddingPoint,lineOrientation,RectOrientation.point,RectOrientation.width,RectOrientation.height,
    Bool.toNat_false,Bool.toNat_true,Bool.not_false,Bool.false_eq_true,ite_true,ite_false] at hd hex hey
  all_goals omega

private theorem line_padding_collar (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool)
    (d : Direction) (inc : Bool) (dx dy : ℕ) (hflip : flip=false) (hd : EndPlacement d inc n dx dy)
    (q : Cell (lineBase flip n hn a b).width (lineBase flip n hn a b).height)
    (he : (lineOrientation d flip).coordinates _ _ dx dy q=paddingPoint d) :
    q∈lineAllNeighbors flip n hn a b := by
  subst flip
  have hh:=normal_padding_collar n d inc dx dy hd q he
  exact (lineAllNeighbors_iff false n hn a b q).mpr ⟨hh.1,Or.inr hh.2⟩

private theorem outer_padding_line_collar (g : GateTileState) (r : Fin 3) (j : Fin (curve (key g r)).length)
    (p : Cell (lineInput g r j).width (lineInput g r j).height)
    (hp : OuterPadding ((lineEmbedding g r j).cells p)) :
    p∈lineAllNeighbors (fillerFlip (key g r) j.val) (fillerSpan (key g r) j.val)
      (filler_shape _ _ j.isLt).2.1 (Inventory.initialPhase g r) (Inventory.targetPhase g r) := by
  obtain ⟨d,he⟩:=hp
  have hf:=(padding_frame d _ he).1
  have ho:=raw_owner g (lineIndex g r j) d
    ((lineRawIso (key g r) j.val j.isLt (Inventory.initialPhase g r) (Inventory.targetPhase g r)).cells p) hf
  obtain ⟨hj,hd⟩:=ho
  obtain ⟨hflip,htravel,hplace⟩:=last_line_metadata (key g r) j hj
  have hcoords:=(line_coordinates g r j p).symm.trans he
  have hor:=congrArg (fun d : Direction=>(lineOrientation d (fillerFlip (key g r) j.val)).coordinates _ _
    (lineOffset (key g r) j.val).1 (lineOffset (key g r) j.val).2 p) (htravel.trans hd)
  have hplace' : EndPlacement d (key g r).2 (fillerSpan (key g r) j.val)
      (lineOffset (key g r) j.val).1 (lineOffset (key g r) j.val).2:=hd ▸hplace
  exact line_padding_collar _ _ (filler_shape _ _ j.isLt).2.1 _ _ d _ _ _ hflip hplace' p (hor.symm.trans hcoords)

theorem outer_mask_line_collar (g : GateTileState) (r : Fin 3) (j : Fin (curve (key g r)).length)
    (p : Cell (lineInput g r j).width (lineInput g r j).height)
    (hp : OuterMask g ((lineEmbedding g r j).cells p)) :
    p∈lineAllNeighbors (fillerFlip (key g r) j.val) (fillerSpan (key g r) j.val)
      (filler_shape _ _ j.isLt).2.1 (Inventory.initialPhase g r) (Inventory.targetPhase g r) :=
  hp.elim (raw_outer_mask_line_collar g r j p) (outer_padding_line_collar g r j p)

theorem outer_mask_corner_empty (g : GateTileState) (r : Fin 3) (j : Fin ((curve (key g r)).length-1))
    (p : Cell (ShortCorners.width (cornerKind (key g r) j.val)) (ShortCorners.height (cornerKind (key g r) j.val))) :
    ¬OuterMask g ((armCornerEmbedding g r j).cells p) := by
  rintro (hp|⟨d,he⟩)
  · exact raw_outer_mask_corner_empty g r j p hp
  · have hf:=(padding_frame d _ he).1
    exact raw_owner g (cornerIndex g r j) d ((cornerIso (key g r) j.val).geometry.cells p) hf

theorem outer_mask_buffer_empty (g : GateTileState) (i : Fin 4)
    (p : Cell (Inventory.piece g (.inl i)).width (Inventory.piece g (.inl i)).height) :
    ¬OuterMask g ((primitiveEmbedding g (.inl i)).cells p) := by
  rintro (hp|⟨d,he⟩)
  · exact raw_outer_mask_buffer_empty g i p hp
  · exact raw_owner g (.inl i) d p (padding_frame d _ he).1

end PushPuzzle.PushFS.Reduction.GateTileRouting
