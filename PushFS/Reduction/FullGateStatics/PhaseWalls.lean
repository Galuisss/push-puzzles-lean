/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateInventory

/-! Literal wall ownership of every physical primitive is independent of both canonical box phases. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics

open Inventory Gadgets Gadgets.Wires
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def wallAt (g : GateTileState) (i : Inventory.Index g) (p : ℕ×ℕ) : Prop :=
  ∃q : Cell (Inventory.piece g i).width (Inventory.piece g i).height,
    q∈(Inventory.piece g i).board.walls ∧
      ((Inventory.offset g i).1+q.1.val,(Inventory.offset g i).2+q.2.val)=p

def lineWallAt (flip : Bool) (n : ℕ) (hn : 2301≤n) (d : Direction) (a b : Bool) (dx dy : ℕ) (p : ℕ×ℕ) : Prop :=
  ∃q : Cell (lineBase flip n hn a b).width (lineBase flip n hn a b).height,
    q∈(lineBase flip n hn a b).board.walls ∧
      (lineOrientation d flip).coordinates _ _ dx dy q=p

private theorem lineWallAt_phases (flip : Bool) (n : ℕ) (hn : 2301≤n) (d : Direction)
    (a b c e : Bool) (dx dy : ℕ) (p : ℕ×ℕ) :
    lineWallAt flip n hn d a b dx dy p ↔lineWallAt flip n hn d c e dx dy p := by
  cases flip
  · let P : Prop:=∃q : Chain.C n,q∈Chain.walls n hn ∧(lineOrientation d false).coordinates (n+5) 21 dx dy q=p
    change P↔P
    exact Iff.rfl
  · change (∃q : FlippedChain.C n,q∈(FlippedChain.atlas n hn (FlippedChain.uniform a) (FlippedChain.uniform b)).walls ∧
      (lineOrientation d true).coordinates (n+25) 21 dx dy q=p)↔
      (∃q : FlippedChain.C n,q∈(FlippedChain.atlas n hn (FlippedChain.uniform c) (FlippedChain.uniform e)).walls ∧
      (lineOrientation d true).coordinates (n+25) 21 dx dy q=p)
    rw [FlippedChain.atlas_walls,FlippedChain.atlas_walls]

private theorem oriented_wallAt {w h W H : ℕ} (e : GridIsometry w h W H) (B : Board w h)
    (dx dy : ℕ) (p : ℕ×ℕ) :
    (∃q : Cell W H,q∈(e.board B).walls ∧(dx+q.1.val,dy+q.2.val)=p)↔
      (∃q : Cell w h,q∈B.walls ∧(dx+(e.cells q).1.val,dy+(e.cells q).2.val)=p) := by
  constructor
  · rintro ⟨q,hq,he⟩
    obtain ⟨r,hr,rfl⟩:=Finset.mem_map.mp hq
    exact ⟨r,hr,he⟩
  · rintro ⟨q,hq,he⟩
    exact ⟨e.cells q,Finset.mem_map.mpr ⟨q,hq,rfl⟩,he⟩

private theorem wallAt_line (g : GateTileState) (role : Fin 3) (j : Fin (curve
    (key g role)).length) (p : ℕ×ℕ) :
    wallAt g (.inr (.inl ⟨role,.inl j⟩)) p ↔
      lineWallAt (fillerFlip (key g role) j.val) (fillerSpan (key g role) j.val)
        (filler_shape (key g role) j.val j.isLt).2.1 (original (key g role) j.val).travel
        (initialPhase g role) (targetPhase g role) (lineOffset (key g role) j.val).1 (lineOffset (key g role) j.val).2 p :=
  oriented_wallAt _ _ _ _ p

def cornerWallAt (k : Key) (i : ℕ) (p : ℕ×ℕ) : Prop :=
  ∃q : Cell (ShortCorners.width (cornerKind k i)) (ShortCorners.height (cornerKind k i)),
    q∈(ShortCorners.template (cornerKind k i)).walls ∧
      (cornerOrientation k i).coordinates _ _ (cornerOffset k i).1 (cornerOffset k i).2 q=p

private theorem wallAt_corner (g : GateTileState) (role : Fin 3) (j : Fin ((curve
    (key g role)).length-1)) (p : ℕ×ℕ) :
    wallAt g (.inr (.inl ⟨role,.inr j⟩)) p ↔cornerWallAt (key g role) j.val p :=
  oriented_wallAt (cornerIso (key g role) j.val).geometry
    ((ShortCorners.puzzle (cornerKind (key g role) j.val) (initialPhase g role) (targetPhase g role)).board)
    (cornerOffset (key g role) j.val).1 (cornerOffset (key g role) j.val).2 p

private theorem wallAt_geometry (g : GateTileState) (i : Inventory.Index g) (p : ℕ×ℕ) :
    wallAt (ofGeometry (geometry g)) i p ↔wallAt g i p := by
  rcases g with ⟨⟨kind,a,b⟩,incoming,pattern,rotation⟩
  rcases i with i | (⟨role,j | j⟩ | role)
  · fin_cases i
    · let P : Prop:=∃q : Gates.C,q∈Gates.walls kind ∧
        ((bufferOffset kind).1+2311+q.1.val,(bufferOffset kind).2+2321+q.2.val)=p
      change P↔P
      exact Iff.rfl
    · let P : Prop:=∃q : Cell 2306 21,
        q∈(Chain.walls 2301 (by omega)).map (GateLead.westIso kind 2301).cells.toEmbedding ∧
        ((bufferOffset kind).1+(if kind then 8 else 9)+q.1.val,
          (bufferOffset kind).2+(2311+(if kind then 29 else 90))+q.2.val)=p
      change P↔P
      exact Iff.rfl
    · let P : Prop:=∃q : Cell 21 2306,
        q∈(Chain.walls 2301 (by omega)).map (GateLead.northIso 2301).cells.toEmbedding ∧
        ((bufferOffset kind).1+(2301+(if kind then 43 else 44))+q.1.val,
          (bufferOffset kind).2+19+q.2.val)=p
      change P↔P
      exact Iff.rfl
    · let P : Prop:=∃q : Cell 2306 21,
        q∈(Chain.walls 2301 (by omega)).map (GateLead.eastIso 2301).cells.toEmbedding ∧
        ((bufferOffset kind).1+(2301+(if kind then 88 else 87))+q.1.val,
          (bufferOffset kind).2+2401+q.2.val)=p
      change P↔P
      exact Iff.rfl
  · let g' : GateTileState:=⟨⟨kind,a,b⟩,incoming,pattern,rotation⟩
    exact (wallAt_line (ofGeometry (geometry g')) role j p).trans
      ((lineWallAt_phases (fillerFlip (key g' role) j.val) (fillerSpan (key g' role) j.val)
        (filler_shape (key g' role) j.val j.isLt).2.1 (original (key g' role) j.val).travel
        (initialPhase (ofGeometry (geometry g')) role) (targetPhase (ofGeometry (geometry g')) role)
        (initialPhase g' role) (targetPhase g' role)
        (lineOffset (key g' role) j.val).1 (lineOffset (key g' role) j.val).2 p).trans
        (wallAt_line g' role j p).symm)
  · let g' : GateTileState:=⟨⟨kind,a,b⟩,incoming,pattern,rotation⟩
    exact (wallAt_corner (ofGeometry (geometry g')) role j p).trans (wallAt_corner g' role j p).symm
  · rfl

/-- The true whole-board walls retain exactly the same finite set under either canonical phase assignment. -/
theorem full_walls_geometry (g : GateTileState) :
    (fullAtlas (ofGeometry (geometry g))).board.walls=(fullAtlas g).board.walls := by
  ext p
  have hg:=full_wall_membership g p
  have hz:=full_wall_membership (ofGeometry (geometry g)) p
  change p∈(fullAtlas g).board.walls ↔∃i,wallAt g i (p.1.val,p.2.val) at hg
  change p∈(fullAtlas (ofGeometry (geometry g))).board.walls ↔
    ∃i,wallAt (ofGeometry (geometry g)) i (p.1.val,p.2.val) at hz
  exact hz.trans ((exists_congr fun i=>wallAt_geometry g i _).trans hg.symm)

/-- Any two complete gate instances with the same physical geometry have exactly the same actual walls. -/
theorem full_walls_eq (g h : GateTileState) (he : geometry g=geometry h) :
    @Eq (Finset C) (fullPuzzle g).board.walls (fullPuzzle h).board.walls := by
  change (fullAtlas g).board.walls=(fullAtlas h).board.walls
  exact (full_walls_geometry g).symm.trans
    ((congrArg (fun k : Geometry=>(fullAtlas (ofGeometry k)).board.walls) he).trans (full_walls_geometry h))

end PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics
