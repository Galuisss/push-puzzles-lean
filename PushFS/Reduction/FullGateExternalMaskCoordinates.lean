/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateExternalMask

/-! Literal coordinate contracts for the actual neighboring endpoint mask. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting

open Gadgets.Wires FullGateBoundary
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def farLineCell (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool) (k : Fin 3) :
    Cell (lineBase flip n hn a b).width (lineBase flip n hn a b).height :=
  (⟨n+(if flip then 20 else 0)+2+k.val,by rw [(line_dimensions flip n hn a b).1]; cases flip <;> simp only [Bool.false_eq_true,ite_false,ite_true]; all_goals have :=k.isLt; omega⟩,
    ⟨10,by rw [(line_dimensions flip n hn a b).2]; decide⟩)

private theorem farLineCell_mem (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool) (k : Fin 3) :
    farLineCell flip n hn a b k∈farLineMask flip n hn a b := by
  apply Finset.mem_filter.mpr
  refine ⟨(lineAllNeighbors_iff flip n hn a b _).mpr ⟨rfl,Or.inr ?_⟩,?_⟩
  all_goals dsimp only [farLineCell]; omega

def farEndpoint : Direction→Bool→Fin 3→(ℕ×ℕ)
  | .west,inc,k=>(3-inc.toNat-k.val,99034)
  | .east,inc,k=>(200003+inc.toNat+k.val,99034)
  | .north,inc,k=>(100003,3-inc.toNat-k.val)
  | .south,inc,k=>(100003,198064+inc.toNat+k.val)

def EndpointCollar : Direction→Bool→(ℕ×ℕ)→Prop
  | .west,inc,p=>p.2=99034 ∧1-inc.toNat≤p.1 ∧p.1≤3-inc.toNat
  | .east,inc,p=>p.2=99034 ∧200003+inc.toNat≤p.1 ∧p.1≤200005+inc.toNat
  | .north,inc,p=>p.1=100003 ∧1-inc.toNat≤p.2 ∧p.2≤3-inc.toNat
  | .south,inc,p=>p.1=100003 ∧198064+inc.toNat≤p.2 ∧p.2≤198066+inc.toNat

private theorem normal_far_endpoint (n : ℕ) (hn : 2301≤n) (a b : Bool) (d : Direction) (inc : Bool)
    (dx dy : ℕ) (hd : EndPlacement d inc n dx dy) (k : Fin 3) :
    (lineOrientation d false).coordinates (n+5) 21 dx dy (farLineCell false n hn a b k)=farEndpoint d inc k := by
  change (lineOrientation d false).coordinates (n+5) 21 dx dy
    ((⟨n+2+k.val,by have :=k.isLt; omega⟩,10) : Chain.C n)=farEndpoint d inc k
  rw [RectOrientation.coordinates_point]
  cases d <;> cases inc <;> fin_cases k
  all_goals simp_all [EndPlacement,lineOrientation,RectOrientation.point,RectOrientation.width,RectOrientation.height,farEndpoint]
  all_goals omega

private theorem line_far_endpoint (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool) (d : Direction) (inc : Bool)
    (dx dy : ℕ) (hflip : flip=false) (hd : EndPlacement d inc n dx dy) (k : Fin 3) :
    (lineOrientation d flip).coordinates _ _ dx dy (farLineCell flip n hn a b k)=farEndpoint d inc k := by
  subst flip
  exact normal_far_endpoint n hn a b d inc dx dy hd k

private theorem last_far_coordinates (g : GateTileState) (r : Fin 3) (k : Fin 3) :
    let j:=lastLineIndex g r
    let p:=(lineEmbedding g r j).cells (farLineCell (fillerFlip (key g r) j.val) (fillerSpan (key g r) j.val)
      (filler_shape _ _ j.isLt).2.1 (Inventory.initialPhase g r) (Inventory.targetPhase g r) k)
    (p.1.val,p.2.val)=farEndpoint (PortAnnulus.outerDirection (g.key r).2) (g.incoming.get r) k := by
  let j:=lastLineIndex g r
  have hj : j.val+1=(curve (key g r)).length:=by dsimp only [j,lastLineIndex]; have :=last_valid (key g r); omega
  obtain ⟨hflip,htravel,hd⟩:=last_line_metadata (key g r) j hj
  have he:=line_coordinates g r j (farLineCell (fillerFlip (key g r) j.val) (fillerSpan (key g r) j.val)
    (filler_shape _ _ j.isLt).2.1 (Inventory.initialPhase g r) (Inventory.targetPhase g r) k)
  have hor:=congrArg (fun d : Direction=>(lineOrientation d (fillerFlip (key g r) j.val)).coordinates _ _
    (lineOffset (key g r) j.val).1 (lineOffset (key g r) j.val).2
    (farLineCell (fillerFlip (key g r) j.val) (fillerSpan (key g r) j.val)
      (filler_shape _ _ j.isLt).2.1 (Inventory.initialPhase g r) (Inventory.targetPhase g r) k)) htravel
  exact he.trans (hor.trans (line_far_endpoint _ _ _ _ _ _ _ _ _ hflip hd k))

private theorem collar_point (d : Direction) (inc : Bool) (p : ℕ×ℕ) (hp : EndpointCollar d inc p) :
    ∃k : Fin 3,farEndpoint d inc k=p := by
  cases d <;> cases inc <;> norm_num [EndpointCollar] at hp
  case west.false=>exact ⟨⟨3-p.1,by omega⟩,Prod.ext (by norm_num [farEndpoint]; omega) hp.1.symm⟩
  case west.true=>exact ⟨⟨2-p.1,by omega⟩,Prod.ext (by norm_num [farEndpoint]; omega) hp.1.symm⟩
  case east.false=>exact ⟨⟨p.1-200003,by omega⟩,Prod.ext (by norm_num [farEndpoint]; omega) hp.1.symm⟩
  case east.true=>exact ⟨⟨p.1-200004,by omega⟩,Prod.ext (by norm_num [farEndpoint]; omega) hp.1.symm⟩
  case north.false=>exact ⟨⟨3-p.2,by omega⟩,Prod.ext hp.1.symm (by norm_num [farEndpoint]; omega)⟩
  case north.true=>exact ⟨⟨2-p.2,by omega⟩,Prod.ext hp.1.symm (by norm_num [farEndpoint]; omega)⟩
  case south.false=>exact ⟨⟨p.2-198064,by omega⟩,Prod.ext hp.1.symm (by norm_num [farEndpoint]; omega)⟩
  case south.true=>exact ⟨⟨p.2-198065,by omega⟩,Prod.ext hp.1.symm (by norm_num [farEndpoint]; omega)⟩

/-- Exact port-relative coordinates suffice to place a real neighboring box in the actual nine-cell mask. -/
private theorem outer_mask_of_collar (g : GateTileState) (r : Fin 3) (p : C)
    (hp : EndpointCollar (PortAnnulus.outerDirection (g.key r).2) (g.incoming.get r) (p.1.val,p.2.val)) :
    OuterMask g p := by
  obtain ⟨k,hk⟩:=collar_point _ _ _ hp
  apply Or.inl
  refine ⟨r,farLineCell _ _ _ _ _ k,farLineCell_mem _ _ _ _ _ k,?_⟩
  have he:=(last_far_coordinates g r k).trans hk
  exact Prod.ext (Fin.ext (congrArg Prod.fst he)) (Fin.ext (congrArg Prod.snd he))

/-- All source and target slots of an actual adjacent ordinary glyph, including its second box on the outer padding edge. -/
def NeighborCollar : Direction→Bool→(ℕ×ℕ)→Prop
  | .west,inc,p=>p.2=99034 ∧p.1≤3-inc.toNat
  | .east,inc,p=>p.2=99034 ∧200003+inc.toNat≤p.1
  | .north,inc,p=>p.1=100003 ∧p.2≤3-inc.toNat
  | .south,inc,p=>p.1=100003 ∧198064+inc.toNat≤p.2

private theorem neighbor_collar_split (d : Direction) (inc : Bool) (p : C)
    (hp : NeighborCollar d inc (p.1.val,p.2.val)) :
    EndpointCollar d inc (p.1.val,p.2.val) ∨(p.1.val=(paddingPoint d).1 ∧p.2.val=(paddingPoint d).2) := by
  have hx:=p.1.isLt
  have hy:=p.2.isLt
  cases d <;> cases inc
  all_goals simp only [NeighborCollar,EndpointCollar,paddingPoint,Bool.toNat_false,Bool.toNat_true] at hp ⊢
  all_goals omega

theorem outer_mask_of_neighbor_collar (g : GateTileState) (r : Fin 3) (p : C)
    (hp : NeighborCollar (PortAnnulus.outerDirection (g.key r).2) (g.incoming.get r) (p.1.val,p.2.val)) :
    OuterMask g p := by
  rcases neighbor_collar_split _ _ p hp with hs|hs
  · exact outer_mask_of_collar g r p hs
  · exact Or.inr ⟨_,Prod.ext hs.1 hs.2⟩

end PushPuzzle.PushFS.Reduction.GateTileRouting
