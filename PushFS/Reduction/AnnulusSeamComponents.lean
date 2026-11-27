/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.AnnulusSignalSeams
public import PushFS.Reduction.FullGateRawLabels

/-! Every actual annular line/corner seam joins its two real physical source identities in one wall-only SCC. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting

open Inventory Gadgets.Wires Catalog Soundness
set_option maxRecDepth 65536
set_option maxHeartbeats 100000
attribute [local irreducible] curve original cornerKind cornerOrientation cornerIso lineOrientation

def lineEndpointLabel (g : GateTileState) (r : Fin 3) (j : Fin (curve (key g r)).length) (last : Bool) : RawLabel g :=
  ⟨.inr (.inl ⟨r,.inl j⟩),if last then lineLast (fillerFlip (key g r) j.val) (fillerSpan (key g r) j.val)
    (filler_shape (key g r) j.val j.isLt).2.1 else lineFirst (fillerFlip (key g r) j.val) (fillerSpan (key g r) j.val)
    (filler_shape (key g r) j.val j.isLt).2.1⟩

def cornerEndpointLabel (g : GateTileState) (r : Fin 3) (j : Fin ((curve (key g r)).length-1)) (last : Bool) : RawLabel g :=
  ⟨.inr (.inl ⟨r,.inr j⟩),if last then ShortCorners.last (cornerKind (key g r) j.val)
    else ShortCorners.first (cornerKind (key g r) j.val)⟩

private theorem corner_line_seam_eq (q : Key) (i : ℕ) (hi : i+1<(curve q).length) (a b : Bool) :
    (cornerRect q i hi).cells ((cornerIso q i).geometry.cells (cornerExitGhost (cornerKind q i) a))=
      (lineRect q (i+1) hi a b).cells ((lineSlotMatching q (i+1) hi a b).source
        (lineFirst (fillerFlip q (i+1)) (fillerSpan q (i+1)) (filler_shape q (i+1) hi).2.1)) := by
  let j : Fin ((curve q).length-1):=⟨i,by omega⟩
  have hxy:=(corner_ghost_coordinates q i a).trans
    ((corner_line_endpoints_checked q j a).1.trans (line_endpoint_coordinates q (i+1) hi a b false).symm)
  apply Prod.ext <;> apply Fin.ext
  · exact congrArg Prod.fst hxy
  · exact congrArg Prod.snd hxy

theorem line_corner_component (g : GateTileState) (r : Fin 3) (j : Fin ((curve (key g r)).length-1)) :
    component (fullPuzzle g).board (rawSource g (lineEndpointLabel g r ⟨j.val,by have:=j.isLt; omega⟩ true))=
      component (fullPuzzle g).board (rawSource g (cornerEndpointLabel g r j false)) := by
  let q:=key g r
  let a:=initialPhase g r
  let b:=targetPhase g r
  have hi:j.val<(curve q).length:=by have hj:j.val<(curve q).length-1:=j.isLt; omega
  let f:=fillerFlip q j.val
  let n:=fillerSpan q j.val
  let hn:2301≤n:=(filler_shape q j.val hi).2.1
  let e:=lineRawIso q j.val hi a b
  let ix : Inventory.Index g:=.inr (.inl ⟨r,.inl ⟨j.val,hi⟩⟩)
  let eg:=primitiveEmbedding g ix
  have hc:SameComponent (linePiece q j.val hi a b).board
      ((lineSlotMatching q j.val hi a b).source (lineLast f n hn)) (e.cells (lineExitGhost f n hn a b)) :=
    (e.sameComponent_iff (lineBase f n hn a b).board
      ((lineMatching f n hn a b).source (lineLast f n hn)) (lineExitGhost f n hn a b)).mpr (line_exit_component f n hn a b)
  have hw:=primitive_walls_agree g ix
  have hp:SameComponent (fullPuzzle g).board
      (rawSource g (lineEndpointLabel g r ⟨j.val,hi⟩ true)) (eg.cells (e.cells (lineExitGhost f n hn a b))) :=
    ⟨GridEmbedding.staticReach hw hc.1,GridEmbedding.staticReach hw hc.2⟩
  have he : eg.cells (e.cells (lineExitGhost f n hn a b))=rawSource g (cornerEndpointLabel g r j false) := by
    have hxy:= (line_ghost_coordinates q j.val hi a b).trans
      ((line_corner_endpoints_checked q j a).1.trans (corner_endpoint_coordinates q j.val a b false).symm)
    apply Prod.ext <;> apply Fin.ext
    · change (lineOffset q j.val).1+(e.cells (lineExitGhost f n hn a b)).1.val=
        (cornerOffset q j.val).1+((cornerMatching q j.val a b).source (ShortCorners.first (cornerKind q j.val))).1.val
      exact congrArg Prod.fst hxy
    · change (lineOffset q j.val).2+(e.cells (lineExitGhost f n hn a b)).2.val=
        (cornerOffset q j.val).2+((cornerMatching q j.val a b).source (ShortCorners.first (cornerKind q j.val))).2.val
      exact congrArg Prod.snd hxy
  rw [he] at hp
  exact component_eq_iff.mpr hp

theorem corner_line_component (g : GateTileState) (r : Fin 3) (j : Fin ((curve (key g r)).length-1)) :
    component (fullPuzzle g).board (rawSource g (cornerEndpointLabel g r j true))=
      component (fullPuzzle g).board (rawSource g (lineEndpointLabel g r ⟨j.val+1,by have:=j.isLt; omega⟩ false)) := by
  let q:=key g r
  let a:=initialPhase g r
  let b:=targetPhase g r
  let k:=cornerKind q j.val
  let e:=(cornerIso q j.val).geometry
  let ix : Inventory.Index g:=.inr (.inl ⟨r,.inr j⟩)
  let eg:=primitiveEmbedding g ix
  have hc:SameComponent (cornerPiece q j.val a b).board
      ((cornerMatching q j.val a b).source (ShortCorners.last k)) (e.cells (cornerExitGhost k a)) :=
    (e.sameComponent_iff (ShortCorners.puzzle k a b).board
      ((ShortCorners.slotMatching k a b).source (ShortCorners.last k)) (cornerExitGhost k a)).mpr (corner_exit_component k a b)
  have hw:=primitive_walls_agree g ix
  have hp:SameComponent (fullPuzzle g).board (rawSource g (cornerEndpointLabel g r j true))
      (eg.cells (e.cells (cornerExitGhost k a))) :=
    ⟨GridEmbedding.staticReach hw hc.1,GridEmbedding.staticReach hw hc.2⟩
  have hi:j.val+1<(curve q).length:=by have hj:j.val<(curve q).length-1:=j.isLt; omega
  have he : eg.cells (e.cells (cornerExitGhost k a))=rawSource g (lineEndpointLabel g r ⟨j.val+1,hi⟩ false) := by
    exact corner_line_seam_eq q j.val hi a b
  rw [he] at hp
  exact component_eq_iff.mpr hp

private theorem step_order (d : Direction) (p q : ℕ×ℕ) (h : DirectionalStep d p q) : DirectionalOrder d p q := by
  cases d <;> dsimp only [DirectionalStep,DirectionalOrder] at * <;> omega

theorem line_corner_order (g : GateTileState) (r : Fin 3) (j : Fin ((curve (key g r)).length-1)) :
    DirectionalOrder (original (key g r) j.val).travel
      ((rawSource g (lineEndpointLabel g r ⟨j.val,by have:=j.isLt; omega⟩ true)).1.val,
        (rawSource g (lineEndpointLabel g r ⟨j.val,by have:=j.isLt; omega⟩ true)).2.val)
      ((rawSource g (cornerEndpointLabel g r j false)).1.val,(rawSource g (cornerEndpointLabel g r j false)).2.val) := by
  let q:=key g r
  let a:=initialPhase g r
  let b:=targetPhase g r
  have hi:j.val<(curve q).length:=by have hj:j.val<(curve q).length-1:=j.isLt; omega
  have hs:=step_order _ _ _ (line_corner_endpoints_checked q j a).2
  have hl:=line_endpoint_coordinates q j.val hi a b true
  have hc:=corner_endpoint_coordinates q j.val a b false
  exact hl.symm ▸hc.symm ▸hs

theorem corner_line_order (g : GateTileState) (r : Fin 3) (j : Fin ((curve (key g r)).length-1)) :
    DirectionalOrder (original (key g r) (j.val+1)).travel
      ((rawSource g (cornerEndpointLabel g r j true)).1.val,(rawSource g (cornerEndpointLabel g r j true)).2.val)
      ((rawSource g (lineEndpointLabel g r ⟨j.val+1,by have:=j.isLt; omega⟩ false)).1.val,
        (rawSource g (lineEndpointLabel g r ⟨j.val+1,by have:=j.isLt; omega⟩ false)).2.val) := by
  let q:=key g r
  let a:=initialPhase g r
  let b:=targetPhase g r
  have hi:j.val+1<(curve q).length:=by have hj:j.val<(curve q).length-1:=j.isLt; omega
  have hs:=step_order _ _ _ (corner_line_endpoints_checked q j a).2
  have hl:=line_endpoint_coordinates q (j.val+1) hi a b false
  have hc:=corner_endpoint_coordinates q j.val a b true
  exact hc.symm ▸hl.symm ▸hs

end PushPuzzle.PushFS.Reduction.GateTileRouting
