/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.AnnulusTravelSignals
public import PushFS.Reduction.AnnulusSeamComponents
public import PushFS.Gadgets.Wires.ShortCorners.TravelSignal

/-! Exact true-phase reference cells of the real full annular layout, with both shared-seam threshold steps. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting

open Inventory Gadgets.Wires Catalog
set_option maxRecDepth 65536
set_option maxHeartbeats 100000
attribute [local irreducible] curve original cornerKind cornerOrientation cornerIso lineOrientation

def lineReference (q : Key) (i : ℕ) (hi : i<(curve q).length) (a b last : Bool) : C :=
  (lineRect q i hi a b).cells ((lineRawIso q i hi a b).cells
    (lineThresholdCell (fillerFlip q i) (fillerSpan q i) (filler_shape q i hi).2.1 a b last))

def cornerReference (q : Key) (i : ℕ) (hi : i+1<(curve q).length) (last : Bool) : C :=
  (cornerRect q i hi).cells ((cornerIso q i).geometry.cells
    ((ShortCorners.template (cornerKind q i)).position true
      (if last then ShortCorners.last (cornerKind q i) else ShortCorners.first (cornerKind q i))))

theorem line_reference_coordinates (q : Key) (i : ℕ) (hi : i<(curve q).length) (a b last : Bool) :
    ((lineReference q i hi a b last).1.val,(lineReference q i hi a b last).2.val)=linePhasePoint q i last true := by
  let o:=lineOrientation (original q i).travel (fillerFlip q i)
  let f:=fillerFlip q i
  let n:=fillerSpan q i
  let hn:2301≤n:=(filler_shape q i hi).2.1
  have he:=congrArg (fun p : ℕ×ℕ=>((lineOffset q i).1+p.1,(lineOffset q i).2+p.2))
    (o.point_cells (lineBase f n hn a b).width (lineBase f n hn a b).height (lineThresholdCell f n hn a b last))
  apply he.symm.trans
  dsimp only [lineThresholdCell]
  rw [(line_dimensions f n hn a b).1,(line_dimensions f n hn a b).2]
  have hx : (if last then n+(if f then 21 else 1) else 3)=
      (if last then n+(if f then 20 else 0)+Bool.toNat true else 2+Bool.toNat true) := by
    cases last <;> cases f <;> rfl
  rw [hx]
  rfl

private theorem corner_reference_coordinates (q : Key) (i : ℕ) (hi : i+1<(curve q).length)
    (last : Bool) :
    ((cornerReference q i hi last).1.val,(cornerReference q i hi last).2.val)=cornerPhasePoint q i last true := by
  exact corner_endpoint_coordinates q i true true last

theorem line_corner_reference_step (g : GateTileState) (r : Fin 3) (j : Fin ((curve (key g r)).length-1)) :
    DirectionalStep (original (key g r) j.val).travel
      ((lineReference (key g r) j.val (by have:=j.isLt; omega) (initialPhase g r) (targetPhase g r) true).1.val,
        (lineReference (key g r) j.val (by have:=j.isLt; omega) (initialPhase g r) (targetPhase g r) true).2.val)
      ((cornerReference (key g r) j.val (by have:=j.isLt; omega) false).1.val,
        (cornerReference (key g r) j.val (by have:=j.isLt; omega) false).2.val) := by
  have hl:=line_reference_coordinates (key g r) j.val (by have:=j.isLt; omega) (initialPhase g r) (targetPhase g r) true
  have hc:=corner_reference_coordinates (key g r) j.val (by have:=j.isLt; omega) false
  exact hl.symm ▸hc.symm ▸(line_corner_endpoints_checked (key g r) j true).2

theorem corner_line_reference_step (g : GateTileState) (r : Fin 3) (j : Fin ((curve (key g r)).length-1)) :
    DirectionalStep (original (key g r) (j.val+1)).travel
      ((cornerReference (key g r) j.val (by have:=j.isLt; omega) true).1.val,
        (cornerReference (key g r) j.val (by have:=j.isLt; omega) true).2.val)
      ((lineReference (key g r) (j.val+1) (by have:=j.isLt; omega) (initialPhase g r) (targetPhase g r) false).1.val,
        (lineReference (key g r) (j.val+1) (by have:=j.isLt; omega) (initialPhase g r) (targetPhase g r) false).2.val) := by
  have hl:=line_reference_coordinates (key g r) (j.val+1) (by have:=j.isLt; omega) (initialPhase g r) (targetPhase g r) false
  have hc:=corner_reference_coordinates (key g r) j.val (by have:=j.isLt; omega) true
  exact hc.symm ▸hl.symm ▸(corner_line_endpoints_checked (key g r) j true).2

end PushPuzzle.PushFS.Reduction.GateTileRouting
