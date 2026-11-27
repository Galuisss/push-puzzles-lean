/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.AnnulusRawFrames
public import PushFS.Reduction.AnnulusLineSignals
public import PushFS.Gadgets.Wires.ShortCorners.RotatedSignal
public import PushFS.Gadgets.Wires.Catalog.SignalJoins

/-! Literal static corridor witnesses for the real line/corner signal seams. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting

open Gadgets Gadgets.Wires Catalog Soundness Polyline
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def lineExitGhost (f : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool) :
    Cell (lineBase f n hn a b).width (lineBase f n hn a b).height :=
  (⟨n+(if f then 20 else 0)+2+a.toNat,by
    rw [(line_dimensions f n hn a b).1]
    have ha:a.toNat≤1:=by cases a <;> decide
    cases f <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega⟩,
    ⟨10,by rw [(line_dimensions f n hn a b).2]; decide⟩)

theorem line_exit_component (f : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool) :
    SameComponent (lineBase f n hn a b).board ((lineMatching f n hn a b).source (lineLast f n hn))
      (lineExitGhost f n hn a b) := by
  let B:=lineBase f n hn a b
  let y : Fin B.height:=⟨10,by rw [(line_dimensions f n hn a b).2]; decide⟩
  have hrow : ∀x : Fin B.width,(x,y)∉B.board.walls := by
    cases f
    · exact ChainGeometry.row_floor n hn
    · intro x
      change (x,10)∉(FlippedChain.atlas n hn (FlippedChain.uniform a) (FlippedChain.uniform b)).walls
      rw [FlippedChain.atlas_walls]
      exact FlippedChain.row_floor n hn x
  have hp:=line_last_position f n hn a b
  have ha:a.toNat≤1:=by cases a <;> decide
  have hs : ((lineMatching f n hn a b).source (lineLast f n hn)).2=y := Fin.ext hp.2
  have hsource : (lineMatching f n hn a b).source (lineLast f n hn)=
      (((lineMatching f n hn a b).source (lineLast f n hn)).1,y) := Prod.ext rfl hs
  rw [hsource]
  apply horizontal_component y hrow
  · rw [hp.1]
    change 0<n+(if f then 20 else 0)+a.toNat ∧n+(if f then 20 else 0)+a.toNat+1<(lineBase f n hn a b).width
    rw [(line_dimensions f n hn a b).1]
    cases f <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega
  · change 0<n+(if f then 20 else 0)+2+a.toNat ∧n+(if f then 20 else 0)+2+a.toNat+1<(lineBase f n hn a b).width
    rw [(line_dimensions f n hn a b).1]
    cases f <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega

def cornerExitGhost (k : ShortCorners.Kind) (a : Bool) : Cell (ShortCorners.width k) (ShortCorners.height k) :=
  (⟨10,by cases k <;> decide⟩,⟨ShortCorners.lastY k+2+a.toNat,by cases k <;> cases a <;> decide⟩)

private theorem corner_exit_checked : ∀(k : ShortCorners.Kind) (a : Bool),
    Gates.staticRun (ShortCorners.template k).wall ((ShortCorners.template k).position a (ShortCorners.last k))
      (Template.slotDirections ((ShortCorners.template k).position a (ShortCorners.last k)) (cornerExitGhost k a))=
      some (cornerExitGhost k a) ∧
    Gates.staticRun (ShortCorners.template k).wall (cornerExitGhost k a)
      (Template.slotDirections (cornerExitGhost k a) ((ShortCorners.template k).position a (ShortCorners.last k)))=
      some ((ShortCorners.template k).position a (ShortCorners.last k)) := by decide +kernel

theorem corner_exit_component (k : ShortCorners.Kind) (a b : Bool) :
    SameComponent (ShortCorners.puzzle k a b).board ((ShortCorners.slotMatching k a b).source (ShortCorners.last k))
      (cornerExitGhost k a) :=
  ⟨Gates.staticRun_sound ((ShortCorners.template k).wall_correct ((ShortCorners.template k).boxes b)) (corner_exit_checked k a).1,
    Gates.staticRun_sound ((ShortCorners.template k).wall_correct ((ShortCorners.template k).boxes b)) (corner_exit_checked k a).2⟩

def linePhasePoint (q : Key) (i : ℕ) (last : Bool) (a : Bool) : ℕ×ℕ :=
  let f:=fillerFlip q i
  let n:=fillerSpan q i
  let o:=lineOrientation (original q i).travel f
  let x:=if last then n+(if f then 20 else 0)+a.toNat else 2+a.toNat
  let p:=o.point (n+(if f then 25 else 5)) 21 (x,10)
  ((lineOffset q i).1+p.1,(lineOffset q i).2+p.2)

def cornerPhasePoint (q : Key) (i : ℕ) (last : Bool) (a : Bool) : ℕ×ℕ :=
  let k:=cornerKind q i
  let p:=if last then (10,ShortCorners.lastY k+a.toNat) else (ShortCorners.sourceX k-a.toNat,10)
  let p':=(cornerOrientation q i).point (ShortCorners.width k) (ShortCorners.height k) p
  ((cornerOffset q i).1+p'.1,(cornerOffset q i).2+p'.2)

def lineGhostPoint (q : Key) (i : ℕ) (a : Bool) : ℕ×ℕ :=
  let f:=fillerFlip q i
  let n:=fillerSpan q i
  let p:=(lineOrientation (original q i).travel f).point (n+(if f then 25 else 5)) 21
    (n+(if f then 20 else 0)+2+a.toNat,10)
  ((lineOffset q i).1+p.1,(lineOffset q i).2+p.2)

def cornerGhostPoint (q : Key) (i : ℕ) (a : Bool) : ℕ×ℕ :=
  let k:=cornerKind q i
  let p:=(cornerOrientation q i).point (ShortCorners.width k) (ShortCorners.height k) (10,ShortCorners.lastY k+2+a.toNat)
  ((cornerOffset q i).1+p.1,(cornerOffset q i).2+p.2)

/-- The actual last line label and next corner label have exactly their two-cell directional seam spacing. -/
theorem line_corner_endpoints_checked : ∀q : Key,∀i : Fin ((curve q).length-1),∀a : Bool,
    lineGhostPoint q i.val a=cornerPhasePoint q i.val false a ∧
      DirectionalStep (original q i.val).travel (linePhasePoint q i.val true a) (cornerPhasePoint q i.val false a) := by
  decide +kernel

/-- The real short-corner exit and the next complete chain meet at the exact same false-phase anchor. -/
theorem corner_line_endpoints_checked : ∀q : Key,∀i : Fin ((curve q).length-1),∀a : Bool,
    cornerGhostPoint q i.val a=linePhasePoint q (i.val+1) false a ∧
      DirectionalStep (original q (i.val+1)).travel (cornerPhasePoint q i.val true a) (linePhasePoint q (i.val+1) false a) := by
  decide +kernel

theorem line_endpoint_coordinates (q : Key) (i : ℕ) (hi : i<(curve q).length) (a b last : Bool) :
    let l:=if last then lineLast (fillerFlip q i) (fillerSpan q i) (filler_shape q i hi).2.1
      else lineFirst (fillerFlip q i) (fillerSpan q i) (filler_shape q i hi).2.1
    ((lineOffset q i).1+((lineSlotMatching q i hi a b).source l).1.val,
      (lineOffset q i).2+((lineSlotMatching q i hi a b).source l).2.val)=linePhasePoint q i last a := by
  dsimp only
  rw [line_source_coordinates,RectOrientation.coordinates_point]
  cases last
  · simp only [Bool.false_eq_true,ite_false]
    rw [(line_first_position _ _ _ a b).1,(line_first_position _ _ _ a b).2,
      (line_dimensions _ _ _ a b).1,(line_dimensions _ _ _ a b).2]
    rfl
  · simp only [ite_true]
    rw [(line_last_position _ _ _ a b).1,(line_last_position _ _ _ a b).2,
      (line_dimensions _ _ _ a b).1,(line_dimensions _ _ _ a b).2]
    rfl

theorem corner_endpoint_coordinates (q : Key) (i : ℕ) (a b last : Bool) :
    let k:=cornerKind q i
    let l:=if last then ShortCorners.last k else ShortCorners.first k
    ((cornerOffset q i).1+((cornerMatching q i a b).source l).1.val,
      (cornerOffset q i).2+((cornerMatching q i a b).source l).2.val)=cornerPhasePoint q i last a := by
  dsimp only
  rw [corner_source_coordinates,RectOrientation.coordinates_point]
  have hp:=ShortCorners.endpoints (cornerKind q i) a
  cases last
  · simp only [Bool.false_eq_true,ite_false]
    have hx : ((ShortCorners.template (cornerKind q i)).position a (ShortCorners.first (cornerKind q i))).1.val=
        ShortCorners.sourceX (cornerKind q i)-a.toNat := by omega
    rw [hx,hp.2.1]
    rfl
  · simp only [ite_true]
    rw [hp.2.2.1,hp.2.2.2]
    rfl

theorem line_ghost_coordinates (q : Key) (i : ℕ) (hi : i<(curve q).length) (a b : Bool) :
    ((lineOffset q i).1+((lineRawIso q i hi a b).cells
      (lineExitGhost (fillerFlip q i) (fillerSpan q i) (filler_shape q i hi).2.1 a b)).1.val,
      (lineOffset q i).2+((lineRawIso q i hi a b).cells
        (lineExitGhost (fillerFlip q i) (fillerSpan q i) (filler_shape q i hi).2.1 a b)).2.val)=lineGhostPoint q i a := by
  have he:=congrArg (fun p : ℕ×ℕ=>((lineOffset q i).1+p.1,(lineOffset q i).2+p.2))
    ((lineOrientation (original q i).travel (fillerFlip q i)).point_cells _ _
      (lineExitGhost (fillerFlip q i) (fillerSpan q i) (filler_shape q i hi).2.1 a b))
  apply he.symm.trans
  dsimp only [lineExitGhost]
  rw [(line_dimensions _ _ _ a b).1,(line_dimensions _ _ _ a b).2]
  rfl

theorem corner_ghost_coordinates (q : Key) (i : ℕ) (a : Bool) :
    ((cornerOffset q i).1+((cornerIso q i).geometry.cells (cornerExitGhost (cornerKind q i) a)).1.val,
      (cornerOffset q i).2+((cornerIso q i).geometry.cells (cornerExitGhost (cornerKind q i) a)).2.val)=
        cornerGhostPoint q i a :=
  (congrArg (fun p : ℕ×ℕ=>((cornerOffset q i).1+p.1,(cornerOffset q i).2+p.2))
    ((cornerOrientation q i).point_cells _ _ (cornerExitGhost (cornerKind q i) a))).symm

theorem corner_directions (q : Key) (i : ℕ) (hi : i+1<(curve q).length) :
    (cornerOrientation q i).direction .west=(original q i).travel ∧
      (cornerOrientation q i).direction .south=(original q (i+1)).travel :=
  RectOrientation.choose_correct _ _ (turn_perpendicular q i hi)

end PushPuzzle.PushFS.Reduction.GateTileRouting
