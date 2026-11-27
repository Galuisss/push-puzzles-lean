/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.ImageSignals
public import PushFS.Gadgets.Wires.Catalog.OutRails
public import PushFS.Gadgets.Wires.Catalog.InRails
public import PushFS.Gadgets.Wires.Polyline.LRails

/-! Every complete natural or corrected long L transmits its actual endpoint signal in any successful ambient board. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog

open Soundness Polyline
set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

private theorem turn_endpoints (phase : Bool) :
    (Turn.template.position phase 0).1.val+phase.toNat=40 ∧ (Turn.template.position phase 0).2.val=9 ∧
    (Turn.template.position phase 28).1.val=10 ∧ (Turn.template.position phase 28).2.val=38+phase.toNat ∧
    (Turn.template.position phase 14).1.val=10 ∧ (Turn.template.position phase 14).2.val=10+phase.toNat := by
  cases phase <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

namespace NormalRelay
variable {I : Instance} {L : Type} [Fintype L] {M : SlotMatching I L}
    {m n : ℕ} {hm : 2301≤m} {hn : 2301≤n} {a b : Bool}

def first (hm : 2301≤m) : Polyline.L.Label m n := ⟨0,ChainEnds.first m hm⟩
def inSeam (hm : 2301≤m) : Polyline.L.Label m n := ⟨0,ChainEnds.last m hm⟩
def outSeam (hn : 2301≤n) : Polyline.L.Label m n := ⟨2,ChainEnds.first n hn⟩
def last (hn : 2301≤n) : Polyline.L.Label m n := ⟨2,ChainEnds.last n hn⟩

def incoming (g : StorageImage M (Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).slotMatching) :
    StorageImage M ((Chain.slotMatching m hm a b).reorient (GridIsometry.reflectX (m+5) 21)) := g.comp (pieceImage (Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)) 0)
def turning (g : StorageImage M (Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).slotMatching) :
    StorageImage M (Turn.checked.slotMatching a b) := g.comp (pieceImage (Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)) 1)
def outgoing (g : StorageImage M (Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).slotMatching) :
    StorageImage M (((Chain.slotMatching n hn a b).reorient (GridIsometry.transpose (n+5) 21)).reorient (GridIsometry.reflectX 21 (n+5))) := g.comp (pieceImage (Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)) 2)

private theorem seam_coordinates :
    ((Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).source (inSeam (m:=m) hm)).1.val+a.toNat=42 ∧
    ((Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).source (inSeam (m:=m) hm)).2.val=10 ∧
    ((Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).source (outSeam (n:=n) hn)).1.val=10 ∧
    ((Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).source (outSeam (n:=n) hn)).2.val=41+a.toNat := by
  have ha : a.toNat≤1 := by cases a <;> decide
  constructor
  · change ((Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).source ⟨0,ChainEnds.last m hm⟩).1.val+a.toNat=42
    rw [Polyline.L.source0 m n hm hn _ _ _,Polyline.L.in_x]
    dsimp only [Polyline.L.uniform]
    rw [ChainEnds.last_x]
    omega
  constructor
  · change ((Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).source ⟨0,ChainEnds.last m hm⟩).2.val=10
    rw [Polyline.L.source0 m n hm hn _ _ _,Polyline.L.in_y,Chain.position_row]
  constructor
  · change ((Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).source ⟨2,ChainEnds.first n hn⟩).1.val=10
    rw [Polyline.L.source2 m n hm hn _ _ _,Polyline.L.out_x,Chain.position_row]
  · change ((Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).source ⟨2,ChainEnds.first n hn⟩).2.val=41+a.toNat
    rw [Polyline.L.source2 m n hm hn _ _ _,Polyline.L.out_y]
    dsimp only [Polyline.L.uniform]
    rw [ChainEnds.first_x]
    omega

private theorem turn_coordinates (i : Fin 29) :
    (Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).source ⟨1,i⟩=(Polyline.L.turnRect m n hm hn).cells (Turn.template.position a i) :=
  Polyline.L.source1 m n hm hn _ _ i

private theorem horizontal_seam (g : StorageImage M (Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).slotMatching) :
    component I.board (M.source (g.labels (inSeam (m:=m) hm)))=
      component I.board (M.source ((turning g).turnGlyph.horizontalRail.anchor)) := by
  change component I.board (M.source (g.labels (inSeam (m:=m) hm)))=
    component I.board (M.source (g.labels ⟨1,(0 : Fin 29)⟩))
  apply g.source_component
  change SameComponent (Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).puzzle.board ((Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).source (inSeam (m:=m) hm)) ((Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).source ⟨1,(0 : Fin 29)⟩)
  have hc:=seam_coordinates (m:=m) (n:=n) (hm:=hm) (hn:=hn) (a:=a) (b:=b)
  have ht:=turn_endpoints a
  have ha : a.toNat≤1 := by cases a <;> decide
  apply Polyline.L.horizontal_component m n hm hn a b
  · exact ⟨hc.2.1,by omega,by omega⟩
  · rw [turn_coordinates]
    simp only [Polyline.L.turn_x,Polyline.L.turn_y]
    exact ⟨by omega,by omega,by omega⟩

private theorem vertical_seam (g : StorageImage M (Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).slotMatching) :
    component I.board (M.source (g.labels (outSeam (n:=n) hn)))=
      component I.board (M.source ((turning g).turnGlyph.verticalRail.anchor)) := by
  change component I.board (M.source (g.labels (outSeam (n:=n) hn)))=
    component I.board (M.source (g.labels ⟨1,(14 : Fin 29)⟩))
  apply g.source_component
  change SameComponent (Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).puzzle.board ((Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).source (outSeam (n:=n) hn)) ((Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).source ⟨1,(14 : Fin 29)⟩)
  have hc:=seam_coordinates (m:=m) (n:=n) (hm:=hm) (hn:=hn) (a:=a) (b:=b)
  have ht:=turn_endpoints a
  have ha : a.toNat≤1 := by cases a <;> decide
  apply Polyline.L.vertical_component m n hm hn a b
  · exact ⟨hc.2.2.1,by omega,by omega⟩
  · rw [turn_coordinates]
    simp only [Polyline.L.turn_x,Polyline.L.turn_y]
    exact ⟨by omega,by omega,by omega⟩

/-- The complete literal three-piece storage chart transmits in any actual successful ambient trajectory. -/
theorem signal (g : StorageImage M (Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).slotMatching) {S T : LabelledState L I.width I.height}
    (h : Successful M S T) (cert : Certificate I) (ho : M.Ordered)
    (hin : (S.position (g.labels (first (m:=m) hm))).1.val≤g.dx+m+39) :
    g.dy+n+40≤(S.position (g.labels (last (n:=n) hn))).2.val := by
  have hi:=(incoming g).west_chain h cert ho (by
    change (S.position (g.labels (first (m:=m) hm))).1.val≤g.dx+38+m+1
    omega)
  have hc:=seam_coordinates (m:=m) (n:=n) (hm:=hm) (hn:=hn) (a:=a) (b:=b)
  have ht:=turn_endpoints a
  have hgH : (S.position ((turning g).labels 0)).1.val+2≤(S.position (g.labels (inSeam (m:=m) hm))).1.val := by
    apply (turning g).turnGlyph.horizontalRail.gap h cert _ _ rfl (horizontal_seam g)
    change (M.source (g.labels ⟨1,(0 : Fin 29)⟩)).1.val<(M.source (g.labels (inSeam (m:=m) hm))).1.val
    rw [g.sources,g.sources]
    change g.dx+((Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).source ⟨1,(0 : Fin 29)⟩).1.val<g.dx+((Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).source (inSeam (m:=m) hm)).1.val
    rw [turn_coordinates]
    simp only [Polyline.L.turn_x]
    omega
  have hturn : (S.position ((turning g).labels 0)).1.val≤(turning g).turnGlyph.dx+39 := by
    change (S.position (g.labels (inSeam (m:=m) hm))).1.val≤g.dx+38+3 at hi
    change (S.position ((turning g).labels 0)).1.val≤g.dx+0+39
    omega
  have hout:=(turning g).turnGlyph.signal h cert ho hturn
  have hgV : (S.position ((turning g).labels 28)).2.val+2≤(S.position (g.labels (outSeam (n:=n) hn))).2.val := by
    apply (turning g).turnGlyph.verticalRail.gap h cert _ _
      ((turning g).turnGlyph.vertical_component 28 (by decide)) (vertical_seam g)
    change (M.source (g.labels ⟨1,(28 : Fin 29)⟩)).2.val<(M.source (g.labels (outSeam (n:=n) hn))).2.val
    rw [g.sources,g.sources]
    change g.dy+((Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).source ⟨1,(28 : Fin 29)⟩).2.val<g.dy+((Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).source (outSeam (n:=n) hn)).2.val
    rw [turn_coordinates]
    simp only [Polyline.L.turn_y]
    omega
  have hinOut : (outgoing g).dy+3≤(S.position ((outgoing g).labels (ChainEnds.first n hn))).2.val := by
    change g.dy+1+39≤(S.position ((turning g).labels 28)).2.val at hout
    change g.dy+39+3≤(S.position (g.labels (outSeam (n:=n) hn))).2.val
    omega
  have hh:=(outgoing g).south_chain h cert ho hinOut
  change g.dy+39+n+1≤(S.position (g.labels (last (n:=n) hn))).2.val at hh
  omega

end NormalRelay
namespace OutRelay
variable {I : Instance} {L : Type} [Fintype L] {M : SlotMatching I L}
    {m n : ℕ} {hm : 2301≤m} {hn : 2301≤n} {a b : Bool}

def first (hm : 2301≤m) : Out.Label m n := ⟨0,ChainEnds.first m hm⟩
def inSeam (hm : 2301≤m) : Out.Label m n := ⟨0,ChainEnds.last m hm⟩
def outSeam (hn : 2301≤n) : Out.Label m n := ⟨2,FlippedChain.firstLabel n hn⟩
def last (_hn : 2301≤n) : Out.Label m n := ⟨2,FlippedChain.lastLabel n⟩

def incoming (g : StorageImage M (Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).slotMatching) :
    StorageImage M ((Chain.slotMatching m hm a b).reorient (GridIsometry.reflectX (m+5) 21)) := g.comp (pieceImage (Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)) 0)
def turning (g : StorageImage M (Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).slotMatching) :
    StorageImage M (Turn.checked.slotMatching a b) := g.comp (pieceImage (Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)) 1)
def outgoing (g : StorageImage M (Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).slotMatching) :
    StorageImage M (((FlippedChain.slotMatching n hn a b).reorient (GridIsometry.transpose (n+25) 21)).reorient (GridIsometry.reflectX 21 (n+25))) := g.comp (pieceImage (Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)) 2)

private theorem seam_coordinates :
    ((Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).source (inSeam (m:=m) hm)).1.val+a.toNat=42 ∧
    ((Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).source (inSeam (m:=m) hm)).2.val=10 ∧
    ((Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).source (outSeam (n:=n) hn)).1.val=10 ∧
    ((Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).source (outSeam (n:=n) hn)).2.val=41+a.toNat := by
  have ha : a.toNat≤1 := by cases a <;> decide
  constructor
  · change ((Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).source ⟨0,ChainEnds.last m hm⟩).1.val+a.toNat=42
    rw [Out.source0 m n hm hn _ _ _,Out.in_x]
    dsimp only [Out.uniform]
    rw [ChainEnds.last_x]
    omega
  constructor
  · change ((Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).source ⟨0,ChainEnds.last m hm⟩).2.val=10
    rw [Out.source0 m n hm hn _ _ _,Out.in_y,Chain.position_row]
  constructor
  · change ((Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).source ⟨2,FlippedChain.firstLabel n hn⟩).1.val=10
    rw [Out.source2 m n hm hn _ _ _,Out.out_x,FlippedChain.position_row]
  · change ((Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).source ⟨2,FlippedChain.firstLabel n hn⟩).2.val=41+a.toNat
    rw [Out.source2 m n hm hn _ _ _,Out.out_y]
    dsimp only [Out.uniform]
    rw [(FlippedChain.endpoints n hn a).1]
    omega

private theorem turn_coordinates (i : Fin 29) :
    (Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).source ⟨1,i⟩=(Out.turnRect m n hm hn).cells (Turn.template.position a i) :=
  Out.source1 m n hm hn _ _ i

private theorem horizontal_seam (g : StorageImage M (Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).slotMatching) :
    component I.board (M.source (g.labels (inSeam (m:=m) hm)))=
      component I.board (M.source ((turning g).turnGlyph.horizontalRail.anchor)) := by
  change component I.board (M.source (g.labels (inSeam (m:=m) hm)))=
    component I.board (M.source (g.labels ⟨1,(0 : Fin 29)⟩))
  apply g.source_component
  change SameComponent (Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).puzzle.board ((Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).source (inSeam (m:=m) hm)) ((Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).source ⟨1,(0 : Fin 29)⟩)
  have hc:=seam_coordinates (m:=m) (n:=n) (hm:=hm) (hn:=hn) (a:=a) (b:=b)
  have ht:=turn_endpoints a
  have ha : a.toNat≤1 := by cases a <;> decide
  apply Out.horizontal_component m n hm hn a b
  · exact ⟨hc.2.1,by omega,by omega⟩
  · rw [turn_coordinates]
    simp only [Out.turn_x,Out.turn_y]
    exact ⟨by omega,by omega,by omega⟩

private theorem vertical_seam (g : StorageImage M (Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).slotMatching) :
    component I.board (M.source (g.labels (outSeam (n:=n) hn)))=
      component I.board (M.source ((turning g).turnGlyph.verticalRail.anchor)) := by
  change component I.board (M.source (g.labels (outSeam (n:=n) hn)))=
    component I.board (M.source (g.labels ⟨1,(14 : Fin 29)⟩))
  apply g.source_component
  change SameComponent (Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).puzzle.board ((Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).source (outSeam (n:=n) hn)) ((Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).source ⟨1,(14 : Fin 29)⟩)
  have hc:=seam_coordinates (m:=m) (n:=n) (hm:=hm) (hn:=hn) (a:=a) (b:=b)
  have ht:=turn_endpoints a
  have ha : a.toNat≤1 := by cases a <;> decide
  apply Out.vertical_component m n hm hn a b
  · exact ⟨hc.2.2.1,by omega,by omega⟩
  · rw [turn_coordinates]
    simp only [Out.turn_x,Out.turn_y]
    exact ⟨by omega,by omega,by omega⟩

/-- The complete literal three-piece storage chart transmits in any actual successful ambient trajectory. -/
theorem signal (g : StorageImage M (Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).slotMatching) {S T : LabelledState L I.width I.height}
    (h : Successful M S T) (cert : Certificate I) (ho : M.Ordered)
    (hin : (S.position (g.labels (first (m:=m) hm))).1.val≤g.dx+m+39) :
    g.dy+n+60≤(S.position (g.labels (last (n:=n) hn))).2.val := by
  have hi:=(incoming g).west_chain h cert ho (by
    change (S.position (g.labels (first (m:=m) hm))).1.val≤g.dx+38+m+1
    omega)
  have hc:=seam_coordinates (m:=m) (n:=n) (hm:=hm) (hn:=hn) (a:=a) (b:=b)
  have ht:=turn_endpoints a
  have hgH : (S.position ((turning g).labels 0)).1.val+2≤(S.position (g.labels (inSeam (m:=m) hm))).1.val := by
    apply (turning g).turnGlyph.horizontalRail.gap h cert _ _ rfl (horizontal_seam g)
    change (M.source (g.labels ⟨1,(0 : Fin 29)⟩)).1.val<(M.source (g.labels (inSeam (m:=m) hm))).1.val
    rw [g.sources,g.sources]
    change g.dx+((Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).source ⟨1,(0 : Fin 29)⟩).1.val<g.dx+((Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).source (inSeam (m:=m) hm)).1.val
    rw [turn_coordinates]
    simp only [Out.turn_x]
    omega
  have hturn : (S.position ((turning g).labels 0)).1.val≤(turning g).turnGlyph.dx+39 := by
    change (S.position (g.labels (inSeam (m:=m) hm))).1.val≤g.dx+38+3 at hi
    change (S.position ((turning g).labels 0)).1.val≤g.dx+0+39
    omega
  have hout:=(turning g).turnGlyph.signal h cert ho hturn
  have hgV : (S.position ((turning g).labels 28)).2.val+2≤(S.position (g.labels (outSeam (n:=n) hn))).2.val := by
    apply (turning g).turnGlyph.verticalRail.gap h cert _ _
      ((turning g).turnGlyph.vertical_component 28 (by decide)) (vertical_seam g)
    change (M.source (g.labels ⟨1,(28 : Fin 29)⟩)).2.val<(M.source (g.labels (outSeam (n:=n) hn))).2.val
    rw [g.sources,g.sources]
    change g.dy+((Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).source ⟨1,(28 : Fin 29)⟩).2.val<g.dy+((Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).source (outSeam (n:=n) hn)).2.val
    rw [turn_coordinates]
    simp only [Out.turn_y]
    omega
  have hinOut : (outgoing g).dy+3≤(S.position ((outgoing g).labels (FlippedChain.firstLabel n hn))).2.val := by
    change g.dy+1+39≤(S.position ((turning g).labels 28)).2.val at hout
    change g.dy+39+3≤(S.position (g.labels (outSeam (n:=n) hn))).2.val
    omega
  have hh:=(outgoing g).south_flipped h cert ho hinOut
  change g.dy+39+n+21≤(S.position (g.labels (last (n:=n) hn))).2.val at hh
  omega

end OutRelay
namespace InRelay
variable {I : Instance} {L : Type} [Fintype L] {M : SlotMatching I L}
    {m n : ℕ} {hm : 2301≤m} {hn : 2301≤n} {a b : Bool}

def first (hm : 2301≤m) : In.Label m n := ⟨0,FlippedChain.firstLabel m hm⟩
def inSeam (_hm : 2301≤m) : In.Label m n := ⟨0,FlippedChain.lastLabel m⟩
def outSeam (hn : 2301≤n) : In.Label m n := ⟨2,ChainEnds.first n hn⟩
def last (hn : 2301≤n) : In.Label m n := ⟨2,ChainEnds.last n hn⟩

def incoming (g : StorageImage M (In.atlas m n hm hn (In.uniform a) (In.uniform b)).slotMatching) :
    StorageImage M ((((((FlippedChain.slotMatching m hm a b).reorient (GridIsometry.transpose (m+25) 21)).reorient (GridIsometry.reflectX 21 (m+25))).reorient (GridIsometry.transpose 21 (m+25))).reorient (GridIsometry.reflectX (m+25) 21))) := g.comp (pieceImage (In.atlas m n hm hn (In.uniform a) (In.uniform b)) 0)
def turning (g : StorageImage M (In.atlas m n hm hn (In.uniform a) (In.uniform b)).slotMatching) :
    StorageImage M (Turn.checked.slotMatching a b) := g.comp (pieceImage (In.atlas m n hm hn (In.uniform a) (In.uniform b)) 1)
def outgoing (g : StorageImage M (In.atlas m n hm hn (In.uniform a) (In.uniform b)).slotMatching) :
    StorageImage M (((Chain.slotMatching n hn a b).reorient (GridIsometry.transpose (n+5) 21)).reorient (GridIsometry.reflectX 21 (n+5))) := g.comp (pieceImage (In.atlas m n hm hn (In.uniform a) (In.uniform b)) 2)

private theorem seam_coordinates :
    ((In.atlas m n hm hn (In.uniform a) (In.uniform b)).source (inSeam (m:=m) hm)).1.val+a.toNat=42 ∧
    ((In.atlas m n hm hn (In.uniform a) (In.uniform b)).source (inSeam (m:=m) hm)).2.val=10 ∧
    ((In.atlas m n hm hn (In.uniform a) (In.uniform b)).source (outSeam (n:=n) hn)).1.val=10 ∧
    ((In.atlas m n hm hn (In.uniform a) (In.uniform b)).source (outSeam (n:=n) hn)).2.val=41+a.toNat := by
  have ha : a.toNat≤1 := by cases a <;> decide
  constructor
  · change ((In.atlas m n hm hn (In.uniform a) (In.uniform b)).source ⟨0,FlippedChain.lastLabel m⟩).1.val+a.toNat=42
    rw [In.source0 m n hm hn _ _ _,In.in_x]
    dsimp only [In.uniform]
    rw [(FlippedChain.endpoints m hm a).2]
    omega
  constructor
  · change ((In.atlas m n hm hn (In.uniform a) (In.uniform b)).source ⟨0,FlippedChain.lastLabel m⟩).2.val=10
    rw [In.source0 m n hm hn _ _ _,In.in_y,FlippedChain.position_row]
  constructor
  · change ((In.atlas m n hm hn (In.uniform a) (In.uniform b)).source ⟨2,ChainEnds.first n hn⟩).1.val=10
    rw [In.source2 m n hm hn _ _ _,In.out_x,Chain.position_row]
  · change ((In.atlas m n hm hn (In.uniform a) (In.uniform b)).source ⟨2,ChainEnds.first n hn⟩).2.val=41+a.toNat
    rw [In.source2 m n hm hn _ _ _,In.out_y]
    dsimp only [In.uniform]
    rw [ChainEnds.first_x]
    omega

private theorem turn_coordinates (i : Fin 29) :
    (In.atlas m n hm hn (In.uniform a) (In.uniform b)).source ⟨1,i⟩=(In.turnRect m n hm hn).cells (Turn.template.position a i) :=
  In.source1 m n hm hn _ _ i

private theorem horizontal_seam (g : StorageImage M (In.atlas m n hm hn (In.uniform a) (In.uniform b)).slotMatching) :
    component I.board (M.source (g.labels (inSeam (m:=m) hm)))=
      component I.board (M.source ((turning g).turnGlyph.horizontalRail.anchor)) := by
  change component I.board (M.source (g.labels (inSeam (m:=m) hm)))=
    component I.board (M.source (g.labels ⟨1,(0 : Fin 29)⟩))
  apply g.source_component
  change SameComponent (In.atlas m n hm hn (In.uniform a) (In.uniform b)).puzzle.board ((In.atlas m n hm hn (In.uniform a) (In.uniform b)).source (inSeam (m:=m) hm)) ((In.atlas m n hm hn (In.uniform a) (In.uniform b)).source ⟨1,(0 : Fin 29)⟩)
  have hc:=seam_coordinates (m:=m) (n:=n) (hm:=hm) (hn:=hn) (a:=a) (b:=b)
  have ht:=turn_endpoints a
  have ha : a.toNat≤1 := by cases a <;> decide
  apply In.horizontal_component m n hm hn a b
  · exact ⟨hc.2.1,by omega,by omega⟩
  · rw [turn_coordinates]
    simp only [In.turn_x,In.turn_y]
    exact ⟨by omega,by omega,by omega⟩

private theorem vertical_seam (g : StorageImage M (In.atlas m n hm hn (In.uniform a) (In.uniform b)).slotMatching) :
    component I.board (M.source (g.labels (outSeam (n:=n) hn)))=
      component I.board (M.source ((turning g).turnGlyph.verticalRail.anchor)) := by
  change component I.board (M.source (g.labels (outSeam (n:=n) hn)))=
    component I.board (M.source (g.labels ⟨1,(14 : Fin 29)⟩))
  apply g.source_component
  change SameComponent (In.atlas m n hm hn (In.uniform a) (In.uniform b)).puzzle.board ((In.atlas m n hm hn (In.uniform a) (In.uniform b)).source (outSeam (n:=n) hn)) ((In.atlas m n hm hn (In.uniform a) (In.uniform b)).source ⟨1,(14 : Fin 29)⟩)
  have hc:=seam_coordinates (m:=m) (n:=n) (hm:=hm) (hn:=hn) (a:=a) (b:=b)
  have ht:=turn_endpoints a
  have ha : a.toNat≤1 := by cases a <;> decide
  apply In.vertical_component m n hm hn a b
  · exact ⟨hc.2.2.1,by omega,by omega⟩
  · rw [turn_coordinates]
    simp only [In.turn_x,In.turn_y]
    exact ⟨by omega,by omega,by omega⟩

/-- The complete literal three-piece storage chart transmits in any actual successful ambient trajectory. -/
theorem signal (g : StorageImage M (In.atlas m n hm hn (In.uniform a) (In.uniform b)).slotMatching) {S T : LabelledState L I.width I.height}
    (h : Successful M S T) (cert : Certificate I) (ho : M.Ordered)
    (hin : (S.position (g.labels (first (m:=m) hm))).1.val≤g.dx+m+59) :
    g.dy+n+40≤(S.position (g.labels (last (n:=n) hn))).2.val := by
  have hi:=(incoming g).west_flipped h cert ho (by
    change (S.position (g.labels (first (m:=m) hm))).1.val≤g.dx+38+m+21
    omega)
  have hc:=seam_coordinates (m:=m) (n:=n) (hm:=hm) (hn:=hn) (a:=a) (b:=b)
  have ht:=turn_endpoints a
  have hgH : (S.position ((turning g).labels 0)).1.val+2≤(S.position (g.labels (inSeam (m:=m) hm))).1.val := by
    apply (turning g).turnGlyph.horizontalRail.gap h cert _ _ rfl (horizontal_seam g)
    change (M.source (g.labels ⟨1,(0 : Fin 29)⟩)).1.val<(M.source (g.labels (inSeam (m:=m) hm))).1.val
    rw [g.sources,g.sources]
    change g.dx+((In.atlas m n hm hn (In.uniform a) (In.uniform b)).source ⟨1,(0 : Fin 29)⟩).1.val<g.dx+((In.atlas m n hm hn (In.uniform a) (In.uniform b)).source (inSeam (m:=m) hm)).1.val
    rw [turn_coordinates]
    simp only [In.turn_x]
    omega
  have hturn : (S.position ((turning g).labels 0)).1.val≤(turning g).turnGlyph.dx+39 := by
    change (S.position (g.labels (inSeam (m:=m) hm))).1.val≤g.dx+38+3 at hi
    change (S.position ((turning g).labels 0)).1.val≤g.dx+0+39
    omega
  have hout:=(turning g).turnGlyph.signal h cert ho hturn
  have hgV : (S.position ((turning g).labels 28)).2.val+2≤(S.position (g.labels (outSeam (n:=n) hn))).2.val := by
    apply (turning g).turnGlyph.verticalRail.gap h cert _ _
      ((turning g).turnGlyph.vertical_component 28 (by decide)) (vertical_seam g)
    change (M.source (g.labels ⟨1,(28 : Fin 29)⟩)).2.val<(M.source (g.labels (outSeam (n:=n) hn))).2.val
    rw [g.sources,g.sources]
    change g.dy+((In.atlas m n hm hn (In.uniform a) (In.uniform b)).source ⟨1,(28 : Fin 29)⟩).2.val<g.dy+((In.atlas m n hm hn (In.uniform a) (In.uniform b)).source (outSeam (n:=n) hn)).2.val
    rw [turn_coordinates]
    simp only [In.turn_y]
    omega
  have hinOut : (outgoing g).dy+3≤(S.position ((outgoing g).labels (ChainEnds.first n hn))).2.val := by
    change g.dy+1+39≤(S.position ((turning g).labels 28)).2.val at hout
    change g.dy+39+3≤(S.position (g.labels (outSeam (n:=n) hn))).2.val
    omega
  have hh:=(outgoing g).south_chain h cert ho hinOut
  change g.dy+39+n+1≤(S.position (g.labels (last (n:=n) hn))).2.val at hh
  omega

end InRelay

end PushPuzzle.PushFS.Gadgets.Wires.Catalog
