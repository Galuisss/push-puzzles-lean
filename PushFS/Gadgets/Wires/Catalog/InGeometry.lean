/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.OutGeometry

/-! Actual mixed L with the terminal-flipped incoming arm reflected on both axes. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog.In


abbrev C (m n : ℕ) := Cell (m+63) (n+44)
abbrev Phases := Polyline.L.Phases

def inIso (m : ℕ) := (GridIsometry.reflectY (m+25) 21).trans (GridIsometry.reflectX (m+25) 21)
def outIso (n : ℕ) := GridIsometry.clockwise (n+5) 21

def inRect (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) := Polyline.L.inRect (m+20) n (by omega) hn
def turnRect (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) := Polyline.L.turnRect (m+20) n (by omega) hn
def outRect (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) := Polyline.L.outRect (m+20) n (by omega) hn

def inEmbed (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) := (inIso m).embedding.trans (inRect m n hm hn)
def outEmbed (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) := (outIso n).embedding.trans (outRect m n hm hn)

@[simp] theorem in_x (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (p : FlippedChain.C m) :
    ((inEmbed m n hm hn).cells p).1.val=38+(m+24-p.1.val) := by
  change 38+((inIso m).cells p).1.val=_
  simp [inIso,GridIsometry.trans,GridIsometry.reflectY,GridIsometry.transpose,GridIsometry.reflectX,Fin.revPerm,Fin.rev]
@[simp] theorem in_y (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (p : FlippedChain.C m) :
    ((inEmbed m n hm hn).cells p).2.val=20-p.2.val := by
  change 0+((inIso m).cells p).2.val=_
  simp [inIso,GridIsometry.trans,GridIsometry.reflectY,GridIsometry.transpose,GridIsometry.reflectX,Fin.revPerm,Fin.rev]
@[simp] theorem out_x (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (p : Chain.C n) :
    ((outEmbed m n hm hn).cells p).1.val=20-p.2.val := Polyline.L.out_x (m+20) n (by omega) hn p
@[simp] theorem out_y (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (p : Chain.C n) :
    ((outEmbed m n hm hn).cells p).2.val=39+p.1.val := rfl
@[simp] theorem turn_x (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (p : Turn.C) :
    ((turnRect m n hm hn).cells p).1.val=p.1.val := Polyline.L.turn_x (m+20) n (by omega) hn p
@[simp] theorem turn_y (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (p : Turn.C) :
    ((turnRect m n hm hn).cells p).2.val=1+p.2.val := rfl

/-- The terminal flip's full last seven columns really carry its north wall before reflection. -/
private theorem flipped_right7 (m : ℕ) (hm : 2301≤m) (p : FlippedChain.C m) (hp : m+18≤p.1.val) :
    p∈FlippedChain.walls m hm ↔p.2.val=8 ∨p.2.val=9 := by
  let q : Flip.C := (⟨p.1.val-m,by have := p.1.isLt; omega⟩,p.2)
  have he : (FlippedChain.flipPlacement m).cells q=p := by
    apply Prod.ext <;> apply Fin.ext
    · change m+(p.1.val-m)=p.1.val
      omega
    · exact FlippedChain.flip_y m q
  rw [←he,FlippedChain.flip_y]
  have hw : q∈Flip.template.walls ↔q.2.val=8 ∨q.2.val=9 := by
    have check : ∀q : Flip.C, 18≤q.1.val → Flip.wallTest q=decide (q.2.val=8 ∨q.2.val=9) := by decide +kernel
    rw [Template.mem_walls]
    change Flip.wallTest q=true↔_
    rw [check q (by change 18≤p.1.val-m; omega),decide_eq_true_eq]
  exact (FlippedChain.flip_walls m hm ∅ q).trans hw

theorem in_turn_walls (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (p : FlippedChain.C m) (q : Turn.C)
    (he : (inEmbed m n hm hn).cells p=(turnRect m n hm hn).cells q) :
    p∈FlippedChain.walls m hm ↔q∈Turn.template.walls := by
  have hx:=congrArg (fun p : C m n=>p.1.val) he
  have hy:=congrArg (fun p : C m n=>p.2.val) he
  simp only [in_x,turn_x] at hx
  simp only [in_y,turn_y] at hy
  have hp:=p.1.isLt
  have hpy:=p.2.isLt
  have hq:=q.1.isLt
  rw [flipped_right7 m hm p (by omega),Polyline.turn_east7 q (by omega)]
  omega

theorem turn_out_walls (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (p : Turn.C) (q : Chain.C n)
    (he : (turnRect m n hm hn).cells p=(outEmbed m n hm hn).cells q) :
    p∈Turn.template.walls ↔q∈Chain.walls n hn := Polyline.L.turn_out_walls (m+20) n (by omega) hn p q he

theorem in_out_disjoint (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (p : FlippedChain.C m) (q : Chain.C n) :
    (inEmbed m n hm hn).cells p≠(outEmbed m n hm hn).cells q := by
  intro he
  have hx:=congrArg (fun p : C m n=>p.1.val) he
  simp only [in_x,out_x] at hx
  omega

end PushPuzzle.PushFS.Gadgets.Wires.Catalog.In
