/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Polyline.L
public import PushFS.Gadgets.Wires.FlippedChain

/-! Actual mixed L with the terminal flip in its clockwise outgoing arm. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog.Out


abbrev C (m n : ℕ) := Cell (m+43) (n+64)
abbrev Phases := Polyline.L.Phases

def inIso (m : ℕ) := GridIsometry.reflectX (m+5) 21
def outIso (n : ℕ) := GridIsometry.clockwise (n+25) 21

def inRect (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) := Polyline.L.inRect m (n+20) hm (by omega)
def turnRect (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) := Polyline.L.turnRect m (n+20) hm (by omega)
def outRect (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) := Polyline.L.outRect m (n+20) hm (by omega)
def inEmbed (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) := (inIso m).embedding.trans (inRect m n hm hn)
def outEmbed (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) := (outIso n).embedding.trans (outRect m n hm hn)

@[simp] theorem in_x (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (p : Chain.C m) :
    ((inEmbed m n hm hn).cells p).1.val=38+(m+4-p.1.val) := Polyline.L.in_x m (n+20) hm (by omega) p
@[simp] theorem in_y (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (p : Chain.C m) :
    ((inEmbed m n hm hn).cells p).2.val=p.2.val := Polyline.L.in_y m (n+20) hm (by omega) p
@[simp] theorem out_x (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (p : FlippedChain.C n) :
    ((outEmbed m n hm hn).cells p).1.val=20-p.2.val := Polyline.L.out_x m (n+20) hm (by omega) p
@[simp] theorem out_y (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (p : FlippedChain.C n) :
    ((outEmbed m n hm hn).cells p).2.val=39+p.1.val := rfl
@[simp] theorem turn_x (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (p : Turn.C) :
    ((turnRect m n hm hn).cells p).1.val=p.1.val := Polyline.L.turn_x m (n+20) hm (by omega) p
@[simp] theorem turn_y (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (p : Turn.C) :
    ((turnRect m n hm hn).cells p).2.val=1+p.2.val := rfl

theorem in_turn_walls (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (p : Chain.C m) (q : Turn.C)
    (he : (inEmbed m n hm hn).cells p=(turnRect m n hm hn).cells q) :
    p∈Chain.walls m hm ↔q∈Turn.template.walls := Polyline.L.in_turn_walls m (n+20) hm (by omega) p q he

theorem turn_out_walls (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (p : Turn.C) (q : FlippedChain.C n)
    (he : (turnRect m n hm hn).cells p=(outEmbed m n hm hn).cells q) :
    p∈Turn.template.walls ↔q∈FlippedChain.walls n hn := by
  have hx:=congrArg (fun p : C m n=>p.1.val) he
  have hy:=congrArg (fun p : C m n=>p.2.val) he
  simp only [turn_x,out_x] at hx
  simp only [turn_y,out_y] at hy
  have hp:=p.2.isLt
  have hq:=q.2.isLt
  rw [Template.mem_walls]
  change Turn.wallTest p=true↔_
  rw [Turn.south_collar p (by omega),decide_eq_true_eq,FlippedChain.left_collar n hn q (by omega)]
  omega

theorem in_out_disjoint (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (p : Chain.C m) (q : FlippedChain.C n) :
    (inEmbed m n hm hn).cells p≠(outEmbed m n hm hn).cells q :=
  Polyline.L.in_out_disjoint m (n+20) hm (by omega) p q

end PushPuzzle.PushFS.Gadgets.Wires.Catalog.Out
