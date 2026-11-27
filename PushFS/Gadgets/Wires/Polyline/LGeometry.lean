/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Polyline.Collars
public import PushFS.AxisIsometry
public import PushFS.Gadgets.Wires.Catalog
public import PushFS.StaticPlacement
public import PushFS.Reduction.StorageRaster
import Mathlib.Tactic.FinCases

/-! Exact physical coordinates of a westward long chain, guarded turn and southward long chain. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Polyline.L

abbrev C (m n : ℕ) := Cell (m+43) (n+44)
abbrev Phases := Fin 3 → Bool

def inIso (m : ℕ) := GridIsometry.reflectX (m+5) 21
def outIso (n : ℕ) := GridIsometry.clockwise (n+5) 21

def inRect (m n : ℕ) (_hm : 2301 ≤ m) (hn : 2301 ≤ n) : GridEmbedding (m+5) 21 (m+43) (n+44) :=
  GridEmbedding.translate 38 0 (by omega) (by omega)
def turnRect (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) : GridEmbedding 45 41 (m+43) (n+44) :=
  GridEmbedding.translate 0 1 (by omega) (by omega)
def outRect (m n : ℕ) (hm : 2301 ≤ m) (_hn : 2301 ≤ n) : GridEmbedding 21 (n+5) (m+43) (n+44) :=
  GridEmbedding.translate 0 39 (by omega) (by omega)

def inEmbed (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) := (inIso m).embedding.trans (inRect m n hm hn)
def outEmbed (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) := (outIso n).embedding.trans (outRect m n hm hn)

@[simp] theorem in_x (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (p : Chain.C m) :
    ((inEmbed m n hm hn).cells p).1.val=38+(m+4-p.1.val) := by
  change 38+((inIso m).cells p).1.val=_
  simp [inIso,GridIsometry.reflectX,Fin.revPerm,Fin.rev]
@[simp] theorem in_y (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (p : Chain.C m) :
    ((inEmbed m n hm hn).cells p).2.val=p.2.val := by
  change 0+((inIso m).cells p).2.val=p.2.val
  simp [inIso,GridIsometry.reflectX]
@[simp] theorem out_x (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (p : Chain.C n) :
    ((outEmbed m n hm hn).cells p).1.val=20-p.2.val := by
  change 0+((outIso n).cells p).1.val=_
  simp [outIso,GridIsometry.clockwise,GridIsometry.trans,GridIsometry.transpose,GridIsometry.reflectX,Fin.revPerm,Fin.rev]
@[simp] theorem out_y (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (p : Chain.C n) :
    ((outEmbed m n hm hn).cells p).2.val=39+p.1.val := rfl
@[simp] theorem turn_x (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (p : Turn.C) :
    ((turnRect m n hm hn).cells p).1.val=p.1.val := by change 0+p.1.val=p.1.val; omega
@[simp] theorem turn_y (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n) (p : Turn.C) :
    ((turnRect m n hm hn).cells p).2.val=1+p.2.val := rfl

/-- Both precise overlap stencils agree, including every cell of their shared rectangles. -/
theorem in_turn_walls (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n)
    (p : Chain.C m) (q : Turn.C) (he : (inEmbed m n hm hn).cells p=(turnRect m n hm hn).cells q) :
    p ∈ Chain.walls m hm ↔ q ∈ Turn.template.walls := by
  have hx := congrArg (fun p : C m n => p.1.val) he
  have hy := congrArg (fun p : C m n => p.2.val) he
  simp only [in_x,turn_x] at hx
  simp only [in_y,turn_y] at hy
  have hq := q.1.isLt
  have hp := p.1.isLt
  have hright : m ≤ p.1.val+2 := by omega
  have heast : 38 ≤ q.1.val := by omega
  rw [chain_right7 m hm p hright,turn_east7 q heast]
  omega

theorem turn_out_walls (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n)
    (p : Turn.C) (q : Chain.C n) (he : (turnRect m n hm hn).cells p=(outEmbed m n hm hn).cells q) :
    p ∈ Turn.template.walls ↔ q ∈ Chain.walls n hn := by
  have hx := congrArg (fun p : C m n => p.1.val) he
  have hy := congrArg (fun p : C m n => p.2.val) he
  simp only [turn_x,out_x] at hx
  simp only [turn_y,out_y] at hy
  have hp := p.2.isLt
  have hq := q.2.isLt
  have hs : 36 ≤ p.2.val := by omega
  have hl : q.1.val < 5 := by omega
  have hw := Turn.south_collar p hs
  rw [Template.mem_walls]
  change Turn.wallTest p=true ↔ _
  rw [hw,decide_eq_true_eq,chain_left5 n hn q hl]
  omega

theorem in_out_disjoint (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n)
    (p : Chain.C m) (q : Chain.C n) : (inEmbed m n hm hn).cells p ≠ (outEmbed m n hm hn).cells q := by
  intro he
  have hx := congrArg (fun p : C m n => p.1.val) he
  simp only [in_x,out_x] at hx
  omega

end PushPuzzle.PushFS.Gadgets.Wires.Polyline.L
