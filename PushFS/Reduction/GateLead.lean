/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Polyline.Collars
public import PushFS.Gadgets.Gates.Collar
import Mathlib.Tactic.FinCases

/-!
# Exact gate-to-chain seams

The real AND and OR ports have different parity and wall sides. These literal
placements use their actual boundary slots, including the one-cell north and
OR offsets. Every wall in each overlapping rectangle agrees.
-/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateLead


open Gadgets Gadgets.Wires Gadgets.Wires.Polyline

abbrev C (n : ℕ) := Cell (2*n+101) (2*n+137)

def gate (n : ℕ) : GridEmbedding 81 107 (2*n+101) (2*n+137) :=
  GridEmbedding.translate (n+10) (n+20) (by omega) (by omega)

def westIso (kind : Bool) (n : ℕ) : GridIsometry (n+5) 21 (n+5) 21 :=
  if kind then GridIsometry.reflectX (n+5) 21
  else (GridIsometry.reflectX (n+5) 21).trans (GridIsometry.reflectY (n+5) 21)

def northIso (n : ℕ) : GridIsometry (n+5) 21 21 (n+5) :=
  (GridIsometry.clockwise (n+5) 21).trans (GridIsometry.reflectY 21 (n+5))

def eastIso (n : ℕ) : GridIsometry (n+5) 21 (n+5) 21 :=
  GridIsometry.reflectY (n+5) 21

def westRect (kind : Bool) (n : ℕ) : GridEmbedding (n+5) 21 (2*n+101) (2*n+137) :=
  GridEmbedding.translate (if kind then 8 else 9) (n+10+(if kind then 29 else 90))
    (by cases kind <;> simp <;> omega) (by cases kind <;> simp <;> omega)

def northRect (kind : Bool) (n : ℕ) : GridEmbedding 21 (n+5) (2*n+101) (2*n+137) :=
  GridEmbedding.translate (n+(if kind then 43 else 44)) 19
    (by cases kind <;> simp <;> omega) (by omega)

def eastRect (kind : Bool) (n : ℕ) : GridEmbedding (n+5) 21 (2*n+101) (2*n+137) :=
  GridEmbedding.translate (n+(if kind then 88 else 87)) (n+100)
    (by cases kind <;> simp <;> omega) (by omega)

def west (kind : Bool) (n : ℕ) := (westIso kind n).embedding.trans (westRect kind n)
def north (kind : Bool) (n : ℕ) := (northIso n).embedding.trans (northRect kind n)
def east (kind : Bool) (n : ℕ) := (eastIso n).embedding.trans (eastRect kind n)

@[simp] theorem gate_x (n : ℕ) (p : Gates.C) : ((gate n).cells p).1.val=n+10+p.1.val := rfl
@[simp] theorem gate_y (n : ℕ) (p : Gates.C) : ((gate n).cells p).2.val=n+20+p.2.val := rfl

@[simp] theorem west_x (kind : Bool) (n : ℕ) (p : Chain.C n) :
    ((west kind n).cells p).1.val=(if kind then 8 else 9)+(n+4-p.1.val) := by
  cases kind <;> simp [west,westIso,westRect,GridEmbedding.trans,GridEmbedding.translate,
    GridIsometry.embedding,GridIsometry.trans,GridIsometry.reflectX,GridIsometry.reflectY,
    GridIsometry.transpose,Fin.revPerm,Fin.rev]

@[simp] theorem west_y (kind : Bool) (n : ℕ) (p : Chain.C n) :
    ((west kind n).cells p).2.val=n+10+(if kind then 29 else 90)+
      (if kind then p.2.val else 20-p.2.val) := by
  cases kind <;> simp [west,westIso,westRect,GridEmbedding.trans,GridEmbedding.translate,
    GridIsometry.embedding,GridIsometry.trans,GridIsometry.reflectX,GridIsometry.reflectY,
    GridIsometry.transpose,Fin.revPerm,Fin.rev]

@[simp] theorem north_x (kind : Bool) (n : ℕ) (p : Chain.C n) :
    ((north kind n).cells p).1.val=n+(if kind then 43 else 44)+(20-p.2.val) := by
  simp [north,northIso,northRect,GridEmbedding.trans,GridEmbedding.translate,
    GridIsometry.embedding,GridIsometry.trans,GridIsometry.reflectX,GridIsometry.reflectY,
    GridIsometry.clockwise,GridIsometry.transpose,Fin.revPerm,Fin.rev]

@[simp] theorem north_y (kind : Bool) (n : ℕ) (p : Chain.C n) :
    ((north kind n).cells p).2.val=19+(n+4-p.1.val) := by
  simp [north,northIso,northRect,GridEmbedding.trans,GridEmbedding.translate,
    GridIsometry.embedding,GridIsometry.trans,GridIsometry.reflectX,GridIsometry.reflectY,
    GridIsometry.clockwise,GridIsometry.transpose,Fin.revPerm,Fin.rev]

@[simp] theorem east_x (kind : Bool) (n : ℕ) (p : Chain.C n) :
    ((east kind n).cells p).1.val=n+(if kind then 88 else 87)+p.1.val := rfl

@[simp] theorem east_y (kind : Bool) (n : ℕ) (p : Chain.C n) :
    ((east kind n).cells p).2.val=n+100+(20-p.2.val) := by
  simp [east,eastIso,eastRect,GridEmbedding.trans,GridEmbedding.translate,
    GridIsometry.embedding,GridIsometry.trans,GridIsometry.reflectX,GridIsometry.reflectY,
    GridIsometry.transpose,Fin.revPerm,Fin.rev]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem west_wall_checked : ∀ (kind : Bool) (p : Gates.C),
    p.1.val≤3 → (if kind then 19 else 80)≤p.2.val → p.2.val≤(if kind then 39 else 100) →
    Gates.wallTest kind p=decide (if kind then p.2.val=30 ∨ p.2.val=31 else p.2.val=88 ∨ p.2.val=89) := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem north_wall_checked : ∀ (kind : Bool) (p : Gates.C),
    p.2.val≤3 → (if kind then 33 else 34)≤p.1.val → p.1.val≤(if kind then 53 else 54) →
    Gates.wallTest kind p=decide (if kind then p.1.val=41 ∨ p.1.val=42 else p.1.val=42 ∨ p.1.val=43) := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
private theorem east_wall_checked : ∀ (kind : Bool) (p : Gates.C),
    77≤p.1.val → 80≤p.2.val → p.2.val≤100 →
    Gates.wallTest kind p=decide (p.2.val=88 ∨ p.2.val=89) := by
  decide +kernel

/-- The complete west overlap agrees for every real chain length. -/
theorem west_walls (kind : Bool) (n : ℕ) (hn : 2301≤n) (p : Chain.C n) (q : Gates.C)
    (he : (west kind n).cells p=(gate n).cells q) :
    p ∈ Chain.walls n hn ↔ q ∈ Gates.walls kind := by
  have hx := congrArg (fun p : C n => p.1.val) he
  have hy := congrArg (fun p : C n => p.2.val) he
  simp only [west_x,west_y,gate_x,gate_y] at hx hy
  have hp := p.1.isLt
  have hpy := p.2.isLt
  have hl : p.1.val<5 := by cases kind <;> simp_all <;> omega
  have hqx : q.1.val≤3 := by cases kind <;> simp_all <;> omega
  have hqy0 : (if kind then 19 else 80)≤q.2.val := by cases kind <;> simp_all <;> omega
  have hqy1 : q.2.val≤(if kind then 39 else 100) := by cases kind <;> simp_all <;> omega
  rw [chain_left5 n hn p hl,Gates.mem_walls,west_wall_checked kind q hqx hqy0 hqy1,decide_eq_true_eq]
  cases kind <;> simp_all <;> omega

/-- The complete north overlap agrees, including its actual one-cell seam shift. -/
theorem north_walls (kind : Bool) (n : ℕ) (hn : 2301≤n) (p : Chain.C n) (q : Gates.C)
    (he : (north kind n).cells p=(gate n).cells q) :
    p ∈ Chain.walls n hn ↔ q ∈ Gates.walls kind := by
  have hx := congrArg (fun p : C n => p.1.val) he
  have hy := congrArg (fun p : C n => p.2.val) he
  simp only [north_x,north_y,gate_x,gate_y] at hx hy
  have hp := p.1.isLt
  have hpy := p.2.isLt
  have hl : p.1.val<5 := by omega
  have hqy : q.2.val≤3 := by omega
  have hqx0 : (if kind then 33 else 34)≤q.1.val := by cases kind <;> simp_all <;> omega
  have hqx1 : q.1.val≤(if kind then 53 else 54) := by cases kind <;> simp_all <;> omega
  rw [chain_left5 n hn p hl,Gates.mem_walls,north_wall_checked kind q hqy hqx0 hqx1,decide_eq_true_eq]
  cases kind <;> simp_all <;> omega

/-- The complete east overlap agrees, using each actual gate's endpoint parity. -/
theorem east_walls (kind : Bool) (n : ℕ) (hn : 2301≤n) (p : Chain.C n) (q : Gates.C)
    (he : (east kind n).cells p=(gate n).cells q) :
    p ∈ Chain.walls n hn ↔ q ∈ Gates.walls kind := by
  have hx := congrArg (fun p : C n => p.1.val) he
  have hy := congrArg (fun p : C n => p.2.val) he
  simp only [east_x,east_y,gate_x,gate_y] at hx hy
  have hqx := q.1.isLt
  have hpy := p.2.isLt
  have hl : p.1.val<5 := by cases kind <;> simp_all <;> omega
  have hqx0 : 77≤q.1.val := by cases kind <;> simp_all <;> omega
  have hqy0 : 80≤q.2.val := by omega
  have hqy1 : q.2.val≤100 := by omega
  rw [chain_left5 n hn p hl,Gates.mem_walls,east_wall_checked kind q hqx0 hqy0 hqy1,decide_eq_true_eq]
  omega

end PushPuzzle.PushFS.Reduction.GateLead
