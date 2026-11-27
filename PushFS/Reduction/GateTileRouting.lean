/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.GateTileData
public import PushFS.Reduction.GateLeadEndpoints
public import PushFS.Reduction.DirectedRaster

/-! Physical annular paths begin at the real buffered endpoints and use the source input/output seam parity. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateTileRouting


open Gadgets Turing.MultiTapeTM ComputableInPolyTime

abbrev Key := GateAnnulus.Key × Bool
abbrev C := Cell 200007 198068

/-- Three cells of exterior padding accommodate every actual shared port collar. -/
def pad (p : ℕ × ℕ) : ℕ × ℕ := (p.1+3,p.2+3)

/-- Place the complete buffered core with its actual unrotated gate at the checked annular core offset. -/
def bufferOffset (kind : Bool) : ℕ × ℕ :=
  ((GateAnnulus.coreOffset kind).1+3-2311,(GateAnnulus.coreOffset kind).2+3-2321)

def bufferRect (kind : Bool) : GridEmbedding 4703 4739 200007 198068 :=
  GridEmbedding.translate (bufferOffset kind).1 (bufferOffset kind).2
    (by cases kind <;> decide +kernel) (by cases kind <;> decide +kernel)

/-- The true exposed seam anchor of the corresponding complete long lead. -/
def bufferedEnd (k : GateAnnulus.Key) : ℕ × ℕ :=
  let p := GateLead.portAnchor k.1 2301 (GateAnnulus.role k)
  ((bufferOffset k.1).1+p.1.val,(bufferOffset k.1).2+p.2.val)

/-- The outer logical boundary anchor, before the source input parity correction. -/
def boundary (k : GateAnnulus.Key) : ℕ × ℕ :=
  pad (GateAnnulus.point ((GateAnnulus.vertices k).getLastD (0,0)))

/-- An input arm extends one unit outward for its end-to-end inverse-phase join. -/
def tail (q : Key) : ℕ × ℕ :=
  if q.2 then (neighbor (PortAnnulus.outerDirection q.1.2) (boundary q.1)).getD (boundary q.1)
  else boundary q.1

/-- Drop the collinear inner join, then connect the actual buffered endpoint to the parity-correct outer endpoint. -/
def vertices (q : Key) : List (ℕ × ℕ) :=
  [bufferedEnd q.1] ++ ((GateAnnulus.vertices q.1).tail.dropLast.map (fun p => pad (GateAnnulus.point p))) ++ [tail q]

def curve (q : Key) : List Segment := (vertices q).zipWith Segment.mk (vertices q).tail

/-- The actual finite routing key, including whether this original source incidence consumes an edge. -/
def key (g : GateTileState) (i : Fin 3) : Key := (g.key i,g.incoming.get i)

private def segmentTest (s : Segment) : Bool :=
  decide (((s.start.1=s.finish.1 ∧ min s.start.2 s.finish.2+3000≤max s.start.2 s.finish.2) ∨
    (s.start.2=s.finish.2 ∧ min s.start.1 s.finish.1+3000≤max s.start.1 s.finish.1)) ∧
    2≤s.start.1 ∧ 2≤s.start.2 ∧ 2≤s.finish.1 ∧ 2≤s.finish.2 ∧
    s.start.1≤200004 ∧ s.finish.1≤200004 ∧ s.start.2≤198065 ∧ s.finish.2≤198065)

private def cornerTest (a b c : ℕ × ℕ) : Bool :=
  decide ((a.1=b.1 ∧ b.2=c.2 ∧ a.2≠b.2 ∧ b.1≠c.1) ∨
    (a.2=b.2 ∧ b.1=c.1 ∧ a.1≠b.1 ∧ b.2≠c.2))

private def shapeTest (q : Key) : Bool :=
  decide (2≤(vertices q).length) &&
    decide (PortAnnulus.Runs (Gates.portDirection (GateAnnulus.role q.1)) (bufferedEnd q.1)
      ((vertices q).getD 1 (0,0))) &&
    decide (PortAnnulus.Runs (PortAnnulus.outerDirection q.1.2)
      ((vertices q).getD ((vertices q).length-2) (0,0)) (tail q)) &&
    (curve q).all segmentTest &&
    (List.range ((vertices q).length-2)).all (fun i => cornerTest
      ((vertices q).getD i (0,0)) ((vertices q).getD (i+1) (0,0)) ((vertices q).getD (i+2) (0,0)))

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem shape_checked : ∀ q : Key, shapeTest q=true := by decide +kernel

/-- Every surviving waypoint is a real perpendicular guarded-turn location. -/
theorem corners (q : Key) {i : ℕ} (hi : i+2<(vertices q).length) :
    let a := (vertices q).getD i (0,0)
    let b := (vertices q).getD (i+1) (0,0)
    let c := (vertices q).getD (i+2) (0,0)
    (a.1=b.1 ∧ b.2=c.2 ∧ a.2≠b.2 ∧ b.1≠c.1) ∨
      (a.2=b.2 ∧ b.1=c.1 ∧ a.1≠b.1 ∧ b.2≠c.2) := by
  have hh := shape_checked q
  simp only [shapeTest,Bool.and_eq_true] at hh
  have ha : (List.range ((vertices q).length-2)).all (fun i => cornerTest
      ((vertices q).getD i (0,0)) ((vertices q).getD (i+1) (0,0)) ((vertices q).getD (i+2) (0,0)))=true := by tauto
  exact of_decide_eq_true (List.all_eq_true.mp ha i (List.mem_range.mpr (by omega)))

end PushPuzzle.PushFS.Reduction.GateTileRouting
