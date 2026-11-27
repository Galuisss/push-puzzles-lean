/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.Raster

/-! Executable directed unit arcs of the actual refined source drawing. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction


open Cslib.Complexity.NCL Plan Turing.MultiTapeTM ComputableInPolyTime
open scoped PushPuzzle.PushFS.Reduction PushPuzzle.PushFS.Reduction.Plan

/-- A natural-coordinate neighbor, retaining the actual north and west boundaries. -/
def neighbor (d : Direction) (p : GridRouting.Point) : Option GridRouting.Point :=
  match d with
  | .north => if p.2 = 0 then none else some (p.1, p.2 - 1)
  | .east => some (p.1 + 1, p.2)
  | .south => some (p.1, p.2 + 1)
  | .west => if p.1 = 0 then none else some (p.1 - 1, p.2)

/-- Unit steps in the orientation in which this segment was emitted. -/
def Segment.Arc (s : Segment) (d : Direction) (p : GridRouting.Point) : Prop :=
  match d with
  | .north => s.start.1 = s.finish.1 ∧ p.1 = s.start.1 ∧
      s.finish.2 < p.2 ∧ p.2 ≤ s.start.2
  | .east => s.start.2 = s.finish.2 ∧ p.2 = s.start.2 ∧
      s.start.1 ≤ p.1 ∧ p.1 < s.finish.1
  | .south => s.start.1 = s.finish.1 ∧ p.1 = s.start.1 ∧
      s.start.2 ≤ p.2 ∧ p.2 < s.finish.2
  | .west => s.start.2 = s.finish.2 ∧ p.2 = s.start.2 ∧
      s.finish.1 < p.1 ∧ p.1 ≤ s.start.1

instance (s : Segment) (d : Direction) (p : GridRouting.Point) : Decidable (s.Arc d p) := by
  cases d <;> unfold Segment.Arc <;> infer_instance

/-- A Boolean query of the emitted segment, including its direction. -/
def Segment.arcTest (d : Direction) (q : Segment × GridRouting.Point) : Bool :=
  match d with
  | .north => decide (q.1.start.1 = q.1.finish.1 ∧ q.2.1 = q.1.start.1 ∧
      q.1.finish.2 < q.2.2 ∧ q.2.2 ≤ q.1.start.2)
  | .east => decide (q.1.start.2 = q.1.finish.2 ∧ q.2.2 = q.1.start.2 ∧
      q.1.start.1 ≤ q.2.1 ∧ q.2.1 < q.1.finish.1)
  | .south => decide (q.1.start.1 = q.1.finish.1 ∧ q.2.1 = q.1.start.1 ∧
      q.1.start.2 ≤ q.2.2 ∧ q.2.2 < q.1.finish.2)
  | .west => decide (q.1.start.2 = q.1.finish.2 ∧ q.2.2 = q.1.start.2 ∧
      q.1.finish.1 < q.2.1 ∧ q.2.1 ≤ q.1.start.1)

theorem Segment.arcTest_correct (d : Direction) (s : Segment) (p : GridRouting.Point) :
    Segment.arcTest d (s, p) = true ↔ s.Arc d p := by
  cases d <;> simp [Segment.arcTest, Segment.Arc]

/-- Every selected unit arc has both actual endpoints on its emitting segment. -/
theorem Segment.Arc.endpoints {s : Segment} {d : Direction} {p : GridRouting.Point}
    (h : s.Arc d p) :
    ∃ q, neighbor d p = some q ∧ s.Contains p ∧ s.Contains q := by
  cases d <;> simp only [Segment.Arc] at h
  · refine ⟨(p.1, p.2 - 1), ?_, ?_, ?_⟩
    · simp [neighbor, show p.2 ≠ 0 by omega]
    · exact Or.inl ⟨h.1, h.2.1, by omega, by omega⟩
    · exact Or.inl ⟨h.1, h.2.1, by dsimp only; omega, by dsimp only; omega⟩
  · refine ⟨(p.1 + 1, p.2), rfl, ?_, ?_⟩
    · exact Or.inr ⟨h.1, h.2.1, by omega, by omega⟩
    · exact Or.inr ⟨h.1, h.2.1, by dsimp only; omega, by dsimp only; omega⟩
  · refine ⟨(p.1, p.2 + 1), rfl, ?_, ?_⟩
    · exact Or.inl ⟨h.1, h.2.1, by omega, by omega⟩
    · exact Or.inl ⟨h.1, h.2.1, by dsimp only; omega, by dsimp only; omega⟩
  · refine ⟨(p.1 - 1, p.2), ?_, ?_, ?_⟩
    · simp [neighbor, show p.1 ≠ 0 by omega]
    · exact Or.inr ⟨h.1, h.2.1, by omega, by omega⟩
    · exact Or.inr ⟨h.1, h.2.1, by dsimp only; omega, by dsimp only; omega⟩

theorem neighbor_reverse {d : Direction} {p q : GridRouting.Point}
    (h : neighbor d p = some q) : neighbor d.opposite q = some p := by
  cases d <;> simp only [neighbor, Direction.opposite] at h ⊢
  · split_ifs at h; simp_all [Prod.ext_iff]; omega
  · have hh := Option.some.inj h
    cases hh
    simp
  · have hh := Option.some.inj h
    cases hh
    simp
  · split_ifs at h; simp_all [Prod.ext_iff]; omega

@[fun_prop] theorem neighbor_polyTime (d : Direction) :
    ComputableInPolyTime (neighbor d) Bitmap.encPoint (encOption Bitmap.encPoint) := by
  cases d <;> unfold neighbor Bitmap.encPoint <;> fun_prop

@[fun_prop] theorem Segment.arcTest_polyTime (d : Direction) :
    ComputableInPolyTime (Segment.arcTest d) (encPair encSegment Bitmap.encPoint) encBool := by
  cases d <;> unfold Segment.arcTest <;> fun_prop

namespace Raster

/-- The four occupied directions at a named edge pixel. -/
structure Mask where
  north : Bool
  east : Bool
  south : Bool
  west : Bool
  deriving DecidableEq, Repr

enc_structure encMask : Mask where
  north : encBool, east : encBool, south : encBool, west : encBool

/-- Read one of the four stored bits. -/
def Mask.get (m : Mask) (d : Direction) : Bool :=
  match d with
  | .north => m.north
  | .east => m.east
  | .south => m.south
  | .west => m.west

/-- Find a directed outgoing unit arc of the given original source edge. -/
def outgoing (d : Direction) (q : Word × (ℕ × GridRouting.Point)) : Bool :=
  (refinedProgram q.1).any fun r => r.edge == q.2.1 &&
    r.path.any (fun s => Segment.arcTest d (s, q.2.2))

/-- An incoming bit names the neighbor's outgoing arc towards this cell. -/
def incoming (d : Direction) (q : Word × (ℕ × GridRouting.Point)) : Bool :=
  match d with
  | .north => if q.2.2.2 = 0 then false
      else outgoing .south (q.1, (q.2.1, (q.2.2.1, q.2.2.2 - 1)))
  | .east => outgoing .west (q.1, (q.2.1, (q.2.2.1 + 1, q.2.2.2)))
  | .south => outgoing .north (q.1, (q.2.1, (q.2.2.1, q.2.2.2 + 1)))
  | .west => if q.2.2.1 = 0 then false
      else outgoing .east (q.1, (q.2.1, (q.2.2.1 - 1, q.2.2.2)))

theorem incoming_eq_neighbor (d : Direction) (q : Word × (ℕ × GridRouting.Point)) :
    incoming d q = (neighbor d q.2.2).elim false
      (fun p => outgoing d.opposite (q.1, (q.2.1, p))) := by
  cases d <;> simp only [incoming, neighbor, Direction.opposite]
  · split_ifs <;> rfl
  · rfl
  · rfl
  · split_ifs <;> rfl

/-- Actual machine-computed outgoing directions. -/
def outgoingMask (q : Word × (ℕ × GridRouting.Point)) : Mask :=
  ⟨outgoing .north q, outgoing .east q, outgoing .south q, outgoing .west q⟩

/-- Actual machine-computed incoming directions. -/
def incomingMask (q : Word × (ℕ × GridRouting.Point)) : Mask :=
  ⟨incoming .north q, incoming .east q, incoming .south q, incoming .west q⟩

@[simp] theorem outgoingMask_get (d : Direction) (q : Word × (ℕ × GridRouting.Point)) :
    (outgoingMask q).get d = outgoing d q := by cases d <;> rfl

@[simp] theorem incomingMask_get (d : Direction) (q : Word × (ℕ × GridRouting.Point)) :
    (incomingMask q).get d = incoming d q := by cases d <;> rfl

theorem outgoing_correct (d : Direction) (w : Word) (e : ℕ) (p : GridRouting.Point) :
    outgoing d (w, (e, p)) = true ↔
      ∃ r ∈ refinedProgram w, r.edge = e ∧ ∃ s ∈ r.path, s.Arc d p := by
  simp [outgoing, Segment.arcTest_correct]

/-- A set outgoing bit certifies the two real pixels, retaining their original edge name. -/
theorem outgoing_sound {d : Direction} {w : Word} {e : ℕ} {p : GridRouting.Point}
    (h : outgoing d (w, (e, p)) = true) :
    ∃ q, neighbor d p = some q ∧ Route.Trace (refinedProgram w) e p ∧
      Route.Trace (refinedProgram w) e q := by
  obtain ⟨r, hr, he, s, hs, ha⟩ := (outgoing_correct d w e p).mp h
  obtain ⟨q, hq, hp, ht⟩ := ha.endpoints
  exact ⟨q, hq, ⟨r, hr, he, s, hs, hp⟩, ⟨r, hr, he, s, hs, ht⟩⟩

/-- Incoming bits certify the same two actual pixels with reversed travel direction. -/
theorem incoming_sound {d : Direction} {w : Word} {e : ℕ} {p : GridRouting.Point}
    (h : incoming d (w, (e, p)) = true) :
    ∃ q, neighbor d p = some q ∧ outgoing d.opposite (w, (e, q)) = true ∧
      Route.Trace (refinedProgram w) e p ∧ Route.Trace (refinedProgram w) e q := by
  rw [incoming_eq_neighbor] at h
  cases hn : neighbor d p with
  | none => simp [hn] at h
  | some q =>
    simp only [hn] at h
    obtain ⟨r, hr, hq, hp⟩ := outgoing_sound h
    have hr' := neighbor_reverse hn
    rw [hr'] at hr
    cases Option.some.inj hr
    exact ⟨q, rfl, h, hp, hq⟩

@[fun_prop] theorem outgoing_polyTime (d : Direction) :
    ComputableInPolyTime (outgoing d)
      (encPair encWord (encPair encUnary Bitmap.encPoint)) encBool := by
  have hr := refinedProgram_polyTime
  unfold outgoing
  fun_prop

@[fun_prop] theorem incoming_polyTime (d : Direction) :
    ComputableInPolyTime (incoming d)
      (encPair encWord (encPair encUnary Bitmap.encPoint)) encBool := by
  cases d <;> unfold incoming <;> fun_prop

@[fun_prop] theorem outgoingMask_polyTime :
    ComputableInPolyTime outgoingMask
      (encPair encWord (encPair encUnary Bitmap.encPoint)) encMask := by
  unfold outgoingMask
  fun_prop

@[fun_prop] theorem incomingMask_polyTime :
    ComputableInPolyTime incomingMask
      (encPair encWord (encPair encUnary Bitmap.encPoint)) encMask := by
  unfold incomingMask
  fun_prop

end Raster
end PushPuzzle.PushFS.Reduction
