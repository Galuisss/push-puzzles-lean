/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalWalls
public import PushFS.Reduction.PhysicalSlotBounds

/-! Uniform canonical source and target slots in the actual complete physical tiles. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalTiles


open Cslib.Complexity.NCL Plan Gadgets.Wires

/-- False selects actual initial boxes; true selects their actual storage goals. -/
noncomputable def slots (goal : Bool) (k : Key) : Labels k↪Cell (piece k).width (piece k).height :=
  if goal then (matching k).target else (matching k).source

def bits (q : CellPlan.Source) (goal : Bool) : List Bool := if goal then q.2.2 else q.2.1

def wirePhase (a : Catalog.Bitmap.Args) (goal : Bool) : Bool := if goal then a.2.2 else a.2.1

def gatePhase (g : GateTileState) (goal : Bool) (role : Fin 3) : Bool :=
  if goal then GateTileRouting.Inventory.targetPhase g role else GateTileRouting.Inventory.initialPhase g role

theorem wire_slots_bounds (a : Catalog.Bitmap.Args) (goal : Bool) (l : Labels (.inr a)) :
    Catalog.SlotRegion a.1 (wirePhase a goal) (slots goal (.inr a) l) := by
  cases goal
  · exact Catalog.source_bounds a.1 a.2.1 a.2.2 l
  · exact Catalog.target_bounds a.1 a.2.1 a.2.2 l

theorem wire_slots_face (a : Catalog.Bitmap.Args) (goal : Bool) (f : Catalog.Face)
    (l : Labels (.inr a)) (hf : Catalog.InFace f (slots goal (.inr a) l)) : Catalog.FaceUsed a.1 f := by
  cases goal
  · exact (Catalog.source_boundary a.1 a.2.1 a.2.2 f l hf).elim
      (fun h=>Or.inl h.1) (fun h=>Or.inr h.1)
  · exact (Catalog.target_boundary a.1 a.2.1 a.2.2 f l hf).elim
      (fun h=>Or.inl h.1) (fun h=>Or.inr h.1)

theorem wire_phase {q : CellPlan.Source} {p : GridRouting.Point} {e : ℕ} {a : Catalog.Bitmap.Args}
    (hc : CellPlan.cell (q,p)=some (.inr (e,a))) (goal : Bool) :
    wirePhase a goal=!(bits q goal).getD e false := by
  obtain ⟨_,_,_,hi,ht⟩ := CellPlan.wire_sound hc
  cases goal
  · exact hi
  · exact ht

theorem gate_phase (q : CellPlan.Source) (v : VertexData) (goal : Bool) (role : Fin 3) :
    gatePhase (gateTileState (v,q.2)) goal role=
      if (v.ports.port role).dir then !(!(bits q goal).getD (v.ports.port role).edge false)
        else !(bits q goal).getD (v.ports.port role).edge false := by
  cases goal <;> simp only [gatePhase,bits,Bool.false_eq_true,ite_false,ite_true,
    GateTileRouting.Inventory.initialPhase,GateTileRouting.Inventory.targetPhase,gateTileState]
  all_goals rw [gateSignals_wire_phase]; simp only [Bool.not_not]

theorem gate_slots_frame (g : GateTileState) (goal : Bool) (d : Direction) (l : Labels (.inl g))
    (hf : GateTileRouting.FullGateBoundary.InFrame d
      ((slots goal (.inl g) l).1.val,(slots goal (.inl g) l).2.val)) :
    ∃role : Fin 3,∃prev : Bool,PortAnnulus.outerDirection (g.key role).2=d ∧
      ((slots goal (.inl g) l).1.val,(slots goal (.inl g) l).2.val)=
        GateTileRouting.FullGateBoundary.endpointPoint d (g.incoming.get role) (gatePhase g goal role) prev := by
  cases goal
  · exact GateTileRouting.full_source_frame g d l hf
  · exact GateTileRouting.full_target_frame g d l hf

end PushPuzzle.PushFS.Reduction.PhysicalTiles
