/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.GateLeadMacros
public import PushFS.Gadgets.Gates.Walking

/-! Exact player access between the gate hub and each released long-lead hub. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateLead


open Gadgets Gadgets.Wires

set_option maxRecDepth 65536

def bridgeCorner (kind : Bool) (i : Fin 3) : Fin 4 :=
  if i=0 then if kind then 0 else 2 else if i=1 then 1 else 3

/-- These real gate cells are simultaneously the nearest actual lead corners. -/
def bridgePoint (kind : Bool) (i : Fin 3) : Gates.C :=
  if i=0 then if kind then (1,20) else (2,99)
  else if i=1 then (if kind then 52 else 53,2) else (if kind then 79 else 78,99)

private def bridgeWalk (kind : Bool) (i : Fin 3) : List Direction :=
  if i=0 then if kind then List.replicate 19 .south else [.east]++List.replicate 6 .north
  else if i=1 then List.replicate (if kind then 27 else 26) .west++[.south]
  else List.replicate 6 .north++(if kind then [] else [.west])

private theorem bridge_checked : ∀ (kind : Bool) (i : Fin 3),
    Execution.valid (Gates.walkTest kind) ⟨Gates.corner (bridgeCorner kind i),∅⟩=true ∧
    Execution.check (Gates.walkTest kind) ⟨Gates.corner (bridgeCorner kind i),∅⟩
      ⟨bridgePoint kind i,∅⟩ (bridgeWalk kind i)=true ∧
    Execution.valid (Gates.walkTest kind) ⟨bridgePoint kind i,∅⟩=true ∧
    Execution.check (Gates.walkTest kind) ⟨bridgePoint kind i,∅⟩
      ⟨Gates.corner (bridgeCorner kind i),∅⟩ ((bridgeWalk kind i).reverse.map Direction.opposite)=true := by
  decide +kernel

theorem bridge_paths (kind : Bool) (i : Fin 3) :
    Reachable (Gates.walkBoard kind) (some 1) ⟨Gates.corner (bridgeCorner kind i),∅⟩ ⟨bridgePoint kind i,∅⟩ ∧
    Reachable (Gates.walkBoard kind) (some 1) ⟨bridgePoint kind i,∅⟩ ⟨Gates.corner (bridgeCorner kind i),∅⟩ :=
  ⟨Execution.sound (Gates.walkTest_correct kind) (bridge_checked kind i).1 (bridge_checked kind i).2.1,
    Execution.sound (Gates.walkTest_correct kind) (bridge_checked kind i).2.2.1 (bridge_checked kind i).2.2.2⟩

theorem boundary_reserved (kind : Bool) (c : Gates.Signals) :
    Gates.boundaryNeighbors kind c ⊆ Gates.reserved kind := by
  have hh : ∀ (kind a b c : Bool),
      @decide (∀ p∈Gates.boundaryNeighbors kind ⟨a,b,c⟩,Gates.reservedTest kind p=true)
        Finset.decidableDforallFinset=true := by decide +kernel
  intro p hp
  have hp' := (@of_decide_eq_true _ Finset.decidableDforallFinset
    (hh kind c.left c.upper c.right)) p hp
  exact (Gates.mem_reserved kind p).mpr hp'

/-- A conservative empty walking path remains the same actual walk with all owned gate boxes and fixed collar boxes. -/
theorem frame_empty {kind : Bool} {fr : Finset Gates.C}
    (hf : fr ⊆ Gates.reserved kind) (hw : Disjoint fr (Gates.walls kind))
    {p q : Gates.C} (hr : Reachable (Gates.walkBoard kind) (some 1) ⟨p,∅⟩ ⟨q,∅⟩) :
    Reachable (Gates.board kind ∅) (some 1) ⟨p,fr⟩ ⟨q,fr⟩ := by
  have hh := Gates.reachable_withFixed (B := Gates.board kind ∅) hf hw hr
  simpa only [Gates.withFixed,Finset.empty_union] using hh

theorem west_bridge (kind : Bool) (n : ℕ) :
    (gate n).cells (bridgePoint kind 0)=(west kind n).cells (Chain.corner n 0) := by
  apply Prod.ext <;> apply Fin.ext
  · rw [gate_x,west_x]
    cases kind <;> simp [bridgePoint,Chain.corner] <;> omega
  · rw [gate_y,west_y]
    cases kind <;> simp [bridgePoint,Chain.corner]

theorem north_bridge (kind : Bool) (n : ℕ) :
    (gate n).cells (bridgePoint kind 1)=(north kind n).cells (Chain.corner n 0) := by
  apply Prod.ext <;> apply Fin.ext
  · rw [gate_x,north_x]
    cases kind <;> simp [bridgePoint,Chain.corner]
  · rw [gate_y,north_y]
    cases kind <;> simp [bridgePoint,Chain.corner] <;> omega

theorem east_bridge (kind : Bool) (n : ℕ) :
    (gate n).cells (bridgePoint kind 2)=(east kind n).cells (Chain.corner n 0) := by
  apply Prod.ext <;> apply Fin.ext
  · rw [gate_x,east_x]
    cases kind <;> simp [bridgePoint,Chain.corner]
  · rw [gate_y,east_y]
    cases kind <;> simp [bridgePoint,Chain.corner]

end PushPuzzle.PushFS.Reduction.GateLead
