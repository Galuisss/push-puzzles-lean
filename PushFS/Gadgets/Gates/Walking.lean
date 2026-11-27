/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Gates.Framing
public import PushFS.Gadgets.Gates.Slots
import Mathlib.Tactic.FinCases

/-!
# Hub-to-corner walks for every independent buffer phase

The eight explicit empty-state direction lists avoid the entire reserved rail
set. Replacing any subset of those conservative obstacles by actual boxes keeps
all walks legal and the actual box set fixed, including mixed buffer phases.
-/

@[expose] public section

namespace PushPuzzle.PushFS.Gadgets.Gates


/-- Four exterior walking anchors in NW, NE, SW, SE order. -/
def corner (i : Fin 4) : C :=
  if i = 0 then (1, 1) else if i = 1 then (79, 1) else if i = 2 then (1, 105) else (79, 105)

/-- Reserve all rail positions except designated flip crossings. -/
def walkTest (kind : Bool) (p : C) : Bool := wallTest kind p || reservedTest kind p

/-- Conservative walking geometry, with all possible rail box positions blocked. -/
def walkBoard (kind : Bool) : Board 81 107 := ⟨walls kind ∪ reserved kind, ∅⟩

theorem walkTest_correct (kind : Bool) (p : C) :
    walkTest kind p = true ↔ p ∈ (walkBoard kind).walls := by
  simp [walkTest, walkBoard]

-- The finite walking certificates reduce explicit coordinate lists through the executor.
set_option maxRecDepth 65536

def andWalk0 : List Direction := [.east, .east, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north]
private theorem andWalk0_checked :
    Execution.valid (walkTest true) ⟨hub, ∅⟩ = true ∧
    Execution.check (walkTest true) ⟨hub, ∅⟩ ⟨corner 0, ∅⟩ andWalk0 = true := by decide +kernel

def andWalk1 : List Direction := [.east, .east, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .west, .west, .north, .north, .north, .north, .north, .north, .north, .north, .north, .east, .east, .east, .south, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north]
private theorem andWalk1_checked :
    Execution.valid (walkTest true) ⟨hub, ∅⟩ = true ∧
    Execution.check (walkTest true) ⟨hub, ∅⟩ ⟨corner 1, ∅⟩ andWalk1 = true := by decide +kernel

def andWalk2 : List Direction := [.east, .east, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .west, .west, .west, .south, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south]
private theorem andWalk2_checked :
    Execution.valid (walkTest true) ⟨hub, ∅⟩ = true ∧
    Execution.check (walkTest true) ⟨hub, ∅⟩ ⟨corner 2, ∅⟩ andWalk2 = true := by decide +kernel

def andWalk3 : List Direction := [.east, .east, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .west, .west, .west, .south, .west, .west, .west, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south]
private theorem andWalk3_checked :
    Execution.valid (walkTest true) ⟨hub, ∅⟩ = true ∧
    Execution.check (walkTest true) ⟨hub, ∅⟩ ⟨corner 3, ∅⟩ andWalk3 = true := by decide +kernel

def orWalk0 : List Direction := [.west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north]
private theorem orWalk0_checked :
    Execution.valid (walkTest false) ⟨hub, ∅⟩ = true ∧
    Execution.check (walkTest false) ⟨hub, ∅⟩ ⟨corner 0, ∅⟩ orWalk0 = true := by decide +kernel

def orWalk1 : List Direction := [.east, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .east, .east, .east, .south, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north]
private theorem orWalk1_checked :
    Execution.valid (walkTest false) ⟨hub, ∅⟩ = true ∧
    Execution.check (walkTest false) ⟨hub, ∅⟩ ⟨corner 1, ∅⟩ orWalk1 = true := by decide +kernel

def orWalk2 : List Direction := [.west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .south, .south, .south, .south, .south, .south, .south, .south, .east, .south, .south, .south, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south]
private theorem orWalk2_checked :
    Execution.valid (walkTest false) ⟨hub, ∅⟩ = true ∧
    Execution.check (walkTest false) ⟨hub, ∅⟩ ⟨corner 2, ∅⟩ orWalk2 = true := by decide +kernel

def orWalk3 : List Direction := [.west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .south, .south, .south, .south, .south, .south, .south, .south, .east, .south, .south, .south, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south]
private theorem orWalk3_checked :
    Execution.valid (walkTest false) ⟨hub, ∅⟩ = true ∧
    Execution.check (walkTest false) ⟨hub, ∅⟩ ⟨corner 3, ∅⟩ orWalk3 = true := by decide +kernel

private theorem corner_walk (kind : Bool) (i : Fin 4) :
    Reachable (walkBoard kind) (some 1) ⟨hub, ∅⟩ ⟨corner i, ∅⟩ := by
  have h : ∀ k, ∀ i : Fin 4, ∃ ds,
      Execution.valid (walkTest k) ⟨hub, ∅⟩ = true ∧
      Execution.check (walkTest k) ⟨hub, ∅⟩ ⟨corner i, ∅⟩ ds = true := by
    intro k i
    fin_cases i <;> cases k
    · exact ⟨orWalk0, orWalk0_checked⟩
    · exact ⟨andWalk0, andWalk0_checked⟩
    · exact ⟨orWalk1, orWalk1_checked⟩
    · exact ⟨andWalk1, andWalk1_checked⟩
    · exact ⟨orWalk2, orWalk2_checked⟩
    · exact ⟨andWalk2, andWalk2_checked⟩
    · exact ⟨orWalk3, orWalk3_checked⟩
    · exact ⟨andWalk3, andWalk3_checked⟩
  obtain ⟨ds, hs, he⟩ := h kind i
  exact Execution.sound (walkTest_correct kind) hs he

private theorem empty_symm {B : Board 81 107} {p q : C}
    (hr : Reachable B (some 1) ⟨p, ∅⟩ ⟨q, ∅⟩) :
    Reachable B (some 1) ⟨q, ∅⟩ ⟨p, ∅⟩ := by
  have aux : ∀ {s t : State 81 107}, Reachable B (some 1) s t → s.boxes = ∅ →
      Reachable B (some 1) t s := by
    intro s t hr
    induction hr with
    | refl => intro _; exact .refl
    | @tail u v hr hs ih =>
      intro he
      have hu : u.boxes = ∅ := Finset.card_eq_zero.mp (by rw [Reachable.card_boxes hr, he]; rfl)
      have hv : v.boxes = ∅ := Finset.card_eq_zero.mp (by rw [Step.card_boxes hs, hu]; rfl)
      obtain ⟨d, hd⟩ := hs
      have hm := Move.single_iff.mp hd
      have hback : Move B (some 1) d.opposite v u :=
        .walk hd.valid_target hm.2.1.reverse hd.valid_source.1 (by simp [hv]) (hu.trans hv.symm)
      exact (Relation.ReflTransGen.single ⟨d.opposite, hback⟩).trans (ih he)
  exact aux hr rfl

private theorem frame_walk (kind : Bool) (goals boxes : Finset C)
    (hb : boxes ⊆ reserved kind) (hw : Disjoint boxes (walls kind)) {p q : C}
    (hr : Reachable (walkBoard kind) (some 1) ⟨p, ∅⟩ ⟨q, ∅⟩) :
    Reachable (board kind goals) (some 1) ⟨p, boxes⟩ ⟨q, boxes⟩ := by
  have hstep : ∀ s t, Step (walkBoard kind) (some 1) s t →
      Step (⟨walls kind ∪ reserved kind, goals⟩ : Board 81 107) (some 1) s t := by
    rintro s t ⟨d, hd⟩
    have hm : SingleMoveView (walkBoard kind) d s t := Move.single_iff.mp hd
    exact ⟨d, Move.single_iff.mpr hm⟩
  have hr' : Reachable (⟨walls kind ∪ reserved kind, goals⟩ : Board 81 107)
      (some 1) ⟨p, ∅⟩ ⟨q, ∅⟩ := hr.lift id hstep
  have hh := reachable_withFixed (B := board kind goals) hb hw hr'
  simpa only [withFixed, Finset.empty_union] using hh

/-- Walk from the exact gate hub to any exterior corner, keeping arbitrary rail boxes fixed. -/
theorem corner_reachable (kind : Bool) (i : Fin 4) (goals boxes : Finset C)
    (hb : boxes ⊆ reserved kind) (hw : Disjoint boxes (walls kind)) :
    Reachable (board kind goals) (some 1) ⟨hub, boxes⟩ ⟨corner i, boxes⟩ :=
  frame_walk kind goals boxes hb hw (corner_walk kind i)

/-- Return from any exterior corner to the exact gate hub with the same rail boxes. -/
theorem corner_to_hub (kind : Bool) (i : Fin 4) (goals boxes : Finset C)
    (hb : boxes ⊆ reserved kind) (hw : Disjoint boxes (walls kind)) :
    Reachable (board kind goals) (some 1) ⟨corner i, boxes⟩ ⟨hub, boxes⟩ :=
  frame_walk kind goals boxes hb hw (empty_symm (corner_walk kind i))

end PushPuzzle.PushFS.Gadgets.Gates
