/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushFS.Grid
public import Mathlib.Data.Finset.Basic
import Lean.Elab.Tactic.Omega

/-! Signed readout of the two-box, five-push three-port shuttle. -/

@[expose] public section
namespace PushPuzzle.PushS.Shuttle


/-- The left train is shortened by two cells for AND and four for OR. -/
inductive Kind
  | andGate | orGate
  deriving DecidableEq

def Kind.kappa : Kind → ℤ
  | .andGate => 2
  | .orGate => 4

/-- Signed short-train displacement and nonnegative outer hole counts. -/
structure Placement where
  left : ℕ
  right : ℕ
  short : ℤ

/-- Open cells between the left train and the two-box short train. -/
def Placement.leftGap (k : Kind) (a : Placement) (x : ℤ) : Prop :=
  (a.left : ℤ) - k.kappa + 1 ≤ x ∧ x ≤ a.short

/-- Open cells between the short train and the right train. -/
def Placement.rightGap (a : Placement) (x : ℤ) : Prop :=
  a.short + 3 ≤ x ∧ x ≤ 13 - (a.right : ℤ)

/-- A work-row sample lies in either of the two candidate gaps. -/
def Placement.hole (k : Kind) (a : Placement) (x : ℤ) : Prop :=
  a.leftGap k x ∨ a.rightGap x

/-- Nonoverlap allows the candidate gaps to be empty. -/
def Placement.Ordered (k : Kind) (a : Placement) : Prop :=
  (a.left : ℤ) - k.kappa ≤ a.short ∧ a.short ≤ 11 - (a.right : ℤ)

/-- The heavy output, left input and relay bits of the canonical target. -/
structure Target where
  heavy : Bool
  left : Bool
  relay : Bool

/-- Canonical placements use short-train positions one and six. -/
def Target.placement (t : Target) : Placement where
  left := if t.left then 1 else 2
  right := if t.relay then 1 else 2
  short := if t.heavy then 6 else 1

/-- Internal relay and AND conditions needed by the work-row readout. -/
def Target.Legal (k : Kind) (t : Target) : Prop :=
  (t.heavy = true → t.relay = true) ∧
  (k = .andGate → t.heavy = false → t.left = true)

/-- The eight fixed work-row samples used by the terminal certificate. -/
def probes : Finset ℤ := {-2, 0, 2, 4, 6, 8, 10, 12}

/-- Every work-row target hole at a sample position is present in the observed placement. -/
def Samples (k : Kind) (t : Target) (a : Placement) : Prop :=
  ∀ x ∈ probes, t.placement.hole k x → a.hole k x

/-- Work-row samples and outer-hole payments recover the target threshold bits and force
both candidate gaps to be nonempty. -/
theorem readout (k : Kind) (t : Target) (a : Placement)
    (hlegal : t.Legal k) (hordered : a.Ordered k) (hs : Samples k t a)
    (hl : t.left = false → 2 ≤ a.left) (hr : t.relay = false → 2 ≤ a.right) :
    (t.heavy = true ↔ 6 ≤ a.short) ∧ (t.left = true ↔ a.left ≤ 1) ∧
      (t.relay = true ↔ a.right ≤ 1) ∧
      (∃ x, a.leftGap k x) ∧ (∃ x, a.rightGap x) := by
  have hm2 := hs (-2) (by simp [probes])
  have h0 := hs 0 (by simp [probes])
  have h2 := hs 2 (by simp [probes])
  have h4 := hs 4 (by simp [probes])
  have h6 := hs 6 (by simp [probes])
  have h8 := hs 8 (by simp [probes])
  have h10 := hs 10 (by simp [probes])
  have h12 := hs 12 (by simp [probes])
  obtain ⟨heavy, left, relay⟩ := t
  cases k <;> cases heavy <;> cases left <;> cases relay <;>
    simp [Target.Legal, Target.placement, Placement.Ordered, Placement.hole,
      Placement.leftGap, Placement.rightGap, Kind.kappa]
      at hlegal hordered hm2 h0 h2 h4 h6 h8 h10 h12 hl hr ⊢ <;>
    refine ⟨by omega, by omega, by omega, ?_, ?_⟩ <;>
    first | exact ⟨0, by omega⟩ | exact ⟨2, by omega⟩ |
      exact ⟨8, by omega⟩ | exact ⟨12, by omega⟩

end PushPuzzle.PushS.Shuttle
