/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.Plan
public import PushFS.Reduction.Bitmap
public import PushFS.Gadgets.Gates.StaticSlots
public import PushFS.Gadgets.Gates.Triggers
public import CslibFrontier.Computability.Complexity.Problems.NCL.Instance.Step
import Mathlib.Tactic.DeriveFintype

/-!
# Binding physical gate flags to the numbered NCL source

The two input flags read inward port directions; the right flag reads outward.
For every actual source vertex, the canonical physical flags satisfy exactly its
weighted NCL constraint. The complete finite wall/box/goal bitmap is emitted by
a polynomial-time finite lookup, including all 108 or 78 physical boxes.
-/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction


open Turing.MultiTapeTM ComputableInPolyTime
open Gadgets
open scoped NCL

deriving instance Fintype for Gates.Signals

/-- The two inward flags and the outward flag, with Boolean pair framing. -/
enc_structure encSignals : Gates.Signals where
  left : encBool, upper : encBool, right : encBool

/-- Read the source's real orientation bits in the physical port convention. -/
def OrderedPorts.signals (p : OrderedPorts) (s : ℕ → Bool) : Gates.Signals :=
  ⟨decide (p.left.In s), decide (p.upper.In s), !(decide (p.output.In s))⟩

/-- Read the flags directly from the given list of orientation bits. -/
def gateSignals (q : OrderedPorts × List Bool) : Gates.Signals :=
  q.1.signals (fun e => q.2.getD e false)

/-- Physical AND/OR legality is exactly weighted inflow for the bound ports. -/
theorem legal_signals_iff (p : OrderedPorts) (s : ℕ → Bool) :
    Gates.legal p.isAND (p.signals s) ↔ p.vertex.Sat s := by
  by_cases ha : p.left.In s <;> by_cases hb : p.upper.In s <;> by_cases hc : p.output.In s <;>
    cases hk : p.isAND <;>
    simp [Gates.legal, OrderedPorts.signals, OrderedPorts.vertex, NCL.Vertex.sat_and,
      NCL.Vertex.sat_or, ha, hb, hc, hk]

@[fun_prop] theorem gateSignals_polyTime :
    ComputableInPolyTime gateSignals (encPair encOrderedPorts (encList encBool)) encSignals := by
  have hget : ComputableInPolyTime (fun q : List Bool × ℕ => q.1.getD q.2 false)
      (encPair (encList encBool) encNat) encBool := listGetD_binary false (by fun_prop) (by fun_prop)
  unfold gateSignals OrderedPorts.signals NCL.Port.In
  fun_prop

/-- The fixed finite data needed to choose a gate's full initial and target bitmaps. -/
structure GateState where
  /-- Gate kind: AND or OR. -/
  isAND : Bool
  /-- Initial canonical port flags. -/
  initial : Gates.Signals
  /-- Target canonical port flags. -/
  target : Gates.Signals
  deriving DecidableEq, Fintype

/-- Gate kind followed by both complete three-flag assignments. -/
enc_structure encGateState : GateState where
  isAND : encBool, initial : encSignals, target : encSignals

end PushPuzzle.PushFS.Reduction
