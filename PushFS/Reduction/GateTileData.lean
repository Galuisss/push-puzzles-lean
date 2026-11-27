/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.VertexTable
public import PushFS.Reduction.GateAnnulus
public import PushFS.Reduction.GateLeadStorage
import Mathlib.Data.List.GetD
import Mathlib.Tactic.FinCases

/-! Actual source vertex records select finite physical gate states and their complete annular routes. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction

open Cslib.Complexity.NCL Plan Turing.MultiTapeTM ComputableInPolyTime
open scoped PushPuzzle.PushFS.Reduction PushPuzzle.PushFS.Reduction.Plan

/-- The full finite input for an unrotated core and its three annular arms. -/
structure GateTileState where
  core : GateState
  incoming : Gadgets.Gates.Signals
  pattern : Fin 3
  rotation : Fin 3
  deriving DecidableEq, Fintype

enc_structure encGateTileState : GateTileState where
  core : encGateState, incoming : encSignals, pattern : encRole, rotation : encRole

/-- Select actual core flags, source-star pattern and cyclic port matching from a real source record. -/
def gateTileState (q : VertexData × (List Bool × List Bool)) : GateTileState :=
  ⟨⟨q.1.ports.isAND,gateSignals (q.1.ports,q.2.1),gateSignals (q.1.ports,q.2.2)⟩,
    ⟨q.1.ports.left.dir,q.1.ports.upper.dir,q.1.ports.output.dir⟩,
    q.1.annulus.1,q.1.annulus.2⟩

@[fun_prop] theorem gateTileState_polyTime :
    ComputableInPolyTime gateTileState
      (encPair encVertexData (encPair (encList encBool) (encList encBool))) encGateTileState := by
  have hgs := gateSignals_polyTime
  unfold gateTileState
  fun_prop

/-- Choose one of the checked physical arm programs using exactly this source's finite metadata. -/
def GateTileState.key (g : GateTileState) (role : Fin 3) : GateAnnulus.Key :=
  (g.core.isAND,g.pattern,g.rotation,role)

def GateTileState.route (g : GateTileState) (role : Fin 3) : List Segment := GateAnnulus.route (g.key role)

/-- The parity bit is exactly the original normalized source port's reference direction. -/
theorem gateTileState_incoming (v : VertexData) (a b : List Bool) (role : Fin 3) :
    (gateTileState (v,(a,b))).incoming.get role=(v.ports.port role).dir := by
  fin_cases role <;> rfl

end PushPuzzle.PushFS.Reduction
