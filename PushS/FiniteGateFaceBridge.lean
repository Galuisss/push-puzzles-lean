/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateFaceGeometry
public import PushS.FiniteRoutingLineFrame
import Mathlib.Tactic.FinCases

/-! Gate-face access through the literal first B-line and its mandatory flip crossing. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGateFaceBridge

open PushFS FiniteGeometry FiniteGateFaceGeometry FiniteGateMacros FiniteGateState
open FiniteGateAStraight FiniteGateVertical FiniteGateInputs FiniteGateOutputs
open FiniteGateBTemporary FiniteGatePlacedContract

variable {W H : ℕ}

attribute [local irreducible] FiniteGeometry.side FiniteRouting.Line.width FiniteRouting.Line.height

/-- Two literal clear gate corridors, with the intervening B-line crossing on the same full stock. -/
structure Access (w : ℕ) (kind : Bool) (e : GridEmbedding (side w) (side w) W H)
    (B : Board W H) (stock : Finset (Cell W H)) : Prop where
  left : FiniteWireFrame.Frame (leftStrip w kind) e B stock
  right : FiniteWireFrame.Frame (rightStrip w kind) e B stock
  cross : Reachable B (some 1) ⟨e.cells (dock w kind true),stock⟩ ⟨e.cells (dock w kind false),stock⟩
  cross_reverse : Reachable B (some 1) ⟨e.cells (dock w kind false),stock⟩ ⟨e.cells (dock w kind true),stock⟩

namespace Access

variable {w : ℕ} {kind : Bool} {e : GridEmbedding (side w) (side w) W H}
    {B : Board W H} {stock : Finset (Cell W H)}

/-- Real walking from any left mouth to any right mouth through the actual flip crossing. -/
theorem left_right (A : Access w kind e B stock) (p q : Cell (side w) (side w))
    (hp : p ∈ leftStrip w kind) (hq : q ∈ rightStrip w kind) :
    Reachable B (some 1) ⟨e.cells p,stock⟩ ⟨e.cells q,stock⟩ :=
  (left_walk_ambient w kind e A.left p _ hp (dock_left_mem w kind)).trans
    (A.cross.trans (right_walk_ambient w kind e A.right _ q (dock_right_mem w kind) hq))

/-- The opposite traversal uses the same concrete corridor frames and actual crossing. -/
theorem right_left (A : Access w kind e B stock) (p q : Cell (side w) (side w))
    (hp : p ∈ rightStrip w kind) (hq : q ∈ leftStrip w kind) :
    Reachable B (some 1) ⟨e.cells p,stock⟩ ⟨e.cells q,stock⟩ :=
  (right_walk_ambient w kind e A.right p _ hp (dock_right_mem w kind)).trans
    (A.cross_reverse.trans (left_walk_ambient w kind e A.left _ q (dock_left_mem w kind) hq))

end Access

end PushPuzzle.PushS.FiniteGateFaceBridge
