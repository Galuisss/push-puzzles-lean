/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.GateLeadAmbientWalking
public import PushFS.Gadgets.Wires.Polyline.Endpoints
import Mathlib.Tactic.FinCases

/-! Exact exposed identities and seam anchors of the complete three-lead gate. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateLead


open Gadgets Gadgets.Wires Gadgets.Wires.Polyline

/-- The true original physical identity at the exposed end of one of the three long leads. -/
def boundaryLabel (kind : Bool) (n : ℕ) (hn : 2301≤n) (i : Fin 3) :
    (j : Fin 4) × Labels kind n j :=
  if i=0 then ⟨1,ChainEnds.last n hn⟩
  else if i=1 then ⟨2,ChainEnds.last n hn⟩ else ⟨3,ChainEnds.last n hn⟩

/-- The semantic end anchor lies two travel units beyond the false-phase exposed box. -/
def portAnchor (kind : Bool) (n : ℕ) (i : Fin 3) : C n :=
  if i=0 then (⟨if kind then 10 else 11,by cases kind <;> simp⟩,
    ⟨n+20+(if kind then 29 else 90),by cases kind <;> simp <;> omega⟩)
  else if i=1 then (⟨n+10+(if kind then 43 else 44),by cases kind <;> simp <;> omega⟩,⟨21,by omega⟩)
  else (⟨2*n+(if kind then 90 else 89),by cases kind <;> simp⟩,⟨n+110,by omega⟩)

end PushPuzzle.PushFS.Reduction.GateLead
