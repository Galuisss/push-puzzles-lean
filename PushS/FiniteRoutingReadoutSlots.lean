/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingOrientation
public import PushS.FiniteRoutingLineProgramReadout
public import PushS.FiniteRoutingTurnReadout

/-! Actual slot equalities recover shared identities and construct complete line/turn readout glyphs. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Gadgets.Wires.Soundness

variable {I : PushFS.Instance} {GlobalLabel : Type} [Fintype GlobalLabel]
    {M : SlotMatching I GlobalLabel} {A : ComponentTracks I}
    {S final : LabelledState GlobalLabel I.width I.height}

namespace Line.Readout.LineGlyph

/-- Actual source-slot equations already enforce injectivity, including both unowned interfaces. -/
def of_slots (w : ℕ) (hw : 2 ≤ w) (atoms : List Line.Atom) (above : Bool)
    (dx dy : ℕ) (fit_x : dx+Line.width w atoms ≤ I.width) (fit_y : dy+Line.height w ≤ I.height)
    (initial target : Bool) (labels : Line.Label w atoms → GlobalLabel)
    (sources : ∀ l, M.source (labels l) = (GridEmbedding.translate dx dy fit_x fit_y).cells (Line.cell w hw atoms initial l))
    (targets : ∀ l, M.target (labels l) = (GridEmbedding.translate dx dy fit_x fit_y).cells (Line.cell w hw atoms target l))
    (tracks : ∀ l, A.name (M.source (labels l)) = .horizontal (dy+FiniteTools.radius w))
    (walls : ∀ p ∈ Line.walls w atoms above, (GridEmbedding.translate dx dy fit_x fit_y).cells p ∈ I.board.walls)
    (floor : ∀ i, (GridEmbedding.translate dx dy fit_x fit_y).cells (Line.Readout.rail w atoms i) ∉ I.board.walls) :
    Line.Readout.LineGlyph M A w atoms above where
  hw := hw
  dx := dx
  dy := dy
  fit_x := fit_x
  fit_y := fit_y
  initialPhase := initial
  targetPhase := target
  labels := ⟨labels, by
    intro i j he
    have hs := congrArg (fun l => M.source l) he
    rw [sources,sources] at hs
    exact Line.cell_injective w hw atoms initial ((GridEmbedding.translate dx dy fit_x fit_y).cells.injective hs)⟩
  sources := sources
  targets := targets
  tracks := tracks
  walls := walls
  railFloor := floor

end Line.Readout.LineGlyph

namespace Turn.Readout.TurnGlyph

/-- The two real turn slot equations enforce distinct physical F and G identities. -/
def of_slots (w : ℕ) (hw : 2 ≤ w) (dx dy : ℕ)
    (fit_x : dx+FiniteTools.side w ≤ I.width) (fit_y : dy+FiniteTools.side w ≤ I.height)
    (initial target : Bool) (labels : Fin 2 → GlobalLabel)
    (sources : ∀ l, M.source (labels l) = (GridEmbedding.translate dx dy fit_x fit_y).cells (Turn.cell w initial l))
    (targets : ∀ l, M.target (labels l) = (GridEmbedding.translate dx dy fit_x fit_y).cells (Turn.cell w target l))
    (horizontalTag : A.name (M.source (labels 0)) = .horizontal (dy+FiniteTools.radius w))
    (verticalTag : A.name (M.source (labels 1)) = .vertical (dx+FiniteTools.radius w))
    (cornerTag : A.name ((GridEmbedding.translate dx dy fit_x fit_y).cells (Turn.center w)) =
      .sink (dx+FiniteTools.radius w) (dy+FiniteTools.radius w))
    (walls : ∀ p ∈ FiniteTools.turnWalls w, (GridEmbedding.translate dx dy fit_x fit_y).cells p ∈ I.board.walls) :
    Turn.Readout.TurnGlyph M A w where
  hw := hw
  dx := dx
  dy := dy
  fit_x := fit_x
  fit_y := fit_y
  initialPhase := initial
  targetPhase := target
  labels := ⟨labels, by
    intro i j he
    have hs := congrArg (fun l => M.source l) he
    rw [sources,sources] at hs
    exact Turn.cell_injective w initial ((GridEmbedding.translate dx dy fit_x fit_y).cells.injective hs)⟩
  sources := sources
  targets := targets
  horizontalTag := horizontalTag
  verticalTag := verticalTag
  cornerTag := cornerTag
  walls := walls

end Turn.Readout.TurnGlyph
end PushPuzzle.PushS.FiniteRouting
