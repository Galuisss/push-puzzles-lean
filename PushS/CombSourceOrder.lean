/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombUpperPartition

/-! The actual contour word of source-fragment ends, before local rotation ears. -/

public section
namespace PushPuzzle.PushS.Comb


/-- Retain the original native tips and crossing ends of genuine source fragments. -/
@[expose] def Token.isSource : Token → Bool
  | .tip .. | .mark .. => true
  | .rotation .. => false

/-- The original compiled contour with only its local rotation ears removed. -/
@[expose] def sourceOrder (width : ℕ) (input : Input) : List Token :=
  (cut width input).order.filter Token.isSource

/-- The actual successive source-fragment ends in the original reference route orders. -/
@[expose] def sourcePairs (width : ℕ) (input : Input) : List (Token × Token) :=
  input.drawing.2.zipIdx.flatMap fun re => pairOff (edgeVisits width input.drawing re.2)

/-- The two ends of distinct actual source fragments do not alternate in the original contour.
-/
@[expose] def SourceNoncrossing (width : ℕ) (input : Input) : Prop :=
  let rank := (sourceOrder width input).idxOf
  ∀ p ∈ sourcePairs width input, ∀ q ∈ sourcePairs width input,
    ¬(min (rank p.1) (rank p.2) < min (rank q.1) (rank q.2) ∧
      min (rank q.1) (rank q.2) < max (rank p.1) (rank p.2) ∧
      max (rank p.1) (rank p.2) < max (rank q.1) (rank q.2))

end PushPuzzle.PushS.Comb
