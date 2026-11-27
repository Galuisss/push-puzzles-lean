/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.Freeze
public import PushS.Labels

/-! The first-motion closure fixes each physical box identity in the anchored region. -/

@[expose] public section
namespace PushPuzzle.PushS.Freeze

open PushFS

variable {w h : ℕ} {ι : Type} [Fintype ι] {B : Board w h} {cap : Option ℕ}
  {d : Direction} {S T : LabelledState ι w h} {C G : Finset (Cell w h)}

/-- The region stays full and all its initial physical identities stay in place. -/
structure Frozen (C : Finset (Cell w h)) (S T : LabelledState ι w h) : Prop where
  full : C ⊆ T.state.boxes
  position : ∀ i, S.position i ∈ C → T.position i = S.position i

end PushPuzzle.PushS.Freeze
