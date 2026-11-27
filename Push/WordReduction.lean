/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.WordSourceSoundness

/-! The total standard polynomial-time reduction from the original fixed-alphabet word language to Push-*. -/

public section
namespace PushPuzzle.Push.WordSource

open Cslib.Complexity Turing.MultiTapeTM

variable {q : ℕ} (H : Digraph (Fin q)) [DecidableRel H.Adj] (hq : 0 < q)

include hq in
/-- The complete repaired physical reader is a standard polynomial-time many-one reduction to ordinary Push-*. -/
theorem polyTimeReducible_word :
    PolyTimeReducible (NCL.HWord.encInstance q) Push.encoding (NCL.HWord.language H) Push.solvable :=
  ⟨checkedCompile H hq, computableInPolyTime_checkedCompile H hq, checkedCompile_mem_iff H hq⟩

end PushPuzzle.Push.WordSource
