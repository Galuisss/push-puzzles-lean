/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.HWord.Strip.Metadata
public import PushS.Source.Strip.Sweep.Context.ProgramData

/-!
# Polynomial-time actual native strip compilation of word networks

The standard-data emitter returns exactly the same existing native context's instruction code.
Compose the fixed fourteen-cell expander and standard graph compiler. Their outputs are the
original actual strip word and native graph, with the established geometric and simulation
theorems unchanged.

## Main results

* `PushPuzzle.NCL.HWord.Strip.Sweep.programCode_eq`: exact actual source instruction stream.
* `PushPuzzle.NCL.HWord.Strip.Sweep.computableInPolyTime_program`: standard encoded actual word compilation.
* `PushPuzzle.NCL.HWord.Strip.Sweep.computableInPolyTime_graph`: standard encoded same native graph compilation.
-/

public section

namespace PushPuzzle.NCL.HWord.Strip.Sweep

open Cslib.Complexity Cslib.Complexity.NCL Cslib.Complexity.NCL.HWord Cslib _root_.Turing.MultiTapeTM

variable {q : ℕ} (H : Digraph (Fin q)) [DecidableRel H.Adj] (hq : 0 < q)

/-- The standard-data emitter returns the same actual original native instruction stream. -/
theorem programCode_eq (n : ℕ) :
    PushPuzzle.NCL.Strip.PolyTime.ProgramData.programCode (vertexBudget q) (edgeBudget q)
      (routingMetadata H hq n) = (context (n := n) H hq).programCode := by
  rw [routingMetadata_eq]
  exact (context H hq).programData_programCode

/-- The same original finite instruction stream emits in standard encoded polynomial time. -/
private theorem computableInPolyTime_programCode :
    ComputableInPolyTime (fun n => (context (n := n) H hq).programCode) encUnary
      PushPuzzle.NCL.Strip.Sweep.Cell.language.encProgram := by
  have h := (PushPuzzle.NCL.Strip.PolyTime.ProgramData.computableInPolyTime_programCode
    (vertexBudget q) (edgeBudget q)).comp (computableInPolyTime_routingMetadata H hq)
  exact h.of_enc_eq (fun n => congrArg PushPuzzle.NCL.Strip.Sweep.Cell.language.encProgram
    (programCode_eq H hq n).symm)

/-- The same actual standard planar strip word compiles in standard encoded polynomial time. -/
theorem computableInPolyTime_program :
    ComputableInPolyTime (fun n => program (n := n) H hq) encUnary NCL.encWord := by
  have h := PushPuzzle.NCL.Strip.Sweep.Cell.language.computableInPolyTime_expand.comp
    (computableInPolyTime_programCode H hq)
  exact h.of_enc_eq (fun n => congrArg NCL.encWord
    ((context (n := n) H hq).expand_programCode).symm)

/-- The same actual native graph compiles in polynomial time under the standard graph encoding.
-/
theorem computableInPolyTime_graph :
    ComputableInPolyTime (fun n => (program (n := n) H hq).compile) encUnary encAndOrGraph :=
  Word.computableInPolyTime_compile.comp (computableInPolyTime_program H hq)

end PushPuzzle.NCL.HWord.Strip.Sweep
