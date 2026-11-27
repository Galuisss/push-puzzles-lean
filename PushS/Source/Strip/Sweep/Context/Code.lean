/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.Context
public import PushS.Source.Strip.Sweep.ProgramCode
public import PushS.Source.Strip.Sweep.FrontierData

/-!
# Exact standard encoded stages of the native strip program

The native source context supplies the same actual carrier records to the polynomial-time
fixed-key frontier scan and the same actual selected instruction stream to the polynomial-time
fixed-fragment compiler. Both computed stages agree exactly with the existing strip program.

## Main definitions

* `PushPuzzle.NCL.Strip.Sweep.Context.programCode`: the actual selected standard encoded instruction stream.

## Main results

* `PushPuzzle.NCL.Strip.Sweep.Context.frontier_eq_scan`: exact actual carrier-record frontier computation.
* `PushPuzzle.NCL.Strip.Sweep.Context.compile_programCode`: same actual native graph from the fixed compiler.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep.Context

open Cslib.Complexity Cslib.Complexity.NCL Cslib

variable {A K : ℕ} (C : Context A K)

/-- Compute the same actual native frontier with the standard encoded fixed-key record scan. -/
theorem frontier_eq_scan (t : ℤ) : C.frontier t =
    PushPuzzle.NCL.Strip.Sweep.FrontierData.scan (2 * height K + 1)
      (PushPuzzle.NCL.Strip.Sweep.FrontierData.entries C.environment (List.finRange C.source.edgeCount) t) :=
  (PushPuzzle.NCL.Strip.Sweep.FrontierData.scan_entries C.environment (List.nodup_finRange _) t).symm

/-- The same native source's actual selected offsets and finite cell codes. -/
@[expose] def programCode : PushPuzzle.NCL.Strip.Sweep.Cell.language.Program :=
  PushPuzzle.NCL.Strip.Sweep.programCode C.environment C.graph C.arity C.color
    (List.finRange C.vertices.length) (List.finRange C.source.edgeCount)

/-- The standard fixed-table expander returns the same actual native strip word. -/
theorem expand_programCode : PushPuzzle.NCL.Strip.Sweep.Cell.language.expand C.programCode = C.program :=
  PushPuzzle.NCL.Strip.Sweep.expand_programCode _ _ _ _ _ _

/-- The standard polynomial-time fixed-table compiler returns the same actual native strip graph.
-/
theorem compile_programCode : PushPuzzle.NCL.Strip.Sweep.Cell.language.compile C.programCode = C.program.compile :=
  PushPuzzle.NCL.Strip.Sweep.compile_programCode _ _ _ _ _ _

end PushPuzzle.NCL.Strip.Sweep.Context
