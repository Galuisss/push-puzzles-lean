/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.Emission
public import PushS.Source.Strip.Sweep.Cell.Code

/-!
# Actual finite instruction stream of the strip sweep

Encode each instruction selected by the same original grid scan with its actual offset and
finite cell code. The standard fixed-fragment expander and graph compiler return exactly the
same existing strip word and native graph.

## Main definitions

* `PushPuzzle.NCL.Strip.Sweep.programCode`: the actual selected finite instruction stream.

## Main results

* `PushPuzzle.NCL.Strip.Sweep.expand_programCode`: exact word agreement with the original actual emission.
* `PushPuzzle.NCL.Strip.Sweep.compile_programCode`: exact native graph agreement.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep

open Cslib.Complexity Cslib.Complexity.NCL Cslib

variable {V E : Type*} {A K : ℕ} (R : Environment V E A K)

/-- The same actual selected grid instructions, serialized as offsets and finite cell codes. -/
@[expose] def programCode (G : ConstraintGraph V E) (h3 : ∀ v, (G v).ports.length = 3)
    (color : E → Color) (vs : List V) (es : List E) : PushPuzzle.NCL.Strip.Sweep.Cell.language.Program :=
  (List.range (scanLength R es)).flatMap fun (i : ℕ) =>
    (instruction R G h3 color vs es (scanPoint K i)).toList.map
      (fun ins => (ins.offset, ins.fragment.code))

/-- Standard fixed-table expansion gives the same actual emitted strip word. -/
theorem expand_programCode (G : ConstraintGraph V E) (h3 : ∀ v, (G v).ports.length = 3)
    (color : E → Color) (vs : List V) (es : List E) :
    PushPuzzle.NCL.Strip.Sweep.Cell.language.expand (programCode R G h3 color vs es) = program R G h3 color vs es := by
  simp only [Word.Fixed.Language.expand, programCode, program, stepWord, List.flatMap_assoc,
    List.flatMap_map, PushPuzzle.NCL.Strip.Sweep.Cell.word_code]

/-- The standard polynomial-time fixed-table compiler gives the same actual native strip graph.
-/
theorem compile_programCode (G : ConstraintGraph V E) (h3 : ∀ v, (G v).ports.length = 3)
    (color : E → Color) (vs : List V) (es : List E) :
    PushPuzzle.NCL.Strip.Sweep.Cell.language.compile (programCode R G h3 color vs es) =
      (program R G h3 color vs es).compile := by
  rw [Word.Fixed.Language.compile_eq_expand, expand_programCode]

end PushPuzzle.NCL.Strip.Sweep
