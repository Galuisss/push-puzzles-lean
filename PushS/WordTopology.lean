/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.WordSource
public import PushS.CombSourceNoncrossing
import all PushS.CombSourceNoncrossing

/-! Complete actual two-page geometry of the original fixed-alphabet source compiler. -/

public section
namespace PushPuzzle.PushS

open Cslib.Complexity

/-- The same original valid strip graph and drawing emit a complete valid actual port layout. -/
theorem StripSource.layout_valid {width span : ℕ} {x : StripSource.Instance}
    (hg : NCL.SourceValid x.ncl.graph) (hd : PushPuzzle.NCL.StripAndOrNCL.ValidDrawing width span x) :
    (StripSource.layout width x).pages.Valid := by
  obtain ⟨P, _, hp, ⟨height, hfit⟩, _, hhead⟩ := StripSource.valid_drawing hg hd
  exact Comb.compile_pages_valid_of_native width hg P hp height hfit hhead

namespace WordSource

variable {q : ℕ} (H : Digraph (Fin q)) [DecidableRel H.Adj] (hq : 0 < q)

/-- Every word's original native planar drawing gives its genuine complete valid two-page layout. -/
theorem layout_pages_valid (x : NCL.HWord.Instance q) :
    (StripSource.layout (PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q) (native H hq x)).pages.Valid :=
  StripSource.layout_valid (width := PushPuzzle.NCL.HWord.Strip.Sweep.drawingWidth q)
    (span := PushPuzzle.NCL.HWord.Strip.Sweep.drawingSpan q) (x := native H hq x)
    (native_valid H hq x) (native_validDrawing H hq x)

end WordSource
end PushPuzzle.PushS
