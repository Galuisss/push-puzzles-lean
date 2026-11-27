/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.Data

/-! Standard-encoding machine polynomial time of the seven real fixed finite-cell glyphs. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog


open Turing.MultiTapeTM ComputableInPolyTime Reduction
open scoped Encoding Reduction.Bitmap

def Kind.code : Kind→ℕ
  | .east=>0 | .west=>1 | .south=>2 | .westSouth=>3 | .eastSouth=>4 | .southEast=>5 | .southWest=>6

def encKind : Kind↪List Bool := ⟨fun k=>encUnary k.code,by
  intro a b h
  have he:=encUnary.injective h
  cases a <;> cases b <;> simp_all only [Kind.code,reduceCtorEq] <;> omega⟩

namespace Bitmap

abbrev Args := Kind×Bool×Bool
abbrev encArgs : Args↪List Bool := encPair encKind (encPair encBool encBool)

def recipe (q : Args) : Reduction.Bitmap.Input := (atlas q.1 q.2.1 q.2.2).input

/-- Seven fixed real glyphs and their four phase assignments have a genuine finite-table machine. -/
theorem recipe_polyTime : ComputableInPolyTime recipe encArgs Reduction.Bitmap.encInput := of_finite _

/-- The emitted dense grid is exactly the semantic complete physical tile. -/
theorem data_eq (q : Args) : Encoding.data (puzzle q.1 q.2.1 q.2.2)=Reduction.Bitmap.emit (recipe q) :=
  (atlas q.1 q.2.1 q.2.2).data_eq

end Bitmap
end PushPuzzle.PushFS.Gadgets.Wires.Catalog
