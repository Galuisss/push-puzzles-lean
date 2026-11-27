/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog
public import PushFS.Gadgets.Wires.Soundness.Pair
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! Templates, strips and canonical geometry of the three horizontal glyphs. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Soundness

inductive HorizontalKind | straight | parity | flip
  deriving DecidableEq

instance : Fintype HorizontalKind where
  elems := {.straight,.parity,.flip}
  complete k := by cases k <;> simp

namespace HorizontalKind

def kind : HorizontalKind → Wires.Kind
  | .straight => .straight | .parity => .parity | .flip => .flip
abbrev width : HorizontalKind → ℕ | .straight => 45 | .parity => 64 | .flip => 25
abbrev count : HorizontalKind → ℕ | .straight => 18 | .parity => 26 | .flip => 9

def template : (k : HorizontalKind) → Template k.width 21 k.count
  | .straight => Straight.template | .parity => Parity.template | .flip => Flip.template

theorem checked (k : HorizontalKind) : k.template.Checked := by
  cases k
  · exact Straight.checked
  · exact Parity.checked
  · exact Flip.checked

def span : HorizontalKind → ℕ | .straight => 40 | .parity => 59 | .flip => 20

def first (k : HorizontalKind) : Fin k.count := ⟨0,by cases k <;> decide⟩
def last : (k : HorizontalKind) → Fin k.count
  | .straight => 17 | .parity => 25 | .flip => 8

def stripCount : HorizontalKind → ℕ | .straight => 4 | .parity => 5 | .flip => 2

/-- A literal sealed interval and its two bounding physical identities. -/
structure Strip (k : HorizontalKind) where
  lo : ℕ
  hi : ℕ
  left : Fin k.count
  right : Fin k.count

def strip : (k : HorizontalKind) → Fin k.stripCount → Strip k
  | .straight => ![⟨8,8,2,3⟩,⟨11,11,3,4⟩,⟨28,28,11,12⟩,⟨31,31,12,13⟩]
  | .parity => ![⟨8,8,2,3⟩,⟨11,11,3,4⟩,⟨28,28,11,12⟩,⟨31,31,12,13⟩,⟨44,46,18,19⟩]
  | .flip => ![⟨8,8,2,3⟩,⟨11,11,3,4⟩]

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Every pair of canonical physical slots lies in one actual horizontal static component. -/
theorem slots_component (k : HorizontalKind) (phase : Bool) (i j : Fin k.count) :
    SameComponent (k.template.board ∅) (k.template.position phase i) (k.template.position phase j) := by
  have check : ∀ (k : HorizontalKind) (phase : Bool) (i j : Fin k.count),
      Gates.staticRun k.template.wall (k.template.position phase i)
        (Template.slotDirections (k.template.position phase i) (k.template.position phase j)) =
          some (k.template.position phase j) := by decide +kernel
  exact ⟨Gates.staticRun_sound (k.template.wall_correct ∅) (check k phase i j),
    Gates.staticRun_sound (k.template.wall_correct ∅) (check k phase j i)⟩

theorem ordered (k : HorizontalKind) (phase : Bool) (i j : Fin k.count) (hij : i < j) :
    (k.template.position phase i).1.val < (k.template.position phase j).1.val := by
  cases k
  · exact Straight.ordered_slots phase i j hij
  · exact Parity.ordered_slots phase i j hij
  · exact Flip.ordered_slots phase i j hij

/-- Literal full-glyph walls, including every traversable flip and the parity strip. -/
theorem strip_walls (k : HorizontalKind) (i : Fin k.stripCount) :
    StripWalls (k.template.board ∅) (k.strip i).lo (k.strip i).hi 10 := by
  cases k <;> fin_cases i <;> refine ⟨?_,?_⟩ <;> decide +kernel

theorem strip_bounds (k : HorizontalKind) (i : Fin k.stripCount) :
    (k.strip i).hi < k.width ∧ (k.strip i).left < (k.strip i).right := by
  revert i
  cases k <;> decide +kernel

/-- Both complete canonical phases leave every literal strip logically open. -/
theorem strip_normal (k : HorizontalKind) (phase : Bool) (i : Fin k.stripCount) :
    (k.template.position phase (k.strip i).left).1.val+1 < (k.strip i).lo ∨
      (k.strip i).hi+1 < (k.template.position phase (k.strip i).right).1.val := by
  revert phase i
  cases k <;> decide +kernel

end HorizontalKind

end PushPuzzle.PushFS.Gadgets.Wires.Soundness
