/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.ShortCorners.Plain
public import PushFS.Gadgets.Wires.ShortCorners.In
public import PushFS.Gadgets.Wires.ShortCorners.Both
public import PushFS.Gadgets.Wires.Catalog.ImageSignals

/-! Four finite true corner wall types, with every helper box, executable macro and allowed physical neighbor. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.ShortCorners


inductive Kind | plain | outFlip | inFlip | both
  deriving DecidableEq

instance : Fintype Kind where
  elems:={.plain,.outFlip,.inFlip,.both}
  complete k:=by cases k <;> simp

def width : Kind→ℕ
  | .plain | .outFlip=>45
  | .inFlip | .both=>63

def height : Kind→ℕ
  | .plain | .inFlip=>44
  | .outFlip | .both=>64

def count : Kind→ℕ
  | .plain=>29
  | .outFlip | .inFlip=>38
  | .both=>47

def template : (k : Kind)→Template (width k) (height k) (count k)
  | .plain=>Plain.template
  | .outFlip=>Out.template
  | .inFlip=>In.template
  | .both=>Both.template

theorem checked (k : Kind) : (template k).Checked := by
  cases k
  · exact Plain.checked
  · exact Out.checked
  · exact In.checked
  · exact Both.checked

def puzzle (k : Kind) (a b : Bool) : Instance := (checked k).storageInstance a b

def slotMatching (k : Kind) (a b : Bool) : SlotMatching (puzzle k a b) (Fin (count k)) :=
  (checked k).slotMatching a b

def first (k : Kind) : Fin (count k) := ⟨0,by cases k <;> decide⟩
def last (k : Kind) : Fin (count k) := ⟨count k-1,by cases k <;> decide⟩

def sourceX : Kind→ℕ
  | .plain | .outFlip=>40
  | .inFlip | .both=>60

def lastY : Kind→ℕ
  | .plain | .inFlip=>39
  | .outFlip | .both=>59

/-- Source and destination anchors use the exact true first/last box and the same end/start gap convention. -/
theorem endpoints (k : Kind) : ∀a : Bool,
    ((template k).position a (first k)).1.val+a.toNat=sourceX k ∧
    ((template k).position a (first k)).2.val=10 ∧
    ((template k).position a (last k)).1.val=10 ∧
    ((template k).position a (last k)).2.val=lastY k+a.toNat := by
  cases k <;> decide +kernel

end PushPuzzle.PushFS.Gadgets.Wires.ShortCorners
