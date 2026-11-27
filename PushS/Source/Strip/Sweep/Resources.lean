/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Typing

/-!
# Actual word resources inside one strip scan cell

Count the newly created wires of the actual emitted word. A local prefix can increase its stack
by at most this count. Prefix stack bounds compose at their actual checked colored interfaces.

## Main definitions

* `PushPuzzle.NCL.Slice.outputCount`, `PushPuzzle.NCL.Word.outputCount`: actual newly created wire counts.
* `PushPuzzle.NCL.Word.WidthBound`: a uniform bound on all actually checked prefix stacks.

## Main results

* `PushPuzzle.NCL.Word.typeRun_length_le`: stack growth is bounded by actual created wires.
* `PushPuzzle.NCL.Word.WidthBound.append`: local stack bounds compose at the actual intermediate interface.
* `PushPuzzle.NCL.Diagram.outputCount_toWord`: the actual count is the diagram's actual inner-edge count.
-/

public section

namespace PushPuzzle.NCL

open Cslib.Complexity Cslib.Complexity.NCL Cslib

open scoped List

/-- The actual number of newly created wires in one word layer. -/
@[expose] def Slice.outputCount : Slice → ℕ
  | .gen _ _ b _ => b.length
  | .swap _ => 0

/-- The actual total number of newly created wires in a word. -/
@[expose] def Word.outputCount (w : Word) : ℕ := (w.map PushPuzzle.NCL.Slice.outputCount).sum

/-- Creation counts add under actual word concatenation. -/
private theorem Word.outputCount_append (u v : Word) :
    (PushPuzzle.NCL.Word.outputCount (u ++ v)) = (PushPuzzle.NCL.Word.outputCount u) + (PushPuzzle.NCL.Word.outputCount v) := by
  simp [outputCount]

private theorem Slice.typeRun_length_le {sl : Slice} {a b : List Color}
    (h : sl.typeRun a = some b) : b.length ≤ a.length + (PushPuzzle.NCL.Slice.outputCount sl) := by
  cases sl with
  | gen k x y vs =>
    simp only [Slice.typeRun] at h
    split_ifs at h with hc
    · have hb := Option.some.inj h
      subst b
      simp only [List.length_append, List.length_take, List.length_drop, PushPuzzle.NCL.Slice.outputCount]
      omega
  | swap k =>
    simp only [Slice.typeRun] at h
    split at h <;> try contradiction
    next x y hx hy =>
      obtain ⟨hk, _⟩ := List.getElem?_eq_some_iff.mp hy
      have hb := Option.some.inj h
      subst b
      simp only [List.length_append, List.length_take, List.length_drop, List.length_cons,
        List.length_nil, PushPuzzle.NCL.Slice.outputCount]
      omega

/-- An actual checked word can increase the color stack by at most its created wires. -/
theorem Word.typeRun_length_le {w : Word} {a b : List Color} (h : w.WellTyped a b) :
    b.length ≤ a.length + (PushPuzzle.NCL.Word.outputCount w) := by
  induction w generalizing a with
  | nil =>
    have hab : a = b := Option.some.inj h
    subst b
    simp [outputCount]
  | cons sl w ih =>
    change (sl.typeRun a).bind (Word.typeRun w) = some b at h
    cases ht : sl.typeRun a with
    | none => simp only [ht, Option.bind_none] at h; cases h
    | some c =>
      have hw : Word.WellTyped w c b := by
        change Word.typeRun w c = some b
        simpa only [ht, Option.bind_some] using h
      have h₁ := PushPuzzle.NCL.Slice.typeRun_length_le ht
      have h₂ := ih hw
      simp only [outputCount, List.map_cons, List.sum_cons]
      dsimp only [outputCount] at h₂
      omega

/-- All actually checked prefixes have stacks of at most `bound` wires. -/
@[expose] def Word.WidthBound (w : Word) (a : List Color) (bound : ℕ) : Prop :=
  ∀ u : Word, u <+: w → ∀ b, u.WellTyped a b → b.length ≤ bound

/-- A word's actual output count gives a bound for every one of its checked prefix stacks. -/
theorem Word.widthBound_outputCount (w : Word) (a : List Color) :
    (PushPuzzle.NCL.Word.WidthBound w) a (a.length + (PushPuzzle.NCL.Word.outputCount w)) := by
  intro u hu b ht
  obtain ⟨v, rfl⟩ := hu
  have h := typeRun_length_le ht
  rw [outputCount_append]
  omega

/-- A larger budget bounds the same actual prefix stacks. -/
theorem Word.WidthBound.mono {w : Word} {a : List Color} {m n : ℕ}
    (h : (PushPuzzle.NCL.Word.WidthBound w) a m) (hmn : m ≤ n) : (PushPuzzle.NCL.Word.WidthBound w) a n :=
  fun u hu b ht => (h u hu b ht).trans hmn

/-- The initial actual colored boundary satisfies every prefix width bound. -/
theorem Word.WidthBound.start {w : Word} {a : List Color} {n : ℕ}
    (h : (PushPuzzle.NCL.Word.WidthBound w) a n) : a.length ≤ n := h [] ⟨w, rfl⟩ a rfl

/-- The final actual colored boundary satisfies the same prefix width bound. -/
theorem Word.WidthBound.finish {w : Word} {a b : List Color} {n : ℕ}
    (h : (PushPuzzle.NCL.Word.WidthBound w) a n) (ht : w.WellTyped a b) : b.length ≤ n :=
  h w (List.prefix_refl _) b ht

/-- Removing an actually checked initial word preserves the bound on all remaining prefixes. -/
theorem Word.WidthBound.of_append_right {u v : Word} {a b : List Color} {n : ℕ}
    (h : (PushPuzzle.NCL.Word.WidthBound (u ++ v)) a n) (ht : u.WellTyped a b) : (PushPuzzle.NCL.Word.WidthBound v) b n := by
  intro p hp c hc
  apply h (u ++ p) ((List.prefix_append_right_inj u).mpr hp) c
  rw [Word.WellTyped, Cslib.Complexity.NCL.Word.typeRun_append, ht, Option.bind_some]
  exact hc

/-- Stack bounds compose using the actual checked intermediate colored boundary. -/
theorem Word.WidthBound.append {u v : Word} {a b : List Color} {n : ℕ}
    (hu : (PushPuzzle.NCL.Word.WidthBound u) a n) (hv : (PushPuzzle.NCL.Word.WidthBound v) b n) (ht : u.WellTyped a b) :
    (PushPuzzle.NCL.Word.WidthBound (u ++ v)) a n := by
  intro p hp c hc
  rcases List.prefix_or_prefix_of_prefix hp (List.prefix_append u v) with hpu | hup
  · exact hu p hpu c hc
  · obtain ⟨r, hr⟩ := hup
    have hrv : r <+: v := (List.prefix_append_right_inj u).mp (hr ▸ hp)
    have hrc : Word.WellTyped r b c := by
      rw [← hr, Word.WellTyped, Cslib.Complexity.NCL.Word.typeRun_append, ht, Option.bind_some] at hc
      exact hc
    exact hv r hrv c hrc

namespace Diagram

open Cslib.Complexity Cslib.Complexity.NCL Cslib.Complexity.NCL.Diagram

variable {Γ : List Color → List Color → Type} (I : Interp Γ)

/-- Word offset changes retain the actual number of emitted layers. -/
theorem length_toWord_offset {a b : List Color} (D : Diagram Γ a b) (k l : ℕ) :
    (D.toWord I k).length = (D.toWord I l).length := by
  induction D generalizing k l with
  | gen _ | id _ | swap _ _ => rfl
  | comp _ _ ih₁ ih₂ | tensor _ _ ih₁ ih₂ =>
    simp only [toWord, List.length_append, ih₁ _ 0, ih₂ _ 0]

/-- The emitted word's actual created wires are precisely the diagram's actual inner edges. -/
theorem outputCount_toWord {a b : List Color} (D : Diagram Γ a b) (k : ℕ) :
    (PushPuzzle.NCL.Word.outputCount (D.toWord I k)) = D.innerCount := by
  induction D generalizing k with
  | gen _ | id _ | swap _ _ => rfl
  | comp _ _ ih₁ ih₂ | tensor _ _ ih₁ ih₂ =>
    simp only [toWord, PushPuzzle.NCL.Word.outputCount_append, ih₁, ih₂, innerCount]

end Diagram
end PushPuzzle.NCL
