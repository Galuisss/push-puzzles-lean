/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.AxisTracks
public import PushFS.Gadgets.Gates.StaticSlots

/-!
# Finite wall-only displacement certificates

The checker visits selected source cells and four directions. Its exact
reflection theorem covers every static displacement, checking source, support
and destination floor. No player access or box-state enumeration is involved.
-/

@[expose] public section

namespace PushPuzzle.PushFS


open Gadgets

variable {w h : ℕ}

/-- The executable wall stencil also detects every semantic static displacement. -/
private theorem staticStep_complete {wall : Cell w h → Bool} {B : Board w h}
    (hw : ∀ p, wall p = true ↔ p ∈ B.walls) {d : Direction} {rear p q : Cell w h}
    (hp : p ∉ B.walls) (hr : Adjacent d rear p) (hq : Adjacent d p q)
    (hrw : rear ∉ B.walls) (hqw : q ∉ B.walls) : Gates.staticStep wall d p = some q := by
  have hf (r : Cell w h) (hr : r ∉ B.walls) : wall r = false :=
    Bool.eq_false_iff.mpr (fun h => hr ((hw r).mp h))
  simp [Gates.staticStep, neighbor_complete hq, neighbor_complete hr.reverse,
    hf p hp, hf rear hrw, hf q hqw]

theorem displacement_iff_staticStep {wall : Cell w h → Bool} {B : Board w h}
    (hw : ∀ p, wall p = true ↔ p ∈ B.walls) (p q : Cell w h) :
    Displacement B p q ↔ ∃ d, Gates.staticStep wall d p = some q := by
  constructor
  · rintro ⟨hp, d, rear, hr, hq, hrw, hqw⟩
    exact ⟨d, staticStep_complete hw hp hr hq hrw hqw⟩
  · rintro ⟨_, hd⟩
    exact Gates.staticStep_sound hw hd

/-- Check every outgoing stencil of a selected finite source set. -/
def checkDisplacements (wall : Cell w h → Bool) (sources : Finset (Cell w h))
    (allowed : Cell w h → Cell w h → Bool) : Bool :=
  @decide (∀ p ∈ sources, ∀ d : Direction,
    (Gates.staticStep wall d p).elim true (allowed p) = true) Finset.decidableDforallFinset

/-- The finite checker is equivalent to the complete semantic outgoing-edge classification. -/
theorem checkDisplacements_correct {wall : Cell w h → Bool} {B : Board w h}
    (hw : ∀ p, wall p = true ↔ p ∈ B.walls) (sources : Finset (Cell w h))
    (allowed : Cell w h → Cell w h → Bool) :
    checkDisplacements wall sources allowed = true ↔
      ∀ p ∈ sources, ∀ q, Displacement B p q → allowed p q = true := by
  simp only [checkDisplacements, decide_eq_true_eq]
  constructor
  · intro hc p hp q hd
    obtain ⟨d, hd⟩ := (displacement_iff_staticStep hw p q).mp hd
    simpa only [hd, Option.elim_some] using hc p hp d
  · intro hc p hp d
    cases he : Gates.staticStep wall d p with
    | none => rfl
    | some q => exact hc p hp q (Gates.staticStep_sound hw he)

namespace AxisTrack

/-- The ordinary same-name-or-increasing-level condition, in executable form. -/
def allowed (name : Cell w h → AxisTrack) (p q : Cell w h) : Bool :=
  decide (name p = name q ∨ (name p).level < (name q).level)

/-- A stronger relation for rotatable line/turn tiles: stay on the same rail or enter a sink. -/
def strongAllowed (name : Cell w h → AxisTrack) (p q : Cell w h) : Bool :=
  decide (name p = name q) || match name p, name q with
    | .horizontal _, .sink _ _ | .vertical _, .sink _ _ => true
    | _, _ => false

theorem allowed_of_strong {name : Cell w h → AxisTrack} {p q : Cell w h}
    (hs : strongAllowed name p q = true) : allowed name p q = true := by
  cases hp : name p <;> cases hq : name q <;>
    simp_all [strongAllowed, allowed, AxisTrack.level]

/-- A direct Boolean check of the declared coordinate support. -/
def supportTest (name : Cell w h → AxisTrack) (p : Cell w h) : Bool :=
  match name p with
  | .outside => true
  | .horizontal y => decide (p.2.val = y)
  | .vertical x => decide (p.1.val = x)
  | .sink x y => decide (p.1.val = x ∧ p.2.val = y)

theorem supportTest_correct (name : Cell w h → AxisTrack) (p : Cell w h) :
    supportTest name p = true ↔ (name p).Supports p := by
  cases he : name p <;> simp [supportTest, he, AxisTrack.Supports]

/-- Only represented rails and sinks need their outgoing edges enumerated. -/
def activeSources (name : Cell w h → AxisTrack) : Finset (Cell w h) :=
  Finset.univ.filter fun p => name p ≠ .outside

/-- An outside source automatically satisfies the four-level classification. -/
theorem allowed_from_outside {name : Cell w h → AxisTrack} {p q : Cell w h}
    (hp : name p = .outside) : allowed name p q = true := by
  cases hq : name q <;> simp [allowed, hp, hq, AxisTrack.level]

end AxisTrack

/-- A coordinate-supported wall-only classification of one complete finite glyph. -/
structure AxisClassifier (B : Board w h) where
  /-- Track names retain their actual row, column or sink coordinates. -/
  name : Cell w h → AxisTrack
  /-- Every declared track uses its specified coordinates. -/
  supported : ∀ p, (name p).Supports p
  /-- Every finite-board static displacement has the classified rank behavior. -/
  displacement : ∀ p q, Displacement B p q → name p = name q ∨ (name p).level < (name q).level

/-- Build a full finite-board classifier from active stencils and supported coordinate names. -/
def AxisClassifier.of_check {wall : Cell w h → Bool} {B : Board w h}
    (hw : ∀ p, wall p = true ↔ p ∈ B.walls) (name : Cell w h → AxisTrack)
    (hsupported : ∀ p, AxisTrack.supportTest name p = true)
    (hchecked : checkDisplacements wall (AxisTrack.activeSources name) (AxisTrack.allowed name) = true) :
    AxisClassifier B where
  name := name
  supported p := (AxisTrack.supportTest_correct name p).mp (hsupported p)
  displacement p q hd := by
    by_cases hp : name p = .outside
    · exact of_decide_eq_true (AxisTrack.allowed_from_outside hp)
    · have hmem : p ∈ AxisTrack.activeSources name := by simp [AxisTrack.activeSources, hp]
      exact of_decide_eq_true ((checkDisplacements_correct hw _ _).mp hchecked p hmem q hd)

/-- A stronger finite stencil certificate supplies the same coordinate-rank classifier. -/
def AxisClassifier.of_strong_check {wall : Cell w h → Bool} {B : Board w h}
    (hw : ∀ p, wall p = true ↔ p ∈ B.walls) (name : Cell w h → AxisTrack)
    (hsupported : ∀ p, AxisTrack.supportTest name p = true)
    (hchecked : checkDisplacements wall (AxisTrack.activeSources name) (AxisTrack.strongAllowed name) = true) :
    AxisClassifier B :=
  of_check hw name hsupported ((checkDisplacements_correct hw _ _).mpr fun p hp q hd =>
    AxisTrack.allowed_of_strong ((checkDisplacements_correct hw _ _).mp hchecked p hp q hd))

end PushPuzzle.PushFS
