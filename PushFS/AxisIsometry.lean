/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Isometry
public import PushFS.DisplacementCheck

/-!
# Reorienting the supported rail and sink classifiers

The stronger line/turn relation allows only movement on one name or movement
from a rail into a sink. It is preserved by transposition and reflection even
though these operations exchange horizontal and vertical level numbers.
Rotated glyphs thus reuse their actual wall stencil proofs.
-/

@[expose] public section

namespace PushPuzzle.PushFS


namespace AxisTrack

/-- A horizontal or vertical rail. -/
def Rail : AxisTrack → Prop
  | .horizontal _ | .vertical _ => True
  | _ => False

/-- An immobile singleton corner. -/
def Sink : AxisTrack → Prop
  | .sink _ _ => True
  | _ => False

/-- Same-name motion or entry from a rail into an immobile corner. -/
def Strong (a b : AxisTrack) : Prop := a = b ∨ a.Rail ∧ b.Sink

theorem strongAllowed_iff {w h : ℕ} (name : Cell w h → AxisTrack) (p q : Cell w h) :
    strongAllowed name p q = true ↔ Strong (name p) (name q) := by
  cases hp : name p <;> cases hq : name q <;> simp [strongAllowed, Strong, Rail, Sink, hp, hq]

end AxisTrack

/-- A real grid isometry with its literal row, column and singleton coordinate transport. -/
structure AxisIsometry (w h W H : ℕ) where
  /-- The checked physical grid transformation. -/
  geometry : GridIsometry w h W H
  /-- The corresponding row, column or singleton name. -/
  name : AxisTrack → AxisTrack
  /-- Only the exterior name maps to the exterior. -/
  outside : ∀ t, name t = .outside ↔ t = .outside
  /-- Names retain the physical coordinate they assert. -/
  supported : ∀ (p : Cell w h) t, t.Supports p → (name t).Supports (geometry.cells p)
  /-- A rail remains a rail. -/
  rail : ∀ t, t.Rail → (name t).Rail
  /-- A singleton remains a singleton. -/
  sink : ∀ t, t.Sink → (name t).Sink

namespace AxisIsometry

variable {w h W H u v : ℕ}

def refl (w h : ℕ) : AxisIsometry w h w h where
  geometry := GridIsometry.refl w h
  name := id
  outside _ := Iff.rfl
  supported _ _ hs := hs
  rail _ hs := hs
  sink _ hs := hs

/-- Compose the actual cell map and the corresponding coordinate names. -/
def trans (e : AxisIsometry w h W H) (f : AxisIsometry W H u v) : AxisIsometry w h u v where
  geometry := e.geometry.trans f.geometry
  name := f.name ∘ e.name
  outside t := (f.outside _).trans (e.outside t)
  supported p t hs := f.supported _ _ (e.supported p t hs)
  rail t hs := f.rail _ (e.rail t hs)
  sink t hs := f.sink _ (e.sink t hs)

/-- Transposition exchanges the row and column names and swaps a sink's coordinates. -/
def transpose (w h : ℕ) : AxisIsometry w h h w where
  geometry := GridIsometry.transpose w h
  name
    | .outside => .outside
    | .horizontal y => .vertical y
    | .vertical x => .horizontal x
    | .sink x y => .sink y x
  outside t := by cases t <;> simp
  supported p t hs := by cases t <;> simp_all [AxisTrack.Supports, GridIsometry.transpose]
  rail t hs := by cases t <;> simp_all [AxisTrack.Rail]
  sink t hs := by cases t <;> simp_all [AxisTrack.Sink]

/-- Horizontal reflection retains rows and reverses column and sink coordinates. -/
def reflectX (w h : ℕ) : AxisIsometry w h w h where
  geometry := GridIsometry.reflectX w h
  name
    | .outside => .outside
    | .horizontal y => .horizontal y
    | .vertical x => .vertical (w - 1 - x)
    | .sink x y => .sink (w - 1 - x) y
  outside t := by cases t <;> simp
  supported p t hs := by
    cases t <;> simp_all [AxisTrack.Supports, GridIsometry.reflectX, Fin.revPerm, Fin.rev] <;> omega
  rail t hs := by cases t <;> simp_all [AxisTrack.Rail]
  sink t hs := by cases t <;> simp_all [AxisTrack.Sink]

def reflectY (w h : ℕ) : AxisIsometry w h w h :=
  ((transpose w h).trans (reflectX h w)).trans (transpose h w)

def clockwise (w h : ℕ) : AxisIsometry w h h w := (transpose w h).trans (reflectX h w)

/-- Every checked stronger displacement relation survives all the supplied reorientations. -/
theorem strong (e : AxisIsometry w h W H) {a b : AxisTrack} (hs : a.Strong b) :
    (e.name a).Strong (e.name b) := by
  rcases hs with he | ⟨ha, hb⟩
  · exact Or.inl (congrArg e.name he)
  · exact Or.inr ⟨e.rail a ha, e.sink b hb⟩

/-- Reorient the actual finite classifier, using a proved rail/sink outgoing relation. -/
def classifier (e : AxisIsometry w h W H) {B : Board w h} (C : AxisClassifier B)
    (hstrong : ∀ p q, C.name p ≠ .outside → Displacement B p q →
      (C.name p).Strong (C.name q)) : AxisClassifier (e.geometry.board B) where
  name p := e.name (C.name (e.geometry.cells.symm p))
  supported p := by
    have hs := e.supported (e.geometry.cells.symm p) _ (C.supported _)
    simpa only [Equiv.apply_symm_apply] using hs
  displacement p q hd := by
    obtain ⟨p', rfl⟩ := e.geometry.cells.surjective p
    obtain ⟨q', rfl⟩ := e.geometry.cells.surjective q
    simp only [Equiv.symm_apply_apply]
    by_cases hp : C.name p' = .outside
    · have he : e.name (C.name p') = .outside := (e.outside _).mpr hp
      have hh : AxisTrack.allowed (fun p => e.name (C.name p)) p' q' = true :=
        AxisTrack.allowed_from_outside he
      exact of_decide_eq_true hh
    · have hs := e.strong (hstrong p' q' hp ((e.geometry.displacement_iff B p' q').mp hd))
      exact of_decide_eq_true (AxisTrack.allowed_of_strong
        ((AxisTrack.strongAllowed_iff (fun p => e.name (C.name p)) p' q').mpr hs))

end AxisIsometry

/-- Reorient every physical source and target identity along with its actual static paths. -/
def SlotMatching.reorient {I : Instance} {Label : Type} [Fintype Label]
    (M : SlotMatching I Label) {W H : ℕ} (e : GridIsometry I.width I.height W H) :
    SlotMatching (e.reorientInstance I) Label where
  source := M.source.trans e.cells.toEmbedding
  target := M.target.trans e.cells.toEmbedding
  source_image := by
    change Finset.univ.map (M.source.trans e.cells.toEmbedding) = I.initial.boxes.map e.cells.toEmbedding
    rw [← Finset.map_map, M.source_image]
  target_image := by
    change Finset.univ.map (M.target.trans e.cells.toEmbedding) = I.board.goals.map e.cells.toEmbedding
    rw [← Finset.map_map, M.target_image]
  connected l := (e.sameComponent_iff I.board (M.source l) (M.target l)).mpr (M.connected l)

end PushPuzzle.PushFS
