/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.StaticTracks

/-!
# Uniform horizontal and vertical rail certificates

Keeping all logical gates in one orientation makes every cross-rail displacement
go from a vertical rail into a horizontal rail, or into a singleton sink. Track
names need only their fixed grid coordinate, so separated collinear rail pieces
can share a name without computing the board's SCCs.
-/

@[expose] public section

namespace PushPuzzle.PushFS


/-- A floor exterior, a complete row or column, or one immobile corner. -/
inductive AxisTrack
  | outside
  | horizontal (row : ℕ)
  | vertical (column : ℕ)
  | sink (x y : ℕ)
  deriving DecidableEq

/-- Increasing levels of the uniformly oriented displacement classification. -/
def AxisTrack.level : AxisTrack → ℕ
  | .outside => 0
  | .vertical _ => 1
  | .horizontal _ => 2
  | .sink _ _ => 3

/-- A named track really uses its declared grid coordinate. -/
def AxisTrack.Supports {w h : ℕ} (p : Cell w h) : AxisTrack → Prop
  | .outside => True
  | .horizontal y => p.2.val = y
  | .vertical x => p.1.val = x
  | .sink x y => p.1.val = x ∧ p.2.val = y

/-- Static geometric data for a complete uniformly oriented board. -/
structure AxisTracks (I : Instance) where
  /-- The named rail or corner at every cell. -/
  name : Cell I.width I.height → AxisTrack
  /-- Names retain their actual grid coordinates. -/
  supported : ∀ p, (name p).Supports p
  /-- Every initial box is on a represented rail or corner. -/
  active : ∀ p ∈ I.initial.boxes, name p ≠ .outside
  /-- Every displacement stays on its named rail or strictly increases level. -/
  displacement : ∀ p q, Displacement I.board p q →
    name p = name q ∨ (name p).level < (name q).level
  /-- Goal slots on the same named rail are separated. -/
  separated : ∀ p ∈ I.board.goals, ∀ q ∈ I.board.goals,
    name p = name q → ∀ d, ¬Adjacent d p q

/-- Coordinate names establish straightness of every initially occupied static component. -/
def AxisTracks.toStaticTracks {I : Instance} (A : AxisTracks I) : StaticTracks I AxisTrack where
  name := A.name
  level := AxisTrack.level
  displacement := A.displacement
  linear p hp := by
    have hs := A.supported p
    cases hn : A.name p with
    | outside => exact False.elim (A.active p hp hn)
    | horizontal y =>
      refine Or.inr (fun q hq => ?_)
      have ht := A.supported q
      rw [hq] at ht
      rw [hn] at hs
      exact Fin.ext (ht.trans hs.symm)
    | vertical x =>
      refine Or.inl (fun q hq => ?_)
      have ht := A.supported q
      rw [hq] at ht
      rw [hn] at hs
      exact Fin.ext (ht.trans hs.symm)
    | sink x y =>
      refine Or.inl (fun q hq => ?_)
      have ht := A.supported q
      rw [hq] at ht
      rw [hn] at hs
      exact Fin.ext (ht.1.trans hs.1.symm)
  separated := A.separated

end PushPuzzle.PushFS
