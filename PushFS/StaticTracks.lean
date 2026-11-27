/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Transfer

/-!
# Constructing SCC certificates from static tracks

The construction gives each initial box a distinct target on the same static
component. A finite track classification has strictly increasing levels on
every displacement between tracks. Therefore an SCC cannot join two tracks;
straight tracks and separated goal slots supply C2 and C3.

## Main results

* `SlotMatching.componentBalanced`: explicit slot paths imply C1 for unlabelled boxes.
* `StaticTracks.certificate`: local displacement classification yields the SCC certificate.
-/

@[expose] public section

namespace PushPuzzle.PushFS


open scoped Classical

/-- A temporary physical box indexing matching initial slots to exact goal slots. -/
structure SlotMatching (I : Instance) (Label : Type) [Fintype Label] where
  /-- The distinct initial slots. -/
  source : Label ↪ Cell I.width I.height
  /-- The distinct goal slots. -/
  target : Label ↪ Cell I.width I.height
  /-- Every initial box is represented once. -/
  source_image : Finset.univ.map source = I.initial.boxes
  /-- Every target is represented once. -/
  target_image : Finset.univ.map target = I.board.goals
  /-- Both slots are connected in both directions by wall-only displacements. -/
  connected : ∀ l, SameComponent I.board (source l) (target l)

/-- Slot paths balance actual SCC occupancies, without a labelled goal predicate. -/
theorem SlotMatching.componentBalanced {I : Instance} {Label : Type} [Fintype Label]
    (M : SlotMatching I Label) : ComponentBalanced I.board I.initial := by
  classical
  intro c
  rw [← M.source_image, ← M.target_image, Finset.filter_map, Finset.filter_map,
    Finset.card_map, Finset.card_map]
  congr 1
  apply Finset.filter_congr
  intro l _
  exact (congrArg (· = c) (component_eq_iff.mpr (M.connected l))) |>.to_iff

/-- A static local track classification of a complete finite board. -/
structure StaticTracks (I : Instance) (Track : Type) where
  /-- Every cell has a track name; unused floor and wall cells may share names. -/
  name : Cell I.width I.height → Track
  /-- The level of each track. -/
  level : Track → ℕ
  /-- Displacements stay on a track or strictly increase its level. -/
  displacement : ∀ p q, Displacement I.board p q →
    name p = name q ∨ level (name p) < level (name q)
  /-- Initially occupied tracks are straight. -/
  linear : ∀ p ∈ I.initial.boxes,
    (∀ q, name q = name p → q.1 = p.1) ∨ (∀ q, name q = name p → q.2 = p.2)
  /-- Goal slots in one track are not adjacent. -/
  separated : ∀ p ∈ I.board.goals, ∀ q ∈ I.board.goals,
    name p = name q → ∀ d, ¬Adjacent d p q

private theorem staticReach_name_eq_or_lt {I : Instance} {Track : Type}
    (T : StaticTracks I Track) {p q : Cell I.width I.height}
    (hr : StaticReach I.board p q) :
    T.name p = T.name q ∨ T.level (T.name p) < T.level (T.name q) := by
  induction hr with
  | refl => exact Or.inl rfl
  | tail _ hd ih =>
    rcases ih with he | hl <;> rcases T.displacement _ _ hd with he' | hl'
    · exact Or.inl (he.trans he')
    · exact Or.inr (he ▸ hl')
    · exact Or.inr (he' ▸ hl)
    · exact Or.inr (hl.trans hl')

/-- Strong connectivity keeps the track name, including at interfaces. -/
theorem StaticTracks.name_eq_of_component_eq {I : Instance} {Track : Type}
    (T : StaticTracks I Track) {p q : Cell I.width I.height}
    (he : component I.board p = component I.board q) : T.name p = T.name q := by
  have hc := component_eq_iff.mp he
  rcases staticReach_name_eq_or_lt T hc.1 with he | hl
  · exact he
  · rcases staticReach_name_eq_or_lt T hc.2 with he | hl'
    · have hlevel := congrArg T.level he
      omega
    · exact False.elim (Nat.lt_asymm hl hl')

/-- Static slot paths, displacement levels and track geometry imply C1–C3. -/
theorem StaticTracks.certificate {I : Instance} {Label Track : Type} [Fintype Label]
    (T : StaticTracks I Track) (M : SlotMatching I Label) : Certificate I where
  balanced := M.componentBalanced
  linear p hp := by
    rcases T.linear p hp with hx | hy
    · exact Or.inl (fun q r hq hr =>
        (hx q (T.name_eq_of_component_eq hq)).trans
          (hx r (T.name_eq_of_component_eq hr)).symm)
    · exact Or.inr (fun q r hq hr =>
        (hy q (T.name_eq_of_component_eq hq)).trans
          (hy r (T.name_eq_of_component_eq hr)).symm)
  separated p hp q hq hc := T.separated p hp q hq (T.name_eq_of_component_eq hc)

end PushPuzzle.PushFS
