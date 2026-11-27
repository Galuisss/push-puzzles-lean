/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Gates.Slots
public import PushFS.StaticTracks

/-! Explicit wall-only paths pairing every physical box with its exact canonical target. -/

@[expose] public section

namespace PushPuzzle.PushFS.Gadgets.Gates


-- The finite literal slot lists and their one- or three-step paths are reduced by the kernel.
set_option maxRecDepth 65536

/-- One wall-only displacement, checking source, support and destination floor. -/
def staticStep {w h : ℕ} (wall : Cell w h → Bool) (d : Direction) (p : Cell w h) :
    Option (Cell w h) := do
  let q ← neighbor d p
  let rear ← neighbor d.opposite p
  if wall p || wall rear || wall q then none else some q

theorem staticStep_sound {w h : ℕ} {wall : Cell w h → Bool} {B : Board w h}
    (hw : ∀ p, wall p = true ↔ p ∈ B.walls) {d : Direction} {p q : Cell w h}
    (he : staticStep wall d p = some q) : Displacement B p q := by
  cases hn : neighbor d p with
  | none => simp [staticStep, hn] at he
  | some dst =>
    cases hr : neighbor d.opposite p with
    | none => simp [staticStep, hn, hr] at he
    | some rear =>
      by_cases hblocked : (wall p || wall rear || wall dst) = true
      · have hnone : staticStep wall d p = none := by
          simp only [staticStep, hn, hr, bind, Option.bind, hblocked, ↓reduceIte]
        rw [hnone] at he
        cases he
      · simp only [staticStep, hn, hr, hblocked, bind, Option.bind, Bool.false_eq_true,
          ↓reduceIte, Option.some.injEq] at he
        subst dst
        simp only [Bool.or_eq_true, not_or] at hblocked
        refine ⟨fun h => hblocked.1.1 ((hw p).mpr h), d, rear, ?_, neighbor_sound hn,
          fun h => hblocked.1.2 ((hw rear).mpr h), fun h => hblocked.2 ((hw q).mpr h)⟩
        simpa only [Direction.opposite_opposite] using (neighbor_sound hr).reverse

/-- Replay static displacement directions without assuming access by the player. -/
def staticRun {w h : ℕ} (wall : Cell w h → Bool) (p : Cell w h) :
    List Direction → Option (Cell w h)
  | [] => some p
  | d :: ds => (staticStep wall d p).bind fun q => staticRun wall q ds

theorem staticRun_sound {w h : ℕ} {wall : Cell w h → Bool} {B : Board w h}
    (hw : ∀ p, wall p = true ↔ p ∈ B.walls) {p q : Cell w h} {ds : List Direction}
    (he : staticRun wall p ds = some q) : StaticReach B p q := by
  induction ds generalizing p with
  | nil =>
    simp only [staticRun, Option.some.injEq] at he
    exact he ▸ .refl
  | cons d ds ih =>
    cases hm : staticStep wall d p with
    | none => simp [staticRun, hm] at he
    | some r =>
      have hh : staticRun wall r ds = some q := by simpa [staticRun, hm] using he
      exact (ih hh).head (staticStep_sound hw hm)

/-- The one- or three-cell straight path between a physical slot's two endpoints. -/
private def straightDirections (p q : C) : List Direction :=
  if p.1.val < q.1.val then List.replicate (q.1.val - p.1.val) .east
  else if q.1.val < p.1.val then List.replicate (p.1.val - q.1.val) .west
  else if p.2.val < q.2.val then List.replicate (q.2.val - p.2.val) .south
  else List.replicate (p.2.val - q.2.val) .north

private def Slot.pathChecked (kind : Bool) (s : Slot) : Bool :=
  decide (staticRun (wallTest kind) s.zero (straightDirections s.zero s.one) = some s.one) &&
  decide (staticRun (wallTest kind) s.one (straightDirections s.one s.zero) = some s.zero)

private theorem slot_paths_checked (kind : Bool) :
    ((slots kind).all fun s => s.pathChecked kind) = true := by
  have hh : ∀ kind : Bool, ((slots kind).all fun s => s.pathChecked kind) = true := by decide +kernel
  exact hh kind

/-- Both positions of each actual physical slot lie in the same static SCC. -/
private theorem slot_sameComponent (kind : Bool) (s : Slot) (hs : s ∈ slots kind)
    (goals : Finset C) :
    SameComponent (board kind goals) s.zero s.one := by
  have hh := List.all_eq_true.mp (slot_paths_checked kind) s hs
  simp only [Slot.pathChecked, Bool.and_eq_true, decide_eq_true_eq] at hh
  exact ⟨staticRun_sound (wallTest_correct kind goals) hh.1,
    staticRun_sound (wallTest_correct kind goals) hh.2⟩

theorem slot_position_component (kind : Bool) (s : Slot) (hs : s ∈ slots kind)
    (a b : Signals) (goals : Finset C) :
    SameComponent (board kind goals) (s.position a) (s.position b) := by
  have hh := slot_sameComponent kind s hs goals
  unfold Slot.position
  split <;> split
  · exact ⟨.refl, .refl⟩
  · exact ⟨hh.2, hh.1⟩
  · exact hh
  · exact ⟨.refl, .refl⟩

/-- A complete explicit storage instance between any two canonical flag assignments. -/
def storageInstance (kind : Bool) (a b : Signals) : Instance where
  width := 81
  height := 107
  board := board kind (canonicalBoxes kind b)
  initial := canonical kind a
  goals_floor := (canonicalBoxes_floor kind b).symm
  initial_valid := canonical_valid kind a _
  boxes_eq_goals := (canonicalBoxes_card kind a).trans (canonicalBoxes_card kind b).symm

/-- Physical identities supply all initial boxes, all exact targets and their static paths. -/
def slotMatching (kind : Bool) (a b : Signals) :
    SlotMatching (storageInstance kind a b) (Fin (slots kind).length) where
  source := ⟨position kind a, position_injective kind a⟩
  target := ⟨position kind b, position_injective kind b⟩
  source_image := by rw [Finset.map_eq_image]; exact position_image kind a
  target_image := by rw [Finset.map_eq_image]; exact position_image kind b
  connected i := slot_position_component kind ((slots kind).get i) (List.get_mem _ _) a b _

end PushPuzzle.PushFS.Gadgets.Gates
