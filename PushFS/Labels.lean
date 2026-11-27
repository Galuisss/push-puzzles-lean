/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.AND
public import PushFS.Components

/-!
# Physical box identities on unlabelled trajectories

Every single-box trajectory lifts to one fixed label set with the actual box
updates. Labels enumerate all occupied cells. They preserve the exact player
position and leave the storage goal unlabelled.
-/

@[expose] public section

namespace PushPuzzle.PushFS


open Gadgets
open scoped BigOperators

variable {w h : ℕ} {ι : Type} [Fintype ι]

/-- A complete physical indexing of the current occupied cells. -/
structure LabelledState (ι : Type) [Fintype ι] (w h : ℕ) where
  /-- The exact unlabelled puzzle state. -/
  state : State w h
  /-- Current location of each physical box. -/
  position : ι → Cell w h
  /-- Distinct boxes occupy distinct cells. -/
  injective : Function.Injective position
  /-- Every occupied cell has a physical identity. -/
  boxes_image : Finset.univ.image position = state.boxes

namespace LabelledState

theorem position_mem (S : LabelledState ι w h) (i : ι) : S.position i ∈ S.state.boxes := by
  rw [← S.boxes_image]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

/-- A real single-box step with its physical identity update. -/
def Step (B : Board w h) (S T : LabelledState ι w h) : Prop :=
  ∃ d, SingleMoveView B d S.state T.state ∧
    ((T.state.boxes = S.state.boxes ∧ T.position = S.position) ∨
      ∃ q, T.state.player ∈ S.state.boxes ∧ Adjacent d T.state.player q ∧
        q ∉ S.state.boxes ∧ T.state.boxes = insert q (S.state.boxes.erase T.state.player) ∧
        T.position = shiftBox T.state.player q ∘ S.position)

/-- A finite sequence following the same physical identities throughout. -/
abbrev Reachable (B : Board w h) := Relation.ReflTransGen (Step (ι := ι) B)

theorem Step.forget {B : Board w h} {S T : LabelledState ι w h} (hs : Step B S T) :
    PushFS.Step B (some 1) S.state T.state := ⟨hs.choose, Move.single_iff.mpr hs.choose_spec.1⟩

theorem Reachable.forget {B : Board w h} {S T : LabelledState ι w h} (hr : Reachable B S T) :
    PushFS.Reachable B (some 1) S.state T.state := hr.lift state (fun _ _ hs => hs.forget)

/-- Every real step admits its physical identity update, including pushes of
boxes not mentioned by any particular gate's local projection. -/
private theorem lift_step (B : Board w h) (S : LabelledState ι w h) {t : State w h}
    (hs : PushFS.Step B (some 1) S.state t) : ∃ T : LabelledState ι w h, T.state = t ∧ Step B S T := by
  obtain ⟨d, hmove⟩ := hs
  have hm := Move.single_iff.mp hmove
  rcases hm.2.2.2 with ⟨_, hboxes⟩ | ⟨hp, q, hq, _, he, hboxes⟩
  · let T : LabelledState ι w h :=
      ⟨t, S.position, S.injective, S.boxes_image.trans hboxes.symm⟩
    exact ⟨T, rfl, d, hm, Or.inl ⟨hboxes, rfl⟩⟩
  · have hinj : Function.Injective (shiftBox t.player q ∘ S.position) := by
      intro i j heq
      exact S.injective (shiftBox_injOn he (S.position_mem i) (S.position_mem j) heq)
    have himage : Finset.univ.image (shiftBox t.player q ∘ S.position) = t.boxes := by
      rw [← Finset.image_image, S.boxes_image, image_shiftBox hp, hboxes]
    let T : LabelledState ι w h := ⟨t, _, hinj, himage⟩
    exact ⟨T, rfl, d, hm, Or.inr ⟨q, hp, hq, he, hboxes, rfl⟩⟩

theorem lift_reachable (B : Board w h) (S : LabelledState ι w h) {t : State w h}
    (hr : PushFS.Reachable B (some 1) S.state t) :
    ∃ T : LabelledState ι w h, T.state = t ∧ Reachable B S T := by
  induction hr with
  | refl => exact ⟨S, rfl, .refl⟩
  | tail _ hs ih =>
    obtain ⟨T, he, hr⟩ := ih
    obtain ⟨U, hu, hstep⟩ := lift_step B T (he ▸ hs)
    exact ⟨U, hu, hr.tail hstep⟩

/-- The initial occupied cells themselves always provide a complete label set. -/
def initial (s : State w h) : LabelledState {p // p ∈ s.boxes} w h where
  state := s
  position := Subtype.val
  injective := Subtype.val_injective
  boxes_image := by ext p; simp

/-- Three selected physical boxes and the same exact player state. -/
def triple (S : LabelledState ι w h) (i j k : ι) : AND.Configuration w h :=
  ⟨S.state, S.position i, S.position j, S.position k⟩

/-- A labelled step supplies the gate's exact tracked trigger updates. -/
theorem Step.triple {B : Board w h} {S T : LabelledState ι w h}
    (hs : Step B S T) (i j k : ι) : AND.TrackedStep B (S.triple i j k) (T.triple i j k) := by
  obtain ⟨d, hm, hwalk | hpush⟩ := hs
  · obtain ⟨hboxes, hp⟩ := hwalk
    exact ⟨d, hm, Or.inl ⟨hboxes, congrFun hp i, congrFun hp j, congrFun hp k⟩⟩
  · obtain ⟨q, hp, hq, he, hboxes, hpos⟩ := hpush
    exact ⟨d, hm, Or.inr ⟨q, hp, hq, he, hboxes,
      congrFun hpos i, congrFun hpos j, congrFun hpos k⟩⟩

/-- Each physical identity retains its static SCC on a potential-preserving step. -/
private theorem Step.component_eq {B : Board w h} {S T : LabelledState ι w h}
    (hs : Step B S T) (he : potential B S.state = potential B T.state) (i : ι) :
    component B (S.position i) = component B (T.position i) := by
  classical
  obtain ⟨d, hm, hwalk | hpush⟩ := hs
  · exact congrArg (component B) (congrFun hwalk.2 i).symm
  · obtain ⟨q, hp, hq, hqe, hb, hpos⟩ := hpush
    by_cases hpi : S.position i = T.state.player
    · have hqw : q ∉ B.walls := by
        rcases hm.2.2.2 with ⟨hfree, _⟩ | ⟨_, q', hq', hw, _⟩
        · exact False.elim (hfree hp)
        · exact hq'.functional hq ▸ hw
      have hd : Displacement B T.state.player q :=
        ⟨hm.2.2.1, d, S.state.player, hm.2.1, hq, hm.1.1, hqw⟩
      have hsum := Finset.sum_erase_add S.state.boxes (rank B) hp
      change (∑ p ∈ S.state.boxes.erase T.state.player, rank B p) +
        rank B T.state.player = potential B S.state at hsum
      have ht : potential B T.state = rank B q +
          ∑ p ∈ S.state.boxes.erase T.state.player, rank B p := by
        simp only [potential, hb, Finset.sum_insert
          (fun h => hqe (Finset.mem_of_mem_erase h))]
      have hrank : rank B T.state.player = rank B q := by omega
      have hc := component_eq_iff.mpr (sameComponent_of_rank_eq (.single hd) hrank)
      simpa only [hpos, Function.comp_apply, hpi, shiftBox_source] using hc
    · have hfix : T.position i = S.position i := by
        simpa only [Function.comp_apply, shiftBox_other hpi] using congrFun hpos i
      exact congrArg (component B) hfix.symm

/-- Each physical box stays in its initial SCC on an equal-potential trajectory. -/
theorem Reachable.component_eq {B : Board w h} {S T : LabelledState ι w h}
    (hr : Reachable B S T) (he : potential B S.state = potential B T.state) (i : ι) :
    component B (S.position i) = component B (T.position i) := by
  induction hr with
  | refl => rfl
  | @tail U V hr hs ih =>
    have hlo := PushFS.Reachable.potential_mono (Reachable.forget hr)
    have hhi := hs.forget.choose_spec.potential_mono
    have hp : potential B S.state = potential B U.state := by omega
    have hq : potential B U.state = potential B V.state := by omega
    exact (ih hp).trans (hs.component_eq hq i)

end LabelledState
end PushPuzzle.PushFS
