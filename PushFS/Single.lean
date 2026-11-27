/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Run
import Mathlib.Tactic.FinCases

/-!
# Single-box move elimination

`Move.single_iff` exposes the empty neighbor or the single pushed box and its
empty destination. Gadget proofs use this equivalent conjunctive view.
-/

@[expose] public section

namespace PushPuzzle.PushFS


variable {w h : ℕ}

/-- Conjunctive view of a single-box walk or push. -/
def SingleMoveView (B : Board w h) (d : Direction) (s t : State w h) : Prop :=
  s.Valid B ∧ Adjacent d s.player t.player ∧ t.player ∉ B.walls ∧
    ((t.player ∉ s.boxes ∧ t.boxes = s.boxes) ∨
      (t.player ∈ s.boxes ∧ ∃ q : Cell w h,
        Adjacent d t.player q ∧ q ∉ B.walls ∧ q ∉ s.boxes ∧
          t.boxes = insert q (s.boxes.erase t.player)))

/-- The one-box cap gives exactly the usual single-box neighbor rule. -/
theorem Move.single_iff {B : Board w h} {d : Direction} {s t : State w h} :
    Move B (some 1) d s t ↔ SingleMoveView B d s t := by
  constructor
  · intro hm
    cases hm with
    | walk hv ha hf he hb => exact ⟨hv, ha, hf, Or.inl ⟨he, hb⟩⟩
    | @push n hv hn hc r hp hb =>
      have hn1 : n = 1 := by change n ≤ 1 at hc; omega
      subst n
      have ha : Adjacent d s.player (r.cell 1) := r.start ▸ r.adjacent 0
      refine ⟨hv, hp ▸ ha, hp ▸ r.floor 1, Or.inr ⟨hp ▸ r.first_occupied hn,
        r.cell ⟨2, by omega⟩, ?_, r.floor _, r.empty, ?_⟩⟩
      · exact hp ▸ r.adjacent ⟨1, by omega⟩
      · exact hp ▸ hb
  · rintro ⟨hv, ha, hf, ⟨he, hb⟩ | ⟨hbox, q, hq, hqw, hqe, hb⟩⟩
    · exact .walk hv ha hf he hb
    · let cell : Fin 3 → Cell w h := fun i =>
        if i.val = 0 then s.player else if i.val = 1 then t.player else q
      let r : Run B d s 1 := {
        cell := cell
        start := rfl
        adjacent := by
          intro i
          fin_cases i
          · simpa [cell] using ha
          · simpa [cell] using hq
        occupied := by intro i; fin_cases i; exact hbox
        empty := hqe
        floor := by
          intro i
          fin_cases i
          · exact hv.1
          · exact hf
          · exact hqw }
      exact .push hv (by decide) (by change 1 ≤ 1; decide) r rfl hb

/-- A free adjacent cell gives the walking branch of the single-box view. -/
theorem SingleMoveView.walk {B : Board w h} {d : Direction} {s : State w h} {p : Cell w h}
    (hs : s.Valid B) (ha : Adjacent d s.player p) (hw : p ∉ B.walls) (he : p ∉ s.boxes) :
    SingleMoveView B d s ⟨p, s.boxes⟩ := ⟨hs, ha, hw, Or.inl ⟨he, rfl⟩⟩

/-- A box with an empty destination gives the pushing branch of the single-box view. -/
theorem SingleMoveView.push {B : Board w h} {d : Direction} {s : State w h} {p q : Cell w h}
    (hs : s.Valid B) (ha : Adjacent d s.player p) (hp : p ∈ s.boxes)
    (hq : Adjacent d p q) (hw : q ∉ B.walls) (he : q ∉ s.boxes) :
    SingleMoveView B d s ⟨p, insert q (s.boxes.erase p)⟩ :=
  ⟨hs, ha, fun h => Finset.disjoint_left.mp hs.2.1 hp h, Or.inr ⟨hp, q, hq, hw, he, rfl⟩⟩

theorem SingleMoveView.valid_target {B : Board w h} {d : Direction} {s t : State w h}
    (hm : SingleMoveView B d s t) : t.Valid B := (Move.single_iff.mpr hm).valid_target

end PushPuzzle.PushFS
