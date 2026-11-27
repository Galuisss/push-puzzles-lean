/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Cavity
public import PushFS.Labels

/-!
# Two physical boxes sealing a horizontal strip

The roof and floor of a finite interval are fixed walls. Once the two boundary
boxes contract into its ends while the player is outside, they can only contract
further. This proves the obstruction used by the parity and face-switch tools,
without requiring the boxes to stay in their two canonical slots.
-/

@[expose] public section

namespace PushPuzzle.PushFS.Gadgets.Wires.Soundness


open AND (InGap)

variable {w h : ℕ}

structure StripWalls (B : Board w h) (lo hi y : ℕ) : Prop where
  below : ∀ p : Cell w h, p.2.val = y + 1 → lo ≤ p.1.val → p.1.val ≤ hi → p ∈ B.walls
  above : ∀ p : Cell w h, p.2.val + 1 = y → lo ≤ p.1.val → p.1.val ≤ hi → p ∈ B.walls

structure Configuration (w h : ℕ) where
  state : State w h
  left : Cell w h
  right : Cell w h

structure Shape (y : ℕ) (S : Configuration w h) : Prop where
  left_box : S.left ∈ S.state.boxes
  right_box : S.right ∈ S.state.boxes
  left_row : S.left.2.val = y
  right_row : S.right.2.val = y
  order : S.left.1.val < S.right.1.val

def Good (lo hi : ℕ) (S : Configuration w h) : Prop :=
  S.left.1.val + 1 < lo ∨ hi + 1 < S.right.1.val

structure Sealed (lo hi y : ℕ) (S : Configuration w h) : Prop extends Shape y S where
  left_lower : lo ≤ S.left.1.val + 1
  right_upper : S.right.1.val ≤ hi + 1
  outside : ¬InGap y S.left S.right S.state.player

/-- Every incoming edge of the gap is blocked by a wall or an actual box. -/
private theorem Sealed.no_entry {B : Board w h} {lo hi y : ℕ} {S : Configuration w h}
    (hs : Sealed lo hi y S) (hw : StripWalls B lo hi y)
    {p q : Cell w h} {d : Direction} (hpw : p ∉ B.walls) (hpb : p ∉ S.state.boxes)
    (hp : ¬InGap y S.left S.right p) (hadj : Adjacent d p q) :
    ¬InGap y S.left S.right q := by
  rintro ⟨hqy, hql, hqr⟩
  have hqx : lo ≤ q.1.val ∧ q.1.val ≤ hi := by
    have := hs.left_lower
    have := hs.right_upper
    omega
  cases d with
  | north =>
    simp only [Adjacent] at hadj
    exact hpw (hw.below p (by omega) (by omega) (by omega))
  | south =>
    simp only [Adjacent] at hadj
    exact hpw (hw.above p (by omega) (by omega) (by omega))
  | east =>
    simp only [Adjacent] at hadj
    have hpy : p.2.val = y := by omega
    have hpx : p.1.val = S.left.1.val := by
      simp only [InGap, hpy, true_and, not_and] at hp
      by_contra he
      exact hp (by omega) (by omega)
    have he : p = S.left :=
      Prod.ext (Fin.ext hpx) (Fin.ext (hpy.trans hs.left_row.symm))
    exact hpb (he ▸ hs.left_box)
  | west =>
    simp only [Adjacent] at hadj
    have hpy : p.2.val = y := by omega
    have hpx : p.1.val = S.right.1.val := by
      simp only [InGap, hpy, true_and, not_and] at hp
      by_contra he
      exact hp (by omega) (by omega)
    have he : p = S.right :=
      Prod.ext (Fin.ext hpx) (Fin.ext (hpy.trans hs.right_row.symm))
    exact hpb (he ▸ hs.right_box)

private theorem Sealed.player_stays_outside {B : Board w h} {lo hi y : ℕ}
    {S : Configuration w h} {t : State w h} {d : Direction}
    (hs : Sealed lo hi y S) (hw : StripWalls B lo hi y) (hm : SingleMoveView B d S.state t) :
    ¬InGap y S.left S.right t.player :=
  hs.no_entry hw hm.1.1 hm.1.2.2 hs.outside hm.2.1

private theorem Sealed.no_left_west {B : Board w h} {lo hi y : ℕ}
    {S : Configuration w h} {t : State w h}
    (hs : Sealed lo hi y S) (hm : SingleMoveView B .west S.state t) : t.player ≠ S.left := by
  intro he
  have ha : Adjacent .west S.state.player S.left := he ▸ hm.2.1
  simp only [Adjacent] at ha
  have hpy : S.state.player.2.val = y := by have := hs.left_row; omega
  by_cases hr : S.state.player.1.val < S.right.1.val
  · exact hs.outside ⟨hpy, by omega, hr⟩
  · have he' : S.state.player = S.right := by
      apply Prod.ext <;> apply Fin.ext
      · have := hs.order; omega
      · have := hs.right_row; omega
    exact hm.1.2.2 (he' ▸ hs.right_box)

private theorem Sealed.no_right_east {B : Board w h} {lo hi y : ℕ}
    {S : Configuration w h} {t : State w h}
    (hs : Sealed lo hi y S) (hm : SingleMoveView B .east S.state t) : t.player ≠ S.right := by
  intro he
  have ha : Adjacent .east S.state.player S.right := he ▸ hm.2.1
  simp only [Adjacent] at ha
  have hpy : S.state.player.2.val = y := by have := hs.right_row; omega
  by_cases hl : S.left.1.val < S.state.player.1.val
  · exact hs.outside ⟨hpy, hl, by omega⟩
  · have he' : S.state.player = S.left := by
      apply Prod.ext <;> apply Fin.ext
      · have := hs.order; omega
      · have := hs.left_row; omega
    exact hm.1.2.2 (he' ▸ hs.left_box)

private theorem Sealed.left_monotone {B : Board w h} {lo hi y : ℕ}
    {S : Configuration w h} {t : State w h} {q : Cell w h} {d : Direction}
    (hs : Sealed lo hi y S) (hm : SingleMoveView B d S.state t) (hq : Adjacent d t.player q)
    (hrow : (shiftBox t.player q S.left).2.val = y) :
    S.left.1.val ≤ (shiftBox t.player q S.left).1.val := by
  by_cases hl : S.left = t.player
  · have htp : t.player = S.left := hl.symm
    simp only [hl, shiftBox_source] at hrow ⊢
    have hleft : t.player.2.val = y := hl ▸ hs.left_row
    cases d with
    | north => simp only [Adjacent] at hq; omega
    | east => simp only [Adjacent] at hq; omega
    | south => simp only [Adjacent] at hq; omega
    | west => exact False.elim (hs.no_left_west hm htp)
  · simp [shiftBox_other hl]

private theorem Sealed.right_antitone {B : Board w h} {lo hi y : ℕ}
    {S : Configuration w h} {t : State w h} {q : Cell w h} {d : Direction}
    (hs : Sealed lo hi y S) (hm : SingleMoveView B d S.state t) (hq : Adjacent d t.player q)
    (hrow : (shiftBox t.player q S.right).2.val = y) :
    (shiftBox t.player q S.right).1.val ≤ S.right.1.val := by
  by_cases hr : S.right = t.player
  · have htp : t.player = S.right := hr.symm
    simp only [hr, shiftBox_source] at hrow ⊢
    have hright : t.player.2.val = y := hr ▸ hs.right_row
    cases d with
    | north => simp only [Adjacent] at hq; omega
    | east => exact False.elim (hs.no_right_east hm htp)
    | south => simp only [Adjacent] at hq; omega
    | west => simp only [Adjacent] at hq; omega
  · simp [shiftBox_other hr]

/-- Physical identity update, including all actual walks and single-box pushes. -/
def TrackedStep (B : Board w h) (S T : Configuration w h) : Prop :=
  ∃ d, SingleMoveView B d S.state T.state ∧
    ((T.state.boxes = S.state.boxes ∧ T.left = S.left ∧ T.right = S.right) ∨
      ∃ q, T.state.player ∈ S.state.boxes ∧ Adjacent d T.state.player q ∧
        q ∉ S.state.boxes ∧ T.state.boxes = insert q (S.state.boxes.erase T.state.player) ∧
        T.left = shiftBox T.state.player q S.left ∧
        T.right = shiftBox T.state.player q S.right)

def GeometricStep (B : Board w h) (y : ℕ) (S T : Configuration w h) : Prop :=
  Shape y S ∧ Shape y T ∧ TrackedStep B S T

private theorem sealed_step {B : Board w h} {lo hi y : ℕ} {S T : Configuration w h}
    (hs : Sealed lo hi y S) (hw : StripWalls B lo hi y) (ht : GeometricStep B y S T) :
    Sealed lo hi y T := by
  obtain ⟨_, hT, d, hm, hwalk | hpush⟩ := ht
  · obtain ⟨_, hl, hr⟩ := hwalk
    refine ⟨hT, ?_, ?_, ?_⟩
    · simpa [hl] using hs.left_lower
    · simpa [hr] using hs.right_upper
    · simpa [hl, hr] using hs.player_stays_outside hw hm
  · obtain ⟨q, _, hq, _, _, hl, hr⟩ := hpush
    have hleft : S.left.1.val ≤ T.left.1.val := by
      simpa [hl] using hs.left_monotone hm hq (hl ▸ hT.left_row)
    have hright : T.right.1.val ≤ S.right.1.val := by
      simpa [hr] using hs.right_antitone hm hq (hr ▸ hT.right_row)
    refine ⟨hT, ?_, ?_, ?_⟩
    · have := hs.left_lower; omega
    · have := hs.right_upper; omega
    · rintro ⟨hy, hll, hrr⟩
      exact hs.player_stays_outside hw hm ⟨hy, by omega, by omega⟩

/-- The first contraction leaves the real player outside the enclosed interval. -/
private theorem outside_of_becomes_bad {lo hi y : ℕ} {S T : Configuration w h} {q : Cell w h}
    (hs : Shape y S) (hg : Good lo hi S) (hb : ¬Good lo hi T)
    (hl : T.left = shiftBox T.state.player q S.left)
    (hr : T.right = shiftBox T.state.player q S.right) :
    ¬InGap y T.left T.right T.state.player := by
  rintro ⟨_, hpl, hpr⟩
  simp only [Good, not_or, not_lt] at hb
  by_cases hmoveL : S.left = T.state.player
  · have hmoveR : S.right ≠ T.state.player := by
      intro he
      have he' := congrArg (fun p : Cell w h => p.1.val) (he.trans hmoveL.symm)
      have := hs.order
      omega
    have hR : T.right = S.right := by simpa [shiftBox_other hmoveR] using hr
    have hpx := congrArg (fun p : Cell w h => p.1.val) hmoveL
    rcases hg with hg | hg <;> rw [hR] at hb <;> omega
  · have hL : T.left = S.left := by simpa [shiftBox_other hmoveL] using hl
    by_cases hmoveR : S.right = T.state.player
    · have hpx := congrArg (fun p : Cell w h => p.1.val) hmoveR
      rcases hg with hg | hg <;> rw [hL] at hb <;> omega
    · have hR : T.right = S.right := by simpa [shiftBox_other hmoveR] using hr
      rw [hL, hR] at hb
      rcases hg with hg | hg <;> omega

private theorem good_or_sealed_step {B : Board w h} {lo hi y : ℕ} {S T : Configuration w h}
    (hw : StripWalls B lo hi y) (hs : Good lo hi S ∨ Sealed lo hi y S)
    (ht : GeometricStep B y S T) : Good lo hi T ∨ Sealed lo hi y T := by
  rcases hs with hg | hs
  · obtain ⟨hS, hT, _, _, hwalk | hpush⟩ := ht
    · obtain ⟨_, hl, hr⟩ := hwalk
      exact Or.inl (by simpa [Good, hl, hr] using hg)
    · by_cases hgood : Good lo hi T
      · exact Or.inl hgood
      · obtain ⟨q, _, _, _, _, hl, hr⟩ := hpush
        have hb := hgood
        simp only [Good, not_or, not_lt] at hb
        exact Or.inr ⟨hT, hb.1, hb.2, outside_of_becomes_bad hS hg hgood hl hr⟩
  · exact Or.inr (sealed_step hs hw ht)

private theorem good_or_sealed_reachable {B : Board w h} {lo hi y : ℕ} {S T : Configuration w h}
    (hw : StripWalls B lo hi y) (hs : Good lo hi S)
    (hr : Relation.ReflTransGen (GeometricStep B y) S T) :
    Good lo hi T ∨ Sealed lo hi y T := by
  induction hr with
  | refl => exact Or.inl hs
  | tail _ hstep ih => exact good_or_sealed_step hw ih hstep

theorem good_on_successful_path {B : Board w h} {lo hi y : ℕ}
    {initial S final : Configuration w h}
    (hw : StripWalls B lo hi y) (hstart : Good lo hi initial) (hfinish : Good lo hi final)
    (hbefore : Relation.ReflTransGen (GeometricStep B y) initial S)
    (hafter : Relation.ReflTransGen (GeometricStep B y) S final) : Good lo hi S := by
  rcases good_or_sealed_reachable hw hstart hbefore with hg | hs
  · exact hg
  · have hf : Sealed lo hi y final := by
      clear hfinish
      induction hafter with
      | refl => exact hs
      | tail _ hstep ih => exact sealed_step ih hw hstep
    have := hf.left_lower
    have := hf.right_upper
    rcases hfinish with hf | hf <;> omega

end PushPuzzle.PushFS.Gadgets.Wires.Soundness
