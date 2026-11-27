/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushFS.Gadgets.OR

/-! Sealed cavities and AND/OR thresholds with an independent right boundary. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteCavity

open PushFS PushFS.Gadgets

open PushFS.Gadgets.AND (InGap Configuration TrackedStep)

variable {w h : ℕ}

/-- Walls below the cavity and above it except for the vertical input column. -/
structure Walls (B : Board w h) (j r y : ℕ) : Prop where
  below : ∀ p : Cell w h, p.2.val = y + 1 → j ≤ p.1.val → p.1.val < r → p ∈ B.walls
  roof : ∀ p : Cell w h, p.2.val + 1 = y →
    (j < p.1.val ∧ p.1.val < r) → p ∈ B.walls

/-- An inaccessible cavity bounded by three physical box labels. -/
structure Sealed (B : Board w h) (j r y : ℕ) (s : State w h)
    (a b c : Cell w h) : Prop where
  a_box : a ∈ s.boxes
  b_box : b ∈ s.boxes
  c_box : c ∈ s.boxes
  a_row : a.2.val = y
  c_row : c.2.val = y
  b_col : b.1.val = j
  b_above : b.2.val < y
  a_lower : j ≤ a.1.val + 1
  c_upper : c.1.val ≤ r
  order : a.1.val < c.1.val
  blocked : j ≤ a.1.val ∨ b.2.val + 1 = y
  outside : ¬InGap y a c s.player

/-- Every neighbor entering the cavity meets a wall or boundary box. -/
private theorem Sealed.no_entry {B : Board w h} {j r y : ℕ} {s : State w h}
    {a b c : Cell w h} (hs : Sealed B j r y s a b c) (hw : Walls B j r y)
    {p q : Cell w h} {d : Direction}
    (hpw : p ∉ B.walls) (hpb : p ∉ s.boxes) (hp : ¬InGap y a c p)
    (hadj : Adjacent d p q) : ¬InGap y a c q := by
  rintro ⟨hqy, hqa, hqc⟩
  have hqx : j ≤ q.1.val ∧ q.1.val < r := by
    have := hs.a_lower
    have := hs.c_upper
    omega
  cases d with
  | north =>
    simp only [Adjacent] at hadj
    exact hpw (hw.below p (by omega) (by omega) (by omega))
  | east =>
    simp only [Adjacent] at hadj
    have hpy : p.2.val = y := by omega
    have hpx : p.1.val = a.1.val := by
      simp only [InGap, hpy, true_and, not_and] at hp
      by_contra he
      have ha : a.1.val < p.1.val := by omega
      exact (hp ha) (by omega)
    have he : p = a := Prod.ext (Fin.ext hpx) (Fin.ext (hpy.trans hs.a_row.symm))
    exact hpb (he ▸ hs.a_box)
  | south =>
    simp only [Adjacent] at hadj
    by_cases hx : p.1.val = j
    · have hab : a.1.val < j := by omega
      have hb : b.2.val + 1 = y := hs.blocked.resolve_left (by omega)
      have he : p = b := Prod.ext (Fin.ext (hx.trans hs.b_col.symm)) (Fin.ext (by omega))
      exact hpb (he ▸ hs.b_box)
    · exact hpw (hw.roof p (by omega) ⟨by omega, by omega⟩)
  | west =>
    simp only [Adjacent] at hadj
    have hpy : p.2.val = y := by omega
    have hpx : p.1.val = c.1.val := by
      simp only [InGap, hpy, true_and, not_and] at hp
      by_contra he
      have ha : a.1.val < p.1.val := by omega
      exact (hp ha) (by omega)
    have he : p = c := Prod.ext (Fin.ext hpx) (Fin.ext (hpy.trans hs.c_row.symm))
    exact hpb (he ▸ hs.c_box)

/-- A legal player step stays outside the old cavity. -/
private theorem Sealed.player_stays_outside {B : Board w h} {j r y : ℕ}
    {s t : State w h} {a b c : Cell w h} {d : Direction}
    (hs : Sealed B j r y s a b c) (hw : Walls B j r y) (hm : SingleMoveView B d s t) :
    ¬InGap y a c t.player :=
  hs.no_entry hw hm.1.1 hm.1.2.2 hs.outside hm.2.1

/-- Pushing A left requires support inside the cavity. -/
private theorem Sealed.no_A_left {B : Board w h} {j r y : ℕ}
    {s t : State w h} {a b c : Cell w h}
    (hs : Sealed B j r y s a b c) (hm : SingleMoveView B .west s t) : t.player ≠ a := by
  intro he
  have ha : Adjacent .west s.player a := he ▸ hm.2.1
  simp only [Adjacent] at ha
  have hpy : s.player.2.val = y := by have := hs.a_row; omega
  have hpx : s.player.1.val = a.1.val + 1 := by omega
  by_cases hc : s.player.1.val < c.1.val
  · exact hs.outside ⟨hpy, by omega, hc⟩
  · have hec : s.player = c := by
      apply Prod.ext <;> apply Fin.ext
      · have := hs.order; omega
      · have := hs.c_row; omega
    exact hm.1.2.2 (hec ▸ hs.c_box)

/-- Moving C right has the symmetric inaccessible-support obstruction. -/
private theorem Sealed.no_C_right {B : Board w h} {j r y : ℕ}
    {s t : State w h} {a b c : Cell w h}
    (hs : Sealed B j r y s a b c) (hm : SingleMoveView B .east s t) : t.player ≠ c := by
  intro he
  have hc : Adjacent .east s.player c := he ▸ hm.2.1
  simp only [Adjacent] at hc
  have hpy : s.player.2.val = y := by have := hs.c_row; omega
  by_cases ha : a.1.val < s.player.1.val
  · exact hs.outside ⟨hpy, ha, by omega⟩
  · have hea : s.player = a := by
      apply Prod.ext <;> apply Fin.ext
      · have := hs.order; omega
      · have := hs.a_row; omega
    exact hm.1.2.2 (hea ▸ hs.a_box)

/-- The upper blocker stays closed while A lies left of its column. -/
private theorem Sealed.no_B_up {B : Board w h} {j r y : ℕ}
    {s t : State w h} {a b c : Cell w h}
    (hs : Sealed B j r y s a b c) (ha : a.1.val < j)
    (hm : SingleMoveView B .north s t) : t.player ≠ b := by
  intro he
  have hb : Adjacent .north s.player b := he ▸ hm.2.1
  simp only [Adjacent] at hb
  have hbc : b.2.val + 1 = y := hs.blocked.resolve_left (by omega)
  have hpy : s.player.2.val = y := by omega
  have hpx : s.player.1.val = j := by have := hs.b_col; omega
  by_cases hc : j < c.1.val
  · exact hs.outside ⟨hpy, by omega, by omega⟩
  · have hec : s.player = c := by
      apply Prod.ext <;> apply Fin.ext
      · have := hs.order; have := hs.a_lower; omega
      · have := hs.c_row; omega
    exact hm.1.2.2 (hec ▸ hs.c_box)

/-- A push preserving A's horizontal track cannot move its left boundary left. -/
private theorem Sealed.A_monotone {B : Board w h} {j r y : ℕ}
    {s t : State w h} {a b c q : Cell w h} {d : Direction}
    (hs : Sealed B j r y s a b c) (hm : SingleMoveView B d s t)
    (hq : Adjacent d t.player q)
    (hrow : (shiftBox t.player q a).2.val = y) :
    a.1.val ≤ (shiftBox t.player q a).1.val := by
  by_cases ha : a = t.player
  · have hta : t.player = a := ha.symm
    simp only [ha, shiftBox_source] at hrow ⊢
    have harow : t.player.2.val = y := ha ▸ hs.a_row
    cases d with
    | north => simp only [Adjacent] at hq; omega
    | east => simp only [Adjacent] at hq; omega
    | south => simp only [Adjacent] at hq; omega
    | west => exact False.elim (hs.no_A_left hm hta)
  · simp [shiftBox_other ha]

/-- A push preserving C's track cannot move the right boundary right. -/
private theorem Sealed.C_antitone {B : Board w h} {j r y : ℕ}
    {s t : State w h} {a b c q : Cell w h} {d : Direction}
    (hs : Sealed B j r y s a b c) (hm : SingleMoveView B d s t)
    (hq : Adjacent d t.player q)
    (hrow : (shiftBox t.player q c).2.val = y) :
    (shiftBox t.player q c).1.val ≤ c.1.val := by
  by_cases hc : c = t.player
  · have htc : t.player = c := hc.symm
    simp only [hc, shiftBox_source] at hrow ⊢
    have hcrow : t.player.2.val = y := hc ▸ hs.c_row
    cases d with
    | north => simp only [Adjacent] at hq; omega
    | east => exact False.elim (hs.no_C_right hm htc)
    | south => simp only [Adjacent] at hq; omega
    | west => simp only [Adjacent] at hq; omega
  · simp [shiftBox_other hc]

/-- Pushing preserves the blocked upper entrance. -/
private theorem Sealed.blocked_after_push {B : Board w h} {j r y : ℕ}
    {s t : State w h} {a b c q : Cell w h} {d : Direction}
    (hs : Sealed B j r y s a b c) (hm : SingleMoveView B d s t)
    (hq : Adjacent d t.player q)
    (ha : a.1.val ≤ (shiftBox t.player q a).1.val)
    (hbcol : (shiftBox t.player q b).1.val = j)
    (hbrow : (shiftBox t.player q b).2.val < y) :
    j ≤ (shiftBox t.player q a).1.val ∨ (shiftBox t.player q b).2.val + 1 = y := by
  by_cases hopen : j ≤ (shiftBox t.player q a).1.val
  · exact Or.inl hopen
  · apply Or.inr
    have hal : a.1.val < j := by omega
    have hb : b.2.val + 1 = y := hs.blocked.resolve_left (by omega)
    by_cases hmove : b = t.player
    · have htb : t.player = b := hmove.symm
      simp only [hmove, shiftBox_source] at hbcol hbrow ⊢
      have hbc : t.player.1.val = j := hmove ▸ hs.b_col
      have hbr : t.player.2.val + 1 = y := hmove ▸ hb
      cases d with
      | north => exact False.elim (hs.no_B_up hal hm htb)
      | east => simp only [Adjacent] at hq; omega
      | south => simp only [Adjacent] at hq; omega
      | west => simp only [Adjacent] at hq; omega
    · simpa only [shiftBox_other hmove] using hb

/-- Track and order preservation propagate the sealed cavity through a push. -/
private theorem Sealed.after_push {B : Board w h} {j r y : ℕ}
    {s t : State w h} {a b c q : Cell w h} {d : Direction}
    (hs : Sealed B j r y s a b c) (hw : Walls B j r y) (hm : SingleMoveView B d s t)
    (hp : t.player ∈ s.boxes) (hq : Adjacent d t.player q) (_he : q ∉ s.boxes)
    (hboxes : t.boxes = insert q (s.boxes.erase t.player))
    (harow : (shiftBox t.player q a).2.val = y)
    (hcrow : (shiftBox t.player q c).2.val = y)
    (hbcol : (shiftBox t.player q b).1.val = j)
    (hbrow : (shiftBox t.player q b).2.val < y)
    (horder : (shiftBox t.player q a).1.val < (shiftBox t.player q c).1.val) :
    Sealed B j r y t (shiftBox t.player q a) (shiftBox t.player q b) (shiftBox t.player q c) := by
  have hmem : ∀ p ∈ s.boxes, shiftBox t.player q p ∈ t.boxes := by
    intro p hp'
    rw [hboxes, ← image_shiftBox hp]
    exact Finset.mem_image.mpr ⟨p, hp', rfl⟩
  have ha := hs.A_monotone hm hq harow
  have hc := hs.C_antitone hm hq hcrow
  refine ⟨hmem a hs.a_box, hmem b hs.b_box, hmem c hs.c_box, harow, hcrow,
    hbcol, hbrow, ?_, ?_, horder, hs.blocked_after_push hm hq ha hbcol hbrow, ?_⟩
  · have := hs.a_lower
    omega
  · have := hs.c_upper
    omega
  · intro hgap
    apply hs.player_stays_outside hw hm
    obtain ⟨hy, hal, hcl⟩ := hgap
    exact ⟨hy, by omega, by omega⟩

/-- Walking preserves the same barriers and cannot enter their cavity. -/
private theorem Sealed.after_walk {B : Board w h} {j r y : ℕ}
    {s t : State w h} {a b c : Cell w h} {d : Direction}
    (hs : Sealed B j r y s a b c) (hw : Walls B j r y)
    (hm : SingleMoveView B d s t) (hboxes : t.boxes = s.boxes) : Sealed B j r y t a b c := by
  exact ⟨hboxes ▸ hs.a_box, hboxes ▸ hs.b_box, hboxes ▸ hs.c_box,
    hs.a_row, hs.c_row, hs.b_col, hs.b_above, hs.a_lower, hs.c_upper,
    hs.order, hs.blocked, hs.player_stays_outside hw hm⟩


namespace AND

abbrev Shape {w h : ℕ} := PushFS.Gadgets.AND.Shape (w := w) (h := h)
abbrev GeometricStep {w h : ℕ} := PushFS.Gadgets.AND.GeometricStep (w := w) (h := h)

/-- The AND condition under the three threshold meanings. -/
def Good (j r y : ℕ) (S : Configuration w h) : Prop :=
  S.c.1.val ≤ r → S.a.1.val < j ∧ S.b.2.val + 1 < y

/-- A contracted output with at least one blocked input. -/
def Bad (j r y : ℕ) (S : Configuration w h) : Prop :=
  S.c.1.val ≤ r ∧ (j ≤ S.a.1.val ∨ S.b.2.val + 1 = y)

abbrev Sealed (B : Board w h) (j r y : ℕ) (S : Configuration w h) : Prop :=
  FiniteCavity.Sealed B j r y S.state S.a S.b S.c

private theorem Good.not_bad {j r y : ℕ} {S : Configuration w h}
    (hg : Good j r y S) : ¬Bad j r y S := by
  rintro ⟨hc, ha | hb⟩ <;> have := hg hc <;> omega

private theorem Shape.good_or_bad {j r y : ℕ} {S : Configuration w h} (hs : Shape j y S) :
    Good j r y S ∨ Bad j r y S := by
  by_cases hc : S.c.1.val ≤ r
  · by_cases ha : S.a.1.val < j ∧ S.b.2.val + 1 < y
    · exact Or.inl (fun _ => ha)
    · apply Or.inr
      refine ⟨hc, ?_⟩
      have := hs.b_above
      omega
  · exact Or.inl (fun h => False.elim (hc h))

private theorem Sealed.not_good {B : Board w h} {j r y : ℕ} {S : Configuration w h}
    (hs : Sealed B j r y S) : ¬Good j r y S :=
  fun hg => hg.not_bad ⟨hs.c_upper, hs.blocked⟩

/-- The first violation of AND legality leaves the player outside the cavity. -/
private theorem outside_of_becomes_bad {B : Board w h} {j r y : ℕ}
    {S T : Configuration w h} {d : Direction} {q : Cell w h}
    (hS : Shape j y S) (_hT : Shape j y T) (hgood : Good j r y S) (hbad : Bad j r y T)
    (_hm : SingleMoveView B d S.state T.state)
    (ha : T.a = shiftBox T.state.player q S.a)
    (hb : T.b = shiftBox T.state.player q S.b)
    (hc : T.c = shiftBox T.state.player q S.c) :
    ¬InGap y T.a T.c T.state.player := by
  rintro ⟨hpy, hpa, hpc⟩
  obtain ⟨hactive, hblocked⟩ := hbad
  by_cases hmoveA : S.a = T.state.player
  · have hmoveB : S.b ≠ T.state.player := by
      intro hbe
      have := hS.b_above
      have := hS.a_row
      have hrows := congrArg (fun p : Cell w h => p.2.val) (hbe.trans hmoveA.symm)
      omega
    have hmoveC : S.c ≠ T.state.player := by
      intro hce
      have := hS.order
      have hcols := congrArg (fun p : Cell w h => p.1.val) (hce.trans hmoveA.symm)
      omega
    have hB : T.b = S.b := by simpa [shiftBox_other hmoveB] using hb
    have hC : T.c = S.c := by simpa [shiftBox_other hmoveC] using hc
    have hg := hgood (hC ▸ hactive)
    have hpax := congrArg (fun p : Cell w h => p.1.val) hmoveA
    rw [hB] at hblocked
    rcases hblocked with hA | hB <;> omega
  · have hA : T.a = S.a := by simpa [shiftBox_other hmoveA] using ha
    by_cases hmoveC : S.c = T.state.player
    · have hmoveB : S.b ≠ T.state.player := by
        intro hbe
        have := hS.b_above
        have := hS.c_row
        have hrows := congrArg (fun p : Cell w h => p.2.val) (hbe.trans hmoveC.symm)
        omega
      have hB : T.b = S.b := by simpa [shiftBox_other hmoveB] using hb
      have hpcx := congrArg (fun p : Cell w h => p.1.val) hmoveC
      have hg := hgood (by omega)
      rw [hA, hB] at hblocked
      rcases hblocked with hA | hB <;> omega
    · have hC : T.c = S.c := by simpa [shiftBox_other hmoveC] using hc
      by_cases hmoveB : S.b = T.state.player
      · have hby := congrArg (fun p : Cell w h => p.2.val) hmoveB
        have := hS.b_above
        omega
      · have hB : T.b = S.b := by simpa [shiftBox_other hmoveB] using hb
        have hg := hgood (hC ▸ hactive)
        rw [hA, hB] at hblocked
        rcases hblocked with hA | hB <;> omega

/-- Badness and player exclusion seal the cavity. -/
private theorem Shape.sealed_of_bad {B : Board w h} {j r y : ℕ} {S : Configuration w h}
    (hs : Shape j y S) (hb : Bad j r y S) (hp : ¬InGap y S.a S.c S.state.player) :
    Sealed B j r y S :=
  ⟨hs.a_box, hs.b_box, hs.c_box, hs.a_row, hs.c_row, hs.b_col, hs.b_above,
    hs.a_lower, hb.1, hs.order, hb.2, hp⟩

/-- Geometrically admissible steps preserve the sealed cavity. -/
private theorem Sealed.step {B : Board w h} {j r y : ℕ} {S T : Configuration w h}
    (hs : Sealed B j r y S) (hw : Walls B j r y) (ht : GeometricStep B j y S T) :
    Sealed B j r y T := by
  obtain ⟨_, hT, d, hm, hwalk | hpush⟩ := ht
  · obtain ⟨hboxes, ha, hb, hc⟩ := hwalk
    rw [show T = ⟨T.state, S.a, S.b, S.c⟩ by cases T; simp_all] at hT ⊢
    exact hs.after_walk hw hm hboxes
  · obtain ⟨q, hp, hq, he, hboxes, ha, hb, hc⟩ := hpush
    have h := hs.after_push hw hm hp hq he hboxes
      (ha ▸ hT.a_row) (hc ▸ hT.c_row) (hb ▸ hT.b_col) (hb ▸ hT.b_above)
      (by simpa [ha, hc] using hT.order)
    simpa [Sealed, ha, hb, hc] using h

/-- A first violation of AND legality creates the permanent cavity obstruction. -/
private theorem good_or_sealed_step {B : Board w h} {j r y : ℕ} {S T : Configuration w h}
    (hw : Walls B j r y) (hs : Good j r y S ∨ Sealed B j r y S)
    (ht : GeometricStep B j y S T) : Good j r y T ∨ Sealed B j r y T := by
  rcases hs with hgood | hsealed
  · obtain ⟨hS, hT, d, hm, hwalk | hpush⟩ := ht
    · obtain ⟨_, ha, hb, hc⟩ := hwalk
      exact Or.inl (by simpa [Good, ha, hb, hc] using hgood)
    · rcases (Shape.good_or_bad (r := r) hT) with hgoodT | hbadT
      · exact Or.inl hgoodT
      · obtain ⟨q, _, _, _, _, ha, hb, hc⟩ := hpush
        exact Or.inr (Shape.sealed_of_bad hT hbadT
          (outside_of_becomes_bad hS hT hgood hbadT hm ha hb hc))
  · exact Or.inr (hsealed.step hw ht)

/-- The good-or-sealed invariant propagates along a tracked trajectory. -/
private theorem good_or_sealed_reachable {B : Board w h} {j r y : ℕ} {S T : Configuration w h}
    (hw : Walls B j r y) (hs : Good j r y S)
    (hr : Relation.ReflTransGen (GeometricStep B j y) S T) :
    Good j r y T ∨ Sealed B j r y T := by
  induction hr with
  | refl => exact Or.inl hs
  | tail _ hstep ih => exact good_or_sealed_step hw ih hstep

/-- A sealed configuration can never reach any logically legal geometric target. -/
private theorem Sealed.not_reachable_good {B : Board w h} {j r y : ℕ} {S T : Configuration w h}
    (hw : Walls B j r y) (hs : Sealed B j r y S)
    (hr : Relation.ReflTransGen (GeometricStep B j y) S T) : ¬Good j r y T := by
  have ht : Sealed B j r y T := by
    induction hr with
    | refl => exact hs
    | tail _ hstep ih => exact ih.step hw hstep
  exact ht.not_good

/-- AND thresholds hold throughout a successful tracked trajectory. -/
theorem good_on_successful_path {B : Board w h} {j r y : ℕ} {initial S final : Configuration w h}
    (hw : Walls B j r y) (hstart : Good j r y initial) (hfinish : Good j r y final)
    (hbefore : Relation.ReflTransGen (GeometricStep B j y) initial S)
    (hafter : Relation.ReflTransGen (GeometricStep B j y) S final) : Good j r y S := by
  rcases good_or_sealed_reachable hw hstart hbefore with hgood | hsealed
  · exact hgood
  · exact False.elim (hsealed.not_reachable_good hw hafter hfinish)


end AND

namespace OR

abbrev Shape {w h : ℕ} := PushFS.Gadgets.OR.Shape (w := w) (h := h)
abbrev GeometricStep {w h : ℕ} := PushFS.Gadgets.OR.GeometricStep (w := w) (h := h)

def Good (j r y : ℕ) (S : Configuration w h) : Prop :=
  S.c.1.val ≤ r → S.a.1.val + 1 < j ∨ S.b.2.val + 1 < y

def Bad (j r y : ℕ) (S : Configuration w h) : Prop :=
  S.c.1.val ≤ r ∧ j ≤ S.a.1.val + 1 ∧ S.b.2.val + 1 = y

private theorem Shape.good_or_bad {j r y : ℕ} {S : Configuration w h} (hs : Shape j y S) :
    Good j r y S ∨ Bad j r y S := by
  by_cases hc : S.c.1.val ≤ r
  · by_cases hi : S.a.1.val + 1 < j ∨ S.b.2.val + 1 < y
    · exact Or.inl (fun _ => hi)
    · have hby := hs.b_above
      exact Or.inr ⟨hc, by omega, by omega⟩
  · exact Or.inl (fun h => False.elim (hc h))

/-- Every first violation leaves the exact player outside the newly sealed gap. -/
private theorem outside_of_becomes_bad {j r y : ℕ}
    {S T : Configuration w h} {q : Cell w h}
    (hS : Shape j y S) (hgood : Good j r y S) (hbad : Bad j r y T)
    (ha : T.a = shiftBox T.state.player q S.a)
    (hb : T.b = shiftBox T.state.player q S.b)
    (hc : T.c = shiftBox T.state.player q S.c) :
    ¬InGap y T.a T.c T.state.player := by
  rintro ⟨hpy, hpa, hpc⟩
  obtain ⟨hactive, hblockedA, hblockedB⟩ := hbad
  by_cases hmoveA : S.a = T.state.player
  · have hmoveB : S.b ≠ T.state.player := by
      intro hbe
      have := hS.b_above
      have := hS.a_row
      have hrows := congrArg (fun p : Cell w h => p.2.val) (hbe.trans hmoveA.symm)
      omega
    have hmoveC : S.c ≠ T.state.player := by
      intro hce
      have := hS.order
      have hcols := congrArg (fun p : Cell w h => p.1.val) (hce.trans hmoveA.symm)
      omega
    have hB : T.b = S.b := by simpa [shiftBox_other hmoveB] using hb
    have hC : T.c = S.c := by simpa [shiftBox_other hmoveC] using hc
    have hg := hgood (hC ▸ hactive)
    have hpax := congrArg (fun p : Cell w h => p.1.val) hmoveA
    rw [hB] at hblockedB
    omega
  · have hA : T.a = S.a := by simpa [shiftBox_other hmoveA] using ha
    by_cases hmoveC : S.c = T.state.player
    · have hmoveB : S.b ≠ T.state.player := by
        intro hbe
        have := hS.b_above
        have := hS.c_row
        have hrows := congrArg (fun p : Cell w h => p.2.val) (hbe.trans hmoveC.symm)
        omega
      have hB : T.b = S.b := by simpa [shiftBox_other hmoveB] using hb
      have hpcx := congrArg (fun p : Cell w h => p.1.val) hmoveC
      have hg := hgood (by omega)
      rw [hA] at hblockedA
      rw [hB] at hblockedB
      omega
    · have hC : T.c = S.c := by simpa [shiftBox_other hmoveC] using hc
      by_cases hmoveB : S.b = T.state.player
      · have hby := congrArg (fun p : Cell w h => p.2.val) hmoveB
        have := hS.b_above
        omega
      · have hB : T.b = S.b := by simpa [shiftBox_other hmoveB] using hb
        have hg := hgood (hC ▸ hactive)
        rw [hA] at hblockedA
        rw [hB] at hblockedB
        omega

private theorem Shape.sealed_of_bad {B : Board w h} {j r y : ℕ} {S : Configuration w h}
    (hs : Shape j y S) (hb : Bad j r y S) (hp : ¬InGap y S.a S.c S.state.player) :
    AND.Sealed B j r y S :=
  ⟨hs.a_box, hs.b_box, hs.c_box, hs.a_row, hs.c_row, hs.b_col, hs.b_above,
    hb.2.1, hb.1, hs.order, Or.inr hb.2.2, hp⟩

/-- Tracks and order propagate the sealed cavity through an OR step. -/
private theorem sealed_step {B : Board w h} {j r y : ℕ} {S T : Configuration w h}
    (hs : AND.Sealed B j r y S) (hw : Walls B j r y) (ht : GeometricStep B j y S T) :
    AND.Sealed B j r y T := by
  obtain ⟨_, hT, d, hm, hwalk | hpush⟩ := ht
  · obtain ⟨hboxes, ha, hb, hc⟩ := hwalk
    rw [show T = ⟨T.state, S.a, S.b, S.c⟩ by cases T; simp_all] at hT ⊢
    exact hs.after_walk hw hm hboxes
  · obtain ⟨q, hp, hq, he, hboxes, ha, hb, hc⟩ := hpush
    have h := hs.after_push hw hm hp hq he hboxes
      (ha ▸ hT.a_row) (hc ▸ hT.c_row) (hb ▸ hT.b_col) (hb ▸ hT.b_above)
      (by simpa [ha, hc] using hT.order)
    simpa [AND.Sealed, ha, hb, hc] using h

private theorem good_or_sealed_step {B : Board w h} {j r y : ℕ} {S T : Configuration w h}
    (hw : Walls B j r y) (hs : Good j r y S ∨ AND.Sealed B j r y S)
    (ht : GeometricStep B j y S T) : Good j r y T ∨ AND.Sealed B j r y T := by
  rcases hs with hgood | hsealed
  · obtain ⟨hS, hT, d, hm, hwalk | hpush⟩ := ht
    · obtain ⟨_, ha, hb, hc⟩ := hwalk
      exact Or.inl (by simpa [Good, ha, hb, hc] using hgood)
    · rcases (Shape.good_or_bad (r := r) hT) with hg | hbad
      · exact Or.inl hg
      · obtain ⟨q, _, _, _, _, ha, hb, hc⟩ := hpush
        exact Or.inr (Shape.sealed_of_bad hT hbad (outside_of_becomes_bad hS hgood hbad ha hb hc))
  · exact Or.inr (sealed_step hsealed hw ht)

private theorem good_or_sealed_reachable {B : Board w h} {j r y : ℕ} {S T : Configuration w h}
    (hw : Walls B j r y) (hs : Good j r y S)
    (hr : Relation.ReflTransGen (GeometricStep B j y) S T) :
    Good j r y T ∨ AND.Sealed B j r y T := by
  induction hr with
  | refl => exact Or.inl hs
  | tail _ hstep ih => exact good_or_sealed_step hw ih hstep

/-- A legal OR goal with A in its normal range excludes the sealed cavity. -/
private theorem sealed_not_good_normal {B : Board w h} {j r y : ℕ} {S : Configuration w h}
    (hs : AND.Sealed B j r y S) (hA : S.a.1.val < j) : ¬Good j r y S := by
  intro hg
  have hallowed := hg hs.c_upper
  have hlower := hs.a_lower
  have hblocked := hs.blocked
  omega

theorem good_on_successful_path {B : Board w h} {j r y : ℕ}
    {initial S final : Configuration w h}
    (hw : Walls B j r y) (hstart : Good j r y initial) (hfinish : Good j r y final)
    (hfinalA : final.a.1.val < j)
    (hbefore : Relation.ReflTransGen (GeometricStep B j y) initial S)
    (hafter : Relation.ReflTransGen (GeometricStep B j y) S final) : Good j r y S := by
  rcases good_or_sealed_reachable hw hstart hbefore with hg | hsealed
  · exact hg
  · have hfinal : AND.Sealed B j r y final := by
      clear hfinish hfinalA
      induction hafter with
      | refl => exact hsealed
      | tail _ hs ih => exact sealed_step ih hw hs
    exact False.elim (sealed_not_good_normal hfinal hfinalA hfinish)


end OR

end PushPuzzle.PushS.FiniteCavity
