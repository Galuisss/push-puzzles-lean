/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.AND

/-!
# OR soundness using the same sealed cavity

The OR junction lies one column farther from A than the AND junction. Either
the left opening or the upper opening suffices. A first logical violation seals
the cavity. Subsequent motion may open B after pushing A too far right, but A
then cannot return to its prescribed target range; this is why the target range
is explicit in the final theorem. No canonical slots are assumed in between.
-/

@[expose] public section

namespace PushPuzzle.PushFS.Gadgets.OR


open AND

variable {w h : ℕ}

/-- Track positions and physical identities; A has no lower slot bound here. -/
structure Shape (j y : ℕ) (S : AND.Configuration w h) : Prop where
  a_box : S.a ∈ S.state.boxes
  b_box : S.b ∈ S.state.boxes
  c_box : S.c ∈ S.state.boxes
  a_row : S.a.2.val = y
  c_row : S.c.2.val = y
  b_col : S.b.1.val = j
  b_above : S.b.2.val < y
  order : S.a.1.val < S.c.1.val

def Good (j y : ℕ) (S : AND.Configuration w h) : Prop :=
  S.c.1.val ≤ j + 3 → S.a.1.val + 1 < j ∨ S.b.2.val + 1 < y

def Bad (j y : ℕ) (S : AND.Configuration w h) : Prop :=
  S.c.1.val ≤ j + 3 ∧ j ≤ S.a.1.val + 1 ∧ S.b.2.val + 1 = y

private theorem Shape.good_or_bad {j y : ℕ} {S : AND.Configuration w h} (hs : Shape j y S) :
    Good j y S ∨ Bad j y S := by
  by_cases hc : S.c.1.val ≤ j + 3
  · by_cases hi : S.a.1.val + 1 < j ∨ S.b.2.val + 1 < y
    · exact Or.inl (fun _ => hi)
    · have hby := hs.b_above
      exact Or.inr ⟨hc, by omega, by omega⟩
  · exact Or.inl (fun h => False.elim (hc h))

/-- Every first violation leaves the exact player outside the newly sealed gap. -/
private theorem outside_of_becomes_bad {j y : ℕ}
    {S T : AND.Configuration w h} {q : Cell w h}
    (hS : Shape j y S) (hgood : Good j y S) (hbad : Bad j y T)
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

private theorem Shape.sealed_of_bad {B : Board w h} {j y : ℕ} {S : AND.Configuration w h}
    (hs : Shape j y S) (hb : Bad j y S) (hp : ¬InGap y S.a S.c S.state.player) :
    AND.Sealed B j y S :=
  ⟨hs.a_box, hs.b_box, hs.c_box, hs.a_row, hs.c_row, hs.b_col, hs.b_above,
    hb.2.1, hb.1, hs.order, Or.inr hb.2.2, hp⟩

def GeometricStep (B : Board w h) (j y : ℕ) (S T : AND.Configuration w h) : Prop :=
  Shape j y S ∧ Shape j y T ∧ TrackedStep B S T

/-- Cavity persistence needs only the new state's tracks and ordering, not an
assumption that A is already in the cavity's restricted slot range. -/
private theorem sealed_step {B : Board w h} {j y : ℕ} {S T : AND.Configuration w h}
    (hs : AND.Sealed B j y S) (hw : CavityWalls B j y) (ht : GeometricStep B j y S T) :
    AND.Sealed B j y T := by
  obtain ⟨_, hT, d, hm, hwalk | hpush⟩ := ht
  · obtain ⟨hboxes, ha, hb, hc⟩ := hwalk
    rw [show T = ⟨T.state, S.a, S.b, S.c⟩ by cases T; simp_all] at hT ⊢
    exact hs.after_walk hw hm hboxes
  · obtain ⟨q, hp, hq, he, hboxes, ha, hb, hc⟩ := hpush
    have h := hs.after_push hw hm hp hq he hboxes
      (ha ▸ hT.a_row) (hc ▸ hT.c_row) (hb ▸ hT.b_col) (hb ▸ hT.b_above)
      (by simpa [ha, hc] using hT.order)
    simpa [AND.Sealed, ha, hb, hc] using h

private theorem good_or_sealed_step {B : Board w h} {j y : ℕ} {S T : AND.Configuration w h}
    (hw : CavityWalls B j y) (hs : Good j y S ∨ AND.Sealed B j y S)
    (ht : GeometricStep B j y S T) : Good j y T ∨ AND.Sealed B j y T := by
  rcases hs with hgood | hsealed
  · obtain ⟨hS, hT, d, hm, hwalk | hpush⟩ := ht
    · obtain ⟨_, ha, hb, hc⟩ := hwalk
      exact Or.inl (by simpa [Good, ha, hb, hc] using hgood)
    · rcases hT.good_or_bad with hg | hbad
      · exact Or.inl hg
      · obtain ⟨q, _, _, _, _, ha, hb, hc⟩ := hpush
        exact Or.inr (hT.sealed_of_bad hbad (outside_of_becomes_bad hS hgood hbad ha hb hc))
  · exact Or.inr (sealed_step hsealed hw ht)

private theorem good_or_sealed_reachable {B : Board w h} {j y : ℕ} {S T : AND.Configuration w h}
    (hw : CavityWalls B j y) (hs : Good j y S)
    (hr : Relation.ReflTransGen (GeometricStep B j y) S T) :
    Good j y T ∨ AND.Sealed B j y T := by
  induction hr with
  | refl => exact Or.inl hs
  | tail _ hstep ih => exact good_or_sealed_step hw ih hstep

/-- A sealed state cannot be a logically legal target with A in its prescribed
normal range. This also handles a later reopened B behind a misplaced A. -/
private theorem sealed_not_good_normal {B : Board w h} {j y : ℕ} {S : AND.Configuration w h}
    (hs : AND.Sealed B j y S) (hA : S.a.1.val < j) : ¬Good j y S := by
  intro hg
  have hallowed := hg hs.c_upper
  have hlower := hs.a_lower
  have hblocked := hs.blocked
  omega

theorem good_on_successful_path {B : Board w h} {j y : ℕ}
    {initial S final : AND.Configuration w h}
    (hw : CavityWalls B j y) (hstart : Good j y initial) (hfinish : Good j y final)
    (hfinalA : final.a.1.val < j)
    (hbefore : Relation.ReflTransGen (GeometricStep B j y) initial S)
    (hafter : Relation.ReflTransGen (GeometricStep B j y) S final) : Good j y S := by
  rcases good_or_sealed_reachable hw hstart hbefore with hg | hsealed
  · exact hg
  · have hfinal : AND.Sealed B j y final := by
      clear hfinish hfinalA
      induction hafter with
      | refl => exact hsealed
      | tail _ hs ih => exact sealed_step ih hw hs
    exact False.elim (sealed_not_good_normal hfinal hfinalA hfinish)

end PushPuzzle.PushFS.Gadgets.OR
