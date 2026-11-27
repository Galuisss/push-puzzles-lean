/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Cavity

/-!
# AND legality along arbitrary successful tracked trajectories

The logical thresholds are A left of the input column, B at least two rows above
the horizontal track, and C contracted to at most three columns right of the
input. Moving A temporarily farther right is allowed.

`TrackedStep` follows the actual physical boxes through a real Push-1 move.
`Shape` records the independently established track/order/geometric bounds; it
contains no logical AND condition and no accessibility or reversibility premise.
Under these geometric facts, any first violation of AND legality creates the
sealed cavity. It stays sealed forever and cannot reach a legal target.
-/

@[expose] public section

namespace PushPuzzle.PushFS.Gadgets.AND



variable {w h : ℕ}

/-- Three physical trigger-box identities, in addition to the exact puzzle state. -/
structure Configuration (w h : ℕ) where
  state : State w h
  a : Cell w h
  b : Cell w h
  c : Cell w h

/-- Geometric facts supplied by track conservation, the protected corner, and
box order. No AND relation or player-region premise is included. -/
structure Shape (j y : ℕ) (S : Configuration w h) : Prop where
  a_box : S.a ∈ S.state.boxes
  b_box : S.b ∈ S.state.boxes
  c_box : S.c ∈ S.state.boxes
  a_row : S.a.2.val = y
  c_row : S.c.2.val = y
  b_col : S.b.1.val = j
  b_above : S.b.2.val < y
  a_lower : j ≤ S.a.1.val + 1
  order : S.a.1.val < S.c.1.val

/-- The actual AND condition under the three threshold meanings. -/
def Good (j y : ℕ) (S : Configuration w h) : Prop :=
  S.c.1.val ≤ j + 3 → S.a.1.val < j ∧ S.b.2.val + 1 < y

/-- A contracted output with at least one blocked input. -/
def Bad (j y : ℕ) (S : Configuration w h) : Prop :=
  S.c.1.val ≤ j + 3 ∧ (j ≤ S.a.1.val ∨ S.b.2.val + 1 = y)

abbrev Sealed (B : Board w h) (j y : ℕ) (S : Configuration w h) : Prop :=
  SealedCavity B j y S.state S.a S.b S.c

private theorem Good.not_bad {j y : ℕ} {S : Configuration w h} (hg : Good j y S) : ¬Bad j y S := by
  rintro ⟨hc, ha | hb⟩ <;> have := hg hc <;> omega

private theorem Shape.good_or_bad {j y : ℕ} {S : Configuration w h} (hs : Shape j y S) :
    Good j y S ∨ Bad j y S := by
  by_cases hc : S.c.1.val ≤ j + 3
  · by_cases ha : S.a.1.val < j ∧ S.b.2.val + 1 < y
    · exact Or.inl (fun _ => ha)
    · apply Or.inr
      refine ⟨hc, ?_⟩
      have := hs.b_above
      omega
  · exact Or.inl (fun h => False.elim (hc h))

private theorem Sealed.not_good {B : Board w h} {j y : ℕ} {S : Configuration w h}
    (hs : Sealed B j y S) : ¬Good j y S :=
  fun hg => hg.not_bad ⟨hs.c_upper, hs.blocked⟩

/-- The exact label update of a real walk or push. -/
def TrackedStep (B : Board w h) (S T : Configuration w h) : Prop :=
  ∃ d, SingleMoveView B d S.state T.state ∧
    ((T.state.boxes = S.state.boxes ∧ T.a = S.a ∧ T.b = S.b ∧ T.c = S.c) ∨
      ∃ q, T.state.player ∈ S.state.boxes ∧ Adjacent d T.state.player q ∧
        q ∉ S.state.boxes ∧ T.state.boxes = insert q (S.state.boxes.erase T.state.player) ∧
        T.a = shiftBox T.state.player q S.a ∧ T.b = shiftBox T.state.player q S.b ∧
        T.c = shiftBox T.state.player q S.c)

/-- If a single actual push first makes the AND condition false, its player is
outside the resulting cavity. This covers output contraction, closing A, and
closing B in one proof, and permits all noncanonical intermediate positions. -/
private theorem outside_of_becomes_bad {B : Board w h} {j y : ℕ}
    {S T : Configuration w h} {d : Direction} {q : Cell w h}
    (hS : Shape j y S) (_hT : Shape j y T) (hgood : Good j y S) (hbad : Bad j y T)
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

/-- Geometry plus badness and the real player's exclusion is the sealed trap. -/
private theorem Shape.sealed_of_bad {B : Board w h} {j y : ℕ} {S : Configuration w h}
    (hs : Shape j y S) (hb : Bad j y S) (hp : ¬InGap y S.a S.c S.state.player) :
    Sealed B j y S :=
  ⟨hs.a_box, hs.b_box, hs.c_box, hs.a_row, hs.c_row, hs.b_col, hs.b_above,
    hs.a_lower, hb.1, hs.order, hb.2, hp⟩

/-- The finite geometric state space retains exact player positions and physical
label updates. Its shape restriction is separately discharged by track geometry. -/
def GeometricStep (B : Board w h) (j y : ℕ) (S T : Configuration w h) : Prop :=
  Shape j y S ∧ Shape j y T ∧ TrackedStep B S T

/-- Once created, a sealed cavity persists under every geometrically admissible
real step. -/
private theorem Sealed.step {B : Board w h} {j y : ℕ} {S T : Configuration w h}
    (hs : Sealed B j y S) (hw : CavityWalls B j y) (ht : GeometricStep B j y S T) :
    Sealed B j y T := by
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
private theorem good_or_sealed_step {B : Board w h} {j y : ℕ} {S T : Configuration w h}
    (hw : CavityWalls B j y) (hs : Good j y S ∨ Sealed B j y S)
    (ht : GeometricStep B j y S T) : Good j y T ∨ Sealed B j y T := by
  rcases hs with hgood | hsealed
  · obtain ⟨hS, hT, d, hm, hwalk | hpush⟩ := ht
    · obtain ⟨_, ha, hb, hc⟩ := hwalk
      exact Or.inl (by simpa [Good, ha, hb, hc] using hgood)
    · rcases hT.good_or_bad with hgoodT | hbadT
      · exact Or.inl hgoodT
      · obtain ⟨q, _, _, _, _, ha, hb, hc⟩ := hpush
        exact Or.inr (hT.sealed_of_bad hbadT
          (outside_of_becomes_bad hS hT hgood hbadT hm ha hb hc))
  · exact Or.inr (hsealed.step hw ht)

/-- The invariant covers arbitrary lengths and arbitrary noncanonical states. -/
private theorem good_or_sealed_reachable {B : Board w h} {j y : ℕ} {S T : Configuration w h}
    (hw : CavityWalls B j y) (hs : Good j y S)
    (hr : Relation.ReflTransGen (GeometricStep B j y) S T) :
    Good j y T ∨ Sealed B j y T := by
  induction hr with
  | refl => exact Or.inl hs
  | tail _ hstep ih => exact good_or_sealed_step hw ih hstep

/-- A sealed configuration can never reach any logically legal geometric target. -/
private theorem Sealed.not_reachable_good {B : Board w h} {j y : ℕ} {S T : Configuration w h}
    (hw : CavityWalls B j y) (hs : Sealed B j y S)
    (hr : Relation.ReflTransGen (GeometricStep B j y) S T) : ¬Good j y T := by
  have ht : Sealed B j y T := by
    induction hr with
    | refl => exact hs
    | tail _ hstep ih => exact ih.step hw hstep
  exact ht.not_good

/-- Every intermediate state of a successful geometric trajectory satisfies the
AND relation. This is the reverse contract, without canonical-state assumptions
on the intermediate configurations. -/
theorem good_on_successful_path {B : Board w h} {j y : ℕ} {initial S final : Configuration w h}
    (hw : CavityWalls B j y) (hstart : Good j y initial) (hfinish : Good j y final)
    (hbefore : Relation.ReflTransGen (GeometricStep B j y) initial S)
    (hafter : Relation.ReflTransGen (GeometricStep B j y) S final) : Good j y S := by
  rcases good_or_sealed_reachable hw hstart hbefore with hgood | hsealed
  · exact hgood
  · exact False.elim (hsealed.not_reachable_good hw hafter hfinish)

end PushPuzzle.PushFS.Gadgets.AND
