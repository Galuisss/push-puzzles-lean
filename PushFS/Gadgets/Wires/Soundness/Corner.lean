/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Soundness.Strip

/-!
# The protected right-angle wire

The horizontal box approaches from the left; the vertical box departs downward.
North and east walls guard their common corner. If both boxes close around it,
the player cannot enter and neither box can reopen its arm. Successful paths
therefore propagate the horizontal phase into the vertical phase.
-/

@[expose] public section

namespace PushPuzzle.PushFS.Gadgets.Wires.Soundness.Corner



variable {w h : ℕ}

structure Walls (B : Board w h) (j y : ℕ) : Prop where
  north : ∀ p : Cell w h, p.1.val = j → p.2.val + 1 = y → p ∈ B.walls
  west : ∀ p : Cell w h, p.1.val + 1 = j → p.2.val = y → p ∈ B.walls

def AtCorner (j y : ℕ) (p : Cell w h) : Prop := p.1.val = j ∧ p.2.val = y

/-- The two physical labels stay on their respective open arms. The shared
corner is excluded because it is an immobile non-goal, as proved above. -/
structure Shape (j y : ℕ) (S : Soundness.Configuration w h) : Prop where
  left_box : S.left ∈ S.state.boxes
  right_box : S.right ∈ S.state.boxes
  left_row : S.left.2.val = y
  left_before : j < S.left.1.val
  right_col : S.right.1.val = j
  right_below : y < S.right.2.val

def Good (j y : ℕ) (S : Soundness.Configuration w h) : Prop :=
  j + 1 < S.left.1.val ∨ y + 1 < S.right.2.val

structure Sealed (j y : ℕ) (S : Soundness.Configuration w h) : Prop extends Shape j y S where
  left_at_end : S.left.1.val = j + 1
  right_at_end : S.right.2.val = y + 1
  outside : ¬AtCorner j y S.state.player

private theorem Sealed.no_entry {B : Board w h} {j y : ℕ} {S : Soundness.Configuration w h}
    (hs : Sealed j y S) (hw : Walls B j y)
    {p q : Cell w h} {d : Direction}
    (hpw : p ∉ B.walls) (hpb : p ∉ S.state.boxes) (hadj : Adjacent d p q) :
    ¬AtCorner j y q := by
  rintro ⟨hqx, hqy⟩
  cases d with
  | north =>
    simp only [Adjacent] at hadj
    have he : p = S.right := by
      apply Prod.ext <;> apply Fin.ext
      · have := hs.right_col; omega
      · have := hs.right_at_end; omega
    exact hpb (he ▸ hs.right_box)
  | west =>
    simp only [Adjacent] at hadj
    have he : p = S.left := by
      apply Prod.ext <;> apply Fin.ext
      · have := hs.left_at_end; omega
      · have := hs.left_row; omega
    exact hpb (he ▸ hs.left_box)
  | south =>
    simp only [Adjacent] at hadj
    exact hpw (hw.north p (by omega) (by omega))
  | east =>
    simp only [Adjacent] at hadj
    exact hpw (hw.west p (by omega) (by omega))

private theorem Sealed.left_unchanged {B : Board w h} {j y : ℕ} {S : Soundness.Configuration w h}
    {t : State w h} {q : Cell w h} {d : Direction}
    (hs : Sealed j y S) (hm : SingleMoveView B d S.state t) (hq : Adjacent d t.player q)
    (hrow : (shiftBox t.player q S.left).2.val = y)
    (hbefore : j < (shiftBox t.player q S.left).1.val) :
    shiftBox t.player q S.left = S.left := by
  by_cases he : S.left = t.player
  · have htp : t.player.1.val = j + 1 := he ▸ hs.left_at_end
    have hty : t.player.2.val = y := he ▸ hs.left_row
    simp only [he, shiftBox_source] at hrow hbefore ⊢
    have hp := hm.2.1
    cases d with
    | north => simp only [Adjacent] at hq; omega
    | west => simp only [Adjacent] at hq; omega
    | south => simp only [Adjacent] at hq; omega
    | east =>
      simp only [Adjacent] at hp
      exact False.elim (hs.outside ⟨by omega, by omega⟩)
  · exact shiftBox_other he

private theorem Sealed.right_unchanged {B : Board w h} {j y : ℕ} {S : Soundness.Configuration w h}
    {t : State w h} {q : Cell w h} {d : Direction}
    (hs : Sealed j y S) (hm : SingleMoveView B d S.state t) (hq : Adjacent d t.player q)
    (hcol : (shiftBox t.player q S.right).1.val = j)
    (hbelow : y < (shiftBox t.player q S.right).2.val) :
    shiftBox t.player q S.right = S.right := by
  by_cases he : S.right = t.player
  · have htp : t.player.2.val = y + 1 := he ▸ hs.right_at_end
    have htx : t.player.1.val = j := he ▸ hs.right_col
    simp only [he, shiftBox_source] at hcol hbelow ⊢
    have hp := hm.2.1
    cases d with
    | north => simp only [Adjacent] at hq; omega
    | west => simp only [Adjacent] at hq; omega
    | east => simp only [Adjacent] at hq; omega
    | south =>
      simp only [Adjacent] at hp
      exact False.elim (hs.outside ⟨by omega, by omega⟩)
  · exact shiftBox_other he

def GeometricStep (B : Board w h) (j y : ℕ) (S T : Soundness.Configuration w h) : Prop :=
  Shape j y S ∧ Shape j y T ∧ Soundness.TrackedStep B S T

private theorem sealed_step {B : Board w h} {j y : ℕ} {S T : Soundness.Configuration w h}
    (hs : Sealed j y S) (hw : Walls B j y) (ht : GeometricStep B j y S T) :
    Sealed j y T := by
  obtain ⟨_, hT, d, hm, hwalk | hpush⟩ := ht
  · obtain ⟨_, hl, hr⟩ := hwalk
    refine ⟨hT, ?_, ?_, hs.no_entry hw hm.1.1 hm.1.2.2 hm.2.1⟩
    · simpa [hl] using hs.left_at_end
    · simpa [hr] using hs.right_at_end
  · obtain ⟨q, _, hq, _, _, hl, hr⟩ := hpush
    have hL : T.left = S.left := hl.trans (hs.left_unchanged hm hq
      (hl ▸ hT.left_row) (hl ▸ hT.left_before))
    have hR : T.right = S.right := hr.trans (hs.right_unchanged hm hq
      (hr ▸ hT.right_col) (hr ▸ hT.right_below))
    refine ⟨hT, ?_, ?_, hs.no_entry hw hm.1.1 hm.1.2.2 hm.2.1⟩
    · simpa [hL] using hs.left_at_end
    · simpa [hR] using hs.right_at_end

private theorem outside_of_becomes_bad {j y : ℕ} {S T : Soundness.Configuration w h} {q : Cell w h}
    (hs : Shape j y S) (hg : Good j y S) (hb : ¬Good j y T)
    (hl : T.left = shiftBox T.state.player q S.left)
    (hr : T.right = shiftBox T.state.player q S.right) :
    ¬AtCorner j y T.state.player := by
  rintro ⟨hx, hy⟩
  have hL : S.left ≠ T.state.player := by
    intro he
    have he' := congrArg (fun p : Cell w h => p.1.val) he
    have := hs.left_before
    omega
  have hR : S.right ≠ T.state.player := by
    intro he
    have he' := congrArg (fun p : Cell w h => p.2.val) he
    have := hs.right_below
    omega
  have hleft : T.left = S.left := by simpa [shiftBox_other hL] using hl
  have hright : T.right = S.right := by simpa [shiftBox_other hR] using hr
  exact hb (by simpa [Good, hleft, hright] using hg)

private theorem good_or_sealed_step {B : Board w h} {j y : ℕ} {S T : Soundness.Configuration w h}
    (hw : Walls B j y) (hs : Good j y S ∨ Sealed j y S)
    (ht : GeometricStep B j y S T) : Good j y T ∨ Sealed j y T := by
  rcases hs with hg | hs
  · obtain ⟨hS, hT, _, _, hwalk | hpush⟩ := ht
    · obtain ⟨_, hl, hr⟩ := hwalk
      exact Or.inl (by simpa [Good, hl, hr] using hg)
    · by_cases hgood : Good j y T
      · exact Or.inl hgood
      · obtain ⟨q, _, _, _, _, hl, hr⟩ := hpush
        have hb := hgood
        simp only [Good, not_or, not_lt] at hb
        have htleft := hT.left_before
        have htright := hT.right_below
        exact Or.inr ⟨hT, by omega, by omega, outside_of_becomes_bad hS hg hgood hl hr⟩
  · exact Or.inr (sealed_step hs hw ht)

theorem good_on_successful_path {B : Board w h} {j y : ℕ}
    {initial S final : Soundness.Configuration w h}
    (hw : Walls B j y) (hstart : Good j y initial) (hfinish : Good j y final)
    (hbefore : Relation.ReflTransGen (GeometricStep B j y) initial S)
    (hafter : Relation.ReflTransGen (GeometricStep B j y) S final) : Good j y S := by
  have hcases : Good j y S ∨ Sealed j y S := by
    clear hafter hfinish
    induction hbefore with
    | refl => exact Or.inl hstart
    | tail _ hstep ih => exact good_or_sealed_step hw ih hstep
  rcases hcases with hg | hs
  · exact hg
  · have hf : Sealed j y final := by
      clear hfinish
      induction hafter with
      | refl => exact hs
      | tail _ hstep ih => exact sealed_step ih hw hstep
    have := hf.left_at_end
    have := hf.right_at_end
    rcases hfinish with hf | hf <;> omega

end PushPuzzle.PushFS.Gadgets.Wires.Soundness.Corner
