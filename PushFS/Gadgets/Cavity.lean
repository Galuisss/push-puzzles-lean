/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.BoxMotion

/-!
# The protected AND's sealed cavity

Write `j` for the vertical input's column and `y` for the horizontal box row.
The two roof cells are `(j+1,y-1)` and `(j+2,y-1)`; the floor under the three-cell
cavity is fixed wall. The moving left and right boundaries are the physical
boxes A and C. The only possible upper entrance is `(j,y-1)`, occupied by B when
that input is closed.

A bad output contraction leaves the player outside this interval. This file
proves that no subsequent player step can enter it, that A cannot be pushed
left, C cannot be pushed right, and that the blocking B cannot be pushed upward.
-/

@[expose] public section

namespace PushPuzzle.PushFS.Gadgets.AND



variable {w h : ℕ}

/-- The open interval between the two actual horizontal boundary boxes. -/
def InGap (y : ℕ) (a c p : Cell w h) : Prop :=
  p.2.val = y ∧ a.1.val < p.1.val ∧ p.1.val < c.1.val

/-- Only the fixed wall cells around the three-cell cavity are constrained. -/
structure CavityWalls (B : Board w h) (j y : ℕ) : Prop where
  below : ∀ p : Cell w h, p.2.val = y + 1 → j ≤ p.1.val → p.1.val ≤ j + 2 → p ∈ B.walls
  roof : ∀ p : Cell w h, p.2.val + 1 = y →
    (p.1.val = j + 1 ∨ p.1.val = j + 2) → p ∈ B.walls

/-- A contracted cavity specified by the board state and labelled box positions. -/
structure SealedCavity (B : Board w h) (j y : ℕ) (s : State w h)
    (a b c : Cell w h) : Prop where
  a_box : a ∈ s.boxes
  b_box : b ∈ s.boxes
  c_box : c ∈ s.boxes
  a_row : a.2.val = y
  c_row : c.2.val = y
  b_col : b.1.val = j
  b_above : b.2.val < y
  a_lower : j ≤ a.1.val + 1
  c_upper : c.1.val ≤ j + 3
  order : a.1.val < c.1.val
  blocked : j ≤ a.1.val ∨ b.2.val + 1 = y
  outside : ¬InGap y a c s.player

/-- Every outside-to-inside neighbor of the contracted cavity is a wall or one
of its actual boundary boxes. Hence a free player cannot cross that boundary. -/
private theorem SealedCavity.no_entry {B : Board w h} {j y : ℕ} {s : State w h}
    {a b c : Cell w h} (hs : SealedCavity B j y s a b c) (hw : CavityWalls B j y)
    {p q : Cell w h} {d : Direction}
    (hpw : p ∉ B.walls) (hpb : p ∉ s.boxes) (hp : ¬InGap y a c p)
    (hadj : Adjacent d p q) : ¬InGap y a c q := by
  rintro ⟨hqy, hqa, hqc⟩
  have hqx : j ≤ q.1.val ∧ q.1.val ≤ j + 2 := by
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
    · exact hpw (hw.roof p (by omega) (by omega))
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

/-- The real one-step player position remains outside the old cavity, whether
the move walks or pushes a box. -/
private theorem SealedCavity.player_stays_outside {B : Board w h} {j y : ℕ}
    {s t : State w h} {a b c : Cell w h} {d : Direction}
    (hs : SealedCavity B j y s a b c) (hw : CavityWalls B j y) (hm : SingleMoveView B d s t) :
    ¬InGap y a c t.player :=
  hs.no_entry hw hm.1.1 hm.1.2.2 hs.outside hm.2.1

/-- Moving A left requires the player already to be in the sealed cavity (or
inside C when the boundary boxes are adjacent), and is therefore impossible. -/
private theorem SealedCavity.no_A_left {B : Board w h} {j y : ℕ}
    {s t : State w h} {a b c : Cell w h}
    (hs : SealedCavity B j y s a b c) (hm : SingleMoveView B .west s t) : t.player ≠ a := by
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
private theorem SealedCavity.no_C_right {B : Board w h} {j y : ℕ}
    {s t : State w h} {a b c : Cell w h}
    (hs : SealedCavity B j y s a b c) (hm : SingleMoveView B .east s t) : t.player ≠ c := by
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

/-- If A leaves the upper entrance potentially usable, the blocking B cannot
be lifted: its support cell is inside the sealed cavity (or occupied by C). -/
private theorem SealedCavity.no_B_up {B : Board w h} {j y : ℕ}
    {s t : State w h} {a b c : Cell w h}
    (hs : SealedCavity B j y s a b c) (ha : a.1.val < j)
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
private theorem SealedCavity.A_monotone {B : Board w h} {j y : ℕ}
    {s t : State w h} {a b c q : Cell w h} {d : Direction}
    (hs : SealedCavity B j y s a b c) (hm : SingleMoveView B d s t)
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
private theorem SealedCavity.C_antitone {B : Board w h} {j y : ℕ}
    {s t : State w h} {a b c q : Cell w h} {d : Direction}
    (hs : SealedCavity B j y s a b c) (hm : SingleMoveView B d s t)
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

/-- The upper entrance cannot reopen while A stays to its left. B cannot be
pushed upward from outside the cavity, nor downward while staying on its branch. -/
private theorem SealedCavity.blocked_after_push {B : Board w h} {j y : ℕ}
    {s t : State w h} {a b c q : Cell w h} {d : Direction}
    (hs : SealedCavity B j y s a b c) (hm : SingleMoveView B d s t)
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

/-- The sealed-cavity invariant is preserved by an actual push, once the
independently proved track and order invariants are supplied for its three
physical labels. A may move temporarily right, so no canonical-slot premise
appears here. -/
theorem SealedCavity.after_push {B : Board w h} {j y : ℕ}
    {s t : State w h} {a b c q : Cell w h} {d : Direction}
    (hs : SealedCavity B j y s a b c) (hw : CavityWalls B j y) (hm : SingleMoveView B d s t)
    (hp : t.player ∈ s.boxes) (hq : Adjacent d t.player q) (_he : q ∉ s.boxes)
    (hboxes : t.boxes = insert q (s.boxes.erase t.player))
    (harow : (shiftBox t.player q a).2.val = y)
    (hcrow : (shiftBox t.player q c).2.val = y)
    (hbcol : (shiftBox t.player q b).1.val = j)
    (hbrow : (shiftBox t.player q b).2.val < y)
    (horder : (shiftBox t.player q a).1.val < (shiftBox t.player q c).1.val) :
    SealedCavity B j y t (shiftBox t.player q a) (shiftBox t.player q b) (shiftBox t.player q c) := by
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
theorem SealedCavity.after_walk {B : Board w h} {j y : ℕ}
    {s t : State w h} {a b c : Cell w h} {d : Direction}
    (hs : SealedCavity B j y s a b c) (hw : CavityWalls B j y)
    (hm : SingleMoveView B d s t) (hboxes : t.boxes = s.boxes) : SealedCavity B j y t a b c := by
  exact ⟨hboxes ▸ hs.a_box, hboxes ▸ hs.b_box, hboxes ▸ hs.c_box,
    hs.a_row, hs.c_row, hs.b_col, hs.b_above, hs.a_lower, hs.c_upper,
    hs.order, hs.blocked, hs.player_stays_outside hw hm⟩

end PushPuzzle.PushFS.Gadgets.AND
