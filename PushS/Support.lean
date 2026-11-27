/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushFS.Run

/-! Reverse support from adjacent holes to complete sparse streets. -/

@[expose] public section
namespace PushPuzzle.PushS.Support

open PushFS

variable {w h n : ℕ} {B : Board w h} {cap : Option ℕ}
  {d : Direction} {s t : State w h} {C : Set (Cell w h)}

/-- Every empty cell belongs to the specified support. -/
def Supported (C : Set (Cell w h)) (s : State w h) : Prop :=
  ∀ p, p ∉ s.boxes → p ∈ C

/-- Two adjacent support cells include their complete row or column. -/
def AxisClosed (C : Set (Cell w h)) : Prop :=
  ∀ ⦃d p q⦄, Adjacent d p q → p ∈ C → q ∈ C →
    ∀ r, d.lane r = d.lane p → r ∈ C

/-- A push leaves its old player cell and first box cell as adjacent holes. -/
theorem AxisClosed.push_lane (hC : AxisClosed C) (hs : s.Valid B)
    (r : Run B d s n) (hn : 0 < n)
    (hb : t.boxes = insert (r.cell ⟨n + 1, by omega⟩) (s.boxes.erase (r.cell 1)))
    (ht : Supported C t) : ∀ p, d.lane p = d.lane s.player → p ∈ C := by
  have hlast : r.cell ⟨n + 1, by omega⟩ ≠ s.player := by
    rw [← r.start]
    intro he
    have hi := congrArg Fin.val (r.injective he)
    simp only [Fin.val_zero] at hi
    omega
  have hfirst : r.cell ⟨n + 1, by omega⟩ ≠ r.cell 1 := by
    intro he
    have hi := congrArg Fin.val (r.injective he)
    simp only [Fin.val_one] at hi
    omega
  have hp : s.player ∉ t.boxes := by
    rw [hb]
    simp only [Finset.mem_insert, Finset.mem_erase]
    exact fun h => h.elim (fun he => hlast he.symm) (fun he => hs.2.2 he.2)
  have hq : r.cell 1 ∉ t.boxes := by
    rw [hb]
    simp only [Finset.mem_insert, Finset.mem_erase]
    exact fun h => h.elim (fun he => hfirst he.symm) (fun he => he.1 rfl)
  have ha : Adjacent d s.player (r.cell 1) := by
    simpa only [Fin.castSucc_zero, r.start, Fin.succ_zero_eq_one] using r.adjacent 0
  exact hC ha (ht _ hp) (ht _ hq)

/-- Every cell of an actual push run is in the terminal support. -/
theorem AxisClosed.push_run (hC : AxisClosed C) (hs : s.Valid B)
    (r : Run B d s n) (hn : 0 < n)
    (hb : t.boxes = insert (r.cell ⟨n + 1, by omega⟩) (s.boxes.erase (r.cell 1)))
    (ht : Supported C t) (i : Fin (n + 2)) : r.cell i ∈ C :=
  hC.push_lane hs r hn hb ht _ (r.lane i)

/-- Support propagates backwards through any legal move. -/
private theorem AxisClosed.move_source (hC : AxisClosed C) (hm : Move B cap d s t)
    (ht : Supported C t) : Supported C s := by
  cases hm with
  | walk _ _ _ _ hb => simpa only [Supported, hb] using ht
  | @push n hs hn _ r _ hb =>
    intro p hp
    by_cases he : p = r.cell ⟨n + 1, by omega⟩
    · subst p
      exact hC.push_run hs r hn hb ht _
    · apply ht p
      rw [hb]
      simp only [Finset.mem_insert, Finset.mem_erase]
      exact fun h => h.elim he (fun h => hp h.2)

theorem AxisClosed.step_source (hC : AxisClosed C) (hm : Step B cap s t)
    (ht : Supported C t) : Supported C s :=
  hC.move_source hm.choose_spec ht

/-- A supported endpoint supports every state with a suffix reaching it. -/
theorem AxisClosed.reachable_source (hC : AxisClosed C) (hr : Reachable B cap s t) :
    Supported C t → Supported C s := by
  induction hr with
  | refl => exact id
  | tail _ hm ih => exact fun ht => ih (hC.step_source hm ht)

/-- Selected coordinates contain no consecutive values. -/
def Separated {k : ℕ} (X : Set (Fin k)) : Prop :=
  ∀ ⦃a b⦄, a ∈ X → b ∈ X → a.val + 1 ≠ b.val

/-- The union of selected complete columns and rows. -/
def streets (X : Set (Fin w)) (Y : Set (Fin h)) : Set (Cell w h) :=
  {p | p.1 ∈ X ∨ p.2 ∈ Y}

private theorem horizontal_row {X : Set (Fin w)} {Y : Set (Fin h)}
    (hX : Separated X) {p q : Cell w h} (hp : p ∈ streets X Y)
    (hq : q ∈ streets X Y) (hy : q.2 = p.2) (hx : p.1.val + 1 = q.1.val) :
    p.2 ∈ Y := by
  rcases hp with hp | hp
  · rcases hq with hq | hq
    · exact False.elim (hX hp hq hx)
    · exact hy ▸ hq
  · exact hp

private theorem vertical_column {X : Set (Fin w)} {Y : Set (Fin h)}
    (hY : Separated Y) {p q : Cell w h} (hp : p ∈ streets X Y)
    (hq : q ∈ streets X Y) (hx : q.1 = p.1) (hy : p.2.val + 1 = q.2.val) :
    p.1 ∈ X := by
  rcases hp with hp | hp
  · exact hp
  · rcases hq with hq | hq
    · exact hx ▸ hq
    · exact False.elim (hY hp hq hy)

/-- Sparse complete streets satisfy the reverse support rule. -/
theorem streets_axisClosed {X : Set (Fin w)} {Y : Set (Fin h)}
    (hX : Separated X) (hY : Separated Y) : AxisClosed (streets X Y) := by
  intro d p q ha hp hq r hr
  cases d with
  | north =>
    obtain ⟨hx, hy⟩ := ha
    have hc := vertical_column hY hq hp hx.symm hy
    exact Or.inl ((Fin.ext hr) ▸ (hx ▸ hc))
  | east =>
    obtain ⟨hx, hy⟩ := ha
    have hc := horizontal_row hX hp hq hy hx.symm
    exact Or.inr ((Fin.ext hr) ▸ hc)
  | south =>
    obtain ⟨hx, hy⟩ := ha
    have hc := vertical_column hY hp hq hx hy.symm
    exact Or.inl ((Fin.ext hr) ▸ hc)
  | west =>
    obtain ⟨hx, hy⟩ := ha
    have hc := horizontal_row hX hq hp hy.symm hx
    exact Or.inr ((Fin.ext hr) ▸ (hy ▸ hc))

end PushPuzzle.PushS.Support
