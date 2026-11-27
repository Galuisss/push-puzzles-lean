/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Slide
public import Mathlib.Data.Int.Interval

/-! A maximum slide on one line merges two occupied components. -/

@[expose] public section
namespace PushPuzzle.PushPush.Line

/-- First occupied coordinate of every consecutive component. -/
def starts (S : Finset ℤ) : Finset ℤ := S.filter fun x => x - 1 ∉ S

/-- Last occupied coordinate of every consecutive component. -/
def ends (S : Finset ℤ) : Finset ℤ := S.filter fun x => x + 1 ∉ S

private theorem starts_card_eq_ends_card (S : Finset ℤ) : (starts S).card = (ends S).card := by
  have hc : (S.filter fun x => x - 1 ∈ S).card = (S.filter fun x => x + 1 ∈ S).card := by
    apply Finset.card_bij (fun x _ => x - 1)
    · intro x hx
      obtain ⟨hx, hp⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_filter.mpr ⟨hp, by simpa using hx⟩
    · intro x _ y _ he
      omega
    · intro y hy
      obtain ⟨hy, hn⟩ := Finset.mem_filter.mp hy
      exact ⟨y + 1, Finset.mem_filter.mpr ⟨hn, by simpa using hy⟩, by omega⟩
  have hp := Finset.card_filter_add_card_filter_not (s := S) (fun x => x - 1 ∈ S)
  have hq := Finset.card_filter_add_card_filter_not (s := S) (fun x => x + 1 ∈ S)
  change _ + (starts S).card = _ at hp
  change _ + (ends S).card = _ at hq
  omega

/-- Reversing the line preserves its number of occupied components. -/
theorem starts_neg_card (S : Finset ℤ) :
    (starts (S.image (fun x => -x))).card = (starts S).card := by
  rw [starts_card_eq_ends_card]
  apply Finset.card_bij (fun x _ => -x)
  · intro x hx
    obtain ⟨hx, hp⟩ := Finset.mem_filter.mp hx
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
    apply Finset.mem_filter.mpr
    refine ⟨by simpa [← he] using hy, ?_⟩
    intro hn
    apply hp
    exact Finset.mem_image.mpr ⟨-x - 1, hn, by omega⟩
  · intro x _ y _ he
    omega
  · intro y hy
    obtain ⟨hy, hp⟩ := Finset.mem_filter.mp hy
    refine ⟨-y, ?_, by omega⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨y, hy, rfl⟩, ?_⟩
    rintro hn
    obtain ⟨z, hz, he⟩ := Finset.mem_image.mp hn
    have he : z = y - 1 := by omega
    exact hp (he ▸ hz)

/-- Translate one consecutive occupied interval by `k`. -/
def slide (S : Finset ℤ) (a n k : ℤ) : Finset ℤ :=
  (S \ Finset.Icc a (a + n - 1)) ∪ Finset.Icc (a + k) (a + n + k - 1)

theorem mem_slide (S : Finset ℤ) (a n k x : ℤ) :
    x ∈ slide S a n k ↔
      (x ∈ S ∧ (x < a ∨ a + n ≤ x)) ∨ (a + k ≤ x ∧ x < a + n + k) := by
  simp only [slide, Finset.mem_union, Finset.mem_sdiff, Finset.mem_Icc]
  by_cases hx : x ∈ S <;> simp [hx] <;> omega

/-- A detached full run followed by a nonempty gap merges with its stopping component. -/
private theorem starts_slide (S : Finset ℤ) {a n k : ℤ} (hn : 0 < n) (hk : 0 < k)
    (hbefore : a - 1 ∉ S)
    (hfull : ∀ x, a ≤ x → x < a + n → x ∈ S)
    (hclear : ∀ x, a + n ≤ x → x < a + n + k → x ∉ S)
    (hstop : a + n + k ∈ S) :
    starts (slide S a n k) = insert (a + k) ((starts S).erase a |>.erase (a + n + k)) := by
  ext x
  simp only [starts, Finset.mem_filter, mem_slide, Finset.mem_insert, Finset.mem_erase]
  have hxa := hfull x
  have hxp := hfull (x - 1)
  have hca := hclear x
  have hcp := hclear (x - 1)
  have hba : x = a - 1 → x ∉ S := fun he => he ▸ hbefore
  have hbp : x - 1 = a - 1 → x - 1 ∉ S := fun he => he ▸ hbefore
  have hsa : x = a + n + k → x ∈ S := fun he => he ▸ hstop
  have hsp : x - 1 = a + n + k → x - 1 ∈ S := fun he => he ▸ hstop
  clear hfull hclear hbefore hstop
  by_cases hx : x ∈ S <;> by_cases hp : x - 1 ∈ S <;> simp_all <;> omega

/-- Every legal interior maximum slide removes precisely one component. -/
theorem starts_slide_card (S : Finset ℤ) {a n k : ℤ} (hn : 0 < n) (hk : 0 < k)
    (hbefore : a - 1 ∉ S)
    (hfull : ∀ x, a ≤ x → x < a + n → x ∈ S)
    (hclear : ∀ x, a + n ≤ x → x < a + n + k → x ∉ S)
    (hstop : a + n + k ∈ S) :
    (starts (slide S a n k)).card + 1 = (starts S).card := by
  have ha : a ∈ starts S := Finset.mem_filter.mpr ⟨hfull a le_rfl (by omega), hbefore⟩
  have hb : a + n + k ∈ (starts S).erase a := by
    apply Finset.mem_erase.mpr
    refine ⟨by omega, Finset.mem_filter.mpr ⟨hstop, ?_⟩⟩
    exact hclear _ (by omega) (by omega)
  have hnew : a + k ∉ ((starts S).erase a).erase (a + n + k) := by
    intro he
    have hm := Finset.mem_filter.mp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase he))
    by_cases hkn : k < n
    · have hp := hfull (a + k - 1) (by omega) (by omega)
      exact hm.2 hp
    · exact hclear _ (by omega) (by omega) hm.1
  rw [starts_slide S hn hk hbefore hfull hclear hstop,
    Finset.card_insert_of_notMem hnew, Finset.card_erase_of_mem hb,
    Finset.card_erase_of_mem ha]
  have htwo := Finset.card_pos.mpr ⟨_, hb⟩
  rw [Finset.card_erase_of_mem ha] at htwo
  omega

end PushPuzzle.PushPush.Line
