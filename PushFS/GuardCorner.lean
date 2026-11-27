/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushFS.GuardStencils

/-! A concave corner has two separate straight displacement rails entering one sink. -/

@[expose] public section
namespace PushPuzzle.PushFS.GuardStencils

variable {w h : ℕ}

/-- One roof row and one right-side column protect a west-to-south corner. -/
def cornerBoard (j : Fin w) (y : Fin h) : Board w h :=
  ⟨Finset.univ.filter fun p =>
    (p.2.val+1 = y.val ∧ p.1.val ≤ j.val+1) ∨
      (p.1.val = j.val+1 ∧ y.val ≤ p.2.val+1), ∅⟩

def cornerName (j : Fin w) (y : Fin h) (p : Cell w h) : AxisTrack :=
  if p.1 = j ∧ p.2 = y then .sink j.val y.val
  else if p.2 = y ∧ p.1.val < j.val then .horizontal y.val
  else if p.1 = j ∧ y.val < p.2.val then .vertical j.val else .outside

private theorem corner_sink {j : Fin w} {y : Fin h} {p q : Cell w h}
    (hp : p.1 = j ∧ p.2 = y) (hd : Displacement (cornerBoard j y) p q) : False := by
  have hpx := congrArg Fin.val hp.1
  have hpy := congrArg Fin.val hp.2
  obtain ⟨_, d, rear, hr, hq, hrw, hqw⟩ := hd
  cases d with
  | north =>
    simp only [Adjacent] at hq
    exact hqw (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨by omega, by omega⟩⟩)
  | east =>
    simp only [Adjacent] at hq
    exact hqw (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨by omega, by omega⟩⟩)
  | south =>
    simp only [Adjacent] at hr
    exact hrw (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨by omega, by omega⟩⟩)
  | west =>
    simp only [Adjacent] at hr
    exact hrw (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨by omega, by omega⟩⟩)

private theorem corner_horizontal {j : Fin w} {y : Fin h} {p q : Cell w h}
    (hp : p.2 = y ∧ p.1.val < j.val) (hd : Displacement (cornerBoard j y) p q) :
    q.2 = y ∧ q.1.val ≤ j.val := by
  have hpy := congrArg Fin.val hp.1
  obtain ⟨_, d, rear, hr, hq, hrw, hqw⟩ := hd
  cases d with
  | north =>
    simp only [Adjacent] at hq
    exact False.elim (hqw (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨by omega, by omega⟩⟩))
  | east =>
    simp only [Adjacent] at hq
    exact ⟨by apply Fin.ext; omega, by omega⟩
  | south =>
    simp only [Adjacent] at hr
    exact False.elim (hrw (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨by omega, by omega⟩⟩))
  | west =>
    simp only [Adjacent] at hq
    exact ⟨by apply Fin.ext; omega, by omega⟩

private theorem corner_vertical {j : Fin w} {y : Fin h} {p q : Cell w h}
    (hp : p.1 = j ∧ y.val < p.2.val) (hd : Displacement (cornerBoard j y) p q) :
    q.1 = j ∧ y.val ≤ q.2.val := by
  have hpx := congrArg Fin.val hp.1
  obtain ⟨_, d, rear, hr, hq, hrw, hqw⟩ := hd
  cases d with
  | north =>
    simp only [Adjacent] at hq
    exact ⟨by apply Fin.ext; omega, by omega⟩
  | east =>
    simp only [Adjacent] at hq
    exact False.elim (hqw (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨by omega, by omega⟩⟩))
  | south =>
    simp only [Adjacent] at hq
    exact ⟨by apply Fin.ext; omega, by omega⟩
  | west =>
    simp only [Adjacent] at hr
    exact False.elim (hrw (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨by omega, by omega⟩⟩))

/-- Any represented corner displacement stays on its rail or enters the corner sink. -/
theorem corner_strong {j : Fin w} {y : Fin h} {p q : Cell w h}
    (hp : cornerName j y p ≠ .outside) (hd : Displacement (cornerBoard j y) p q) :
    AxisTrack.strongAllowed (cornerName j y) p q = true := by
  by_cases hs : p.1 = j ∧ p.2 = y
  · exact False.elim (corner_sink hs hd)
  · by_cases hh : p.2 = y ∧ p.1.val < j.val
    · obtain ⟨hqy, hqx⟩ := corner_horizontal hh hd
      have hpj : p.1 ≠ j := by
        intro he; have := congrArg Fin.val he; omega
      have hsource : cornerName j y p = .horizontal y.val := by
        simp [cornerName, hpj, hh]
      by_cases hqj : q.1 = j
      · have htarget : cornerName j y q = .sink j.val y.val := by simp [cornerName, hqj, hqy]
        simp [AxisTrack.strongAllowed, hsource, htarget]
      · have hq : q.1.val < j.val := by
          have hne : q.1.val ≠ j.val := fun h => hqj (Fin.ext h)
          omega
        have htarget : cornerName j y q = .horizontal y.val := by simp [cornerName, hqj, hqy, hq]
        simp [AxisTrack.strongAllowed, hsource, htarget]
    · have hv : p.1 = j ∧ y.val < p.2.val := by
        by_contra h
        exact hp (by simp only [cornerName, hs, hh, h, ite_false])
      obtain ⟨hqj, hqy⟩ := corner_vertical hv hd
      have hpy : p.2 ≠ y := fun he => Nat.lt_irrefl _ (he ▸ hv.2)
      have hsource : cornerName j y p = .vertical j.val := by simp [cornerName, hpy, hv]
      by_cases hqy' : q.2 = y
      · have htarget : cornerName j y q = .sink j.val y.val := by simp [cornerName, hqj, hqy']
        simp [AxisTrack.strongAllowed, hsource, htarget]
      · have hq : y.val < q.2.val := by
          have hne : q.2.val ≠ y.val := fun h => hqy' (Fin.ext h)
          omega
        have htarget : cornerName j y q = .vertical j.val := by simp [cornerName, hqj, hqy', hq]
        simp [AxisTrack.strongAllowed, hsource, htarget]

/-- The coordinate classifier of the actual minimal corner wall stencil. -/
def cornerClassifier (j : Fin w) (y : Fin h) : AxisClassifier (cornerBoard j y) where
  name := cornerName j y
  supported p := by unfold cornerName; split_ifs <;> simp_all [AxisTrack.Supports]
  displacement p q hd := by
    by_cases hp : cornerName j y p = .outside
    · exact of_decide_eq_true (AxisTrack.allowed_from_outside hp)
    · exact of_decide_eq_true (AxisTrack.allowed_of_strong (corner_strong hp hd))

end PushPuzzle.PushFS.GuardStencils
