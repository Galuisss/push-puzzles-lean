/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushFS.AxisStencil

/-! Minimal straight-rail and unrotated gate-junction wall stencils. -/

@[expose] public section
namespace PushPuzzle.PushFS.GuardStencils

variable {w h : ℕ}

/-- A full protecting row immediately below a horizontal rail. -/
def horizontalBoard (y : Fin h) : Board w h :=
  ⟨Finset.univ.filter fun p => p.2.val = y.val+1, ∅⟩

/-- The literal coordinate name of a horizontal rail. -/
def horizontalName (y : Fin h) (p : Cell w h) : AxisTrack :=
  if p.2 = y then .horizontal y.val else .outside

/-- A single guarding side blocks both perpendicular box directions. -/
def horizontalClassifier (y : Fin h) : AxisClassifier (horizontalBoard (w := w) y) where
  name := horizontalName y
  supported p := by unfold horizontalName; split <;> simp_all [AxisTrack.Supports]
  displacement p q hd := by
    obtain ⟨_, d, rear, hr, hq, hrw, hqw⟩ := hd
    by_cases hp : p.2 = y
    · have hpy := congrArg Fin.val hp
      cases d with
      | north =>
        simp only [Adjacent] at hr
        exact False.elim (hrw (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩))
      | east =>
        left
        have hqy : q.2 = y := by apply Fin.ext; simp only [Adjacent] at hq; omega
        simp only [horizontalName, hp, hqy, ite_true]
      | south =>
        simp only [Adjacent] at hq
        exact False.elim (hqw (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩))
      | west =>
        left
        have hqy : q.2 = y := by apply Fin.ext; simp only [Adjacent] at hq; omega
        simp only [horizontalName, hp, hqy, ite_true]
    · exact of_decide_eq_true (AxisTrack.allowed_from_outside
        (show horizontalName y p = .outside from ite_eq_right hp))

/-- A full protecting column immediately right of a vertical rail. -/
def verticalBoard (x : Fin w) : Board w h :=
  ⟨Finset.univ.filter fun p => p.1.val = x.val+1, ∅⟩

def verticalName (x : Fin w) (p : Cell w h) : AxisTrack :=
  if p.1 = x then .vertical x.val else .outside

def verticalClassifier (x : Fin w) : AxisClassifier (verticalBoard (h := h) x) where
  name := verticalName x
  supported p := by unfold verticalName; split <;> simp_all [AxisTrack.Supports]
  displacement p q hd := by
    obtain ⟨_, d, rear, hr, hq, hrw, hqw⟩ := hd
    by_cases hp : p.1 = x
    · have hpx := congrArg Fin.val hp
      cases d with
      | north =>
        left
        have hqx : q.1 = x := by apply Fin.ext; simp only [Adjacent] at hq; omega
        simp only [verticalName, hp, hqx, ite_true]
      | east =>
        simp only [Adjacent] at hq
        exact False.elim (hqw (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩))
      | south =>
        left
        have hqx : q.1 = x := by apply Fin.ext; simp only [Adjacent] at hq; omega
        simp only [verticalName, hp, hqx, ite_true]
      | west =>
        simp only [Adjacent] at hr
        exact False.elim (hrw (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩))
    · exact of_decide_eq_true (AxisTrack.allowed_from_outside
        (show verticalName x p = .outside from ite_eq_right hp))

/-- A horizontal rail and an upper vertical input guarded on its right. -/
def junctionBoard (j : Fin w) (y : Fin h) : Board w h :=
  ⟨Finset.univ.filter fun p =>
    p.2.val = y.val+1 ∨ (p.1.val = j.val+1 ∧ p.2.val < y.val), ∅⟩

/-- The input enters the horizontal rail in the increasing axis-level direction. -/
def junctionName (j : Fin w) (y : Fin h) (p : Cell w h) : AxisTrack :=
  if p.2 = y then .horizontal y.val
  else if p.1 = j ∧ p.2.val < y.val then .vertical j.val else .outside

private theorem junction_horizontal {j : Fin w} {y : Fin h} {p q : Cell w h}
    (hp : p.2 = y) (hd : Displacement (junctionBoard j y) p q) : q.2 = y := by
  have hpy := congrArg Fin.val hp
  obtain ⟨_, d, rear, hr, hq, hrw, hqw⟩ := hd
  cases d with
  | north =>
    simp only [Adjacent] at hr
    exact False.elim (hrw (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl (by omega)⟩))
  | east => apply Fin.ext; simp only [Adjacent] at hq; omega
  | south =>
    simp only [Adjacent] at hq
    exact False.elim (hqw (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl (by omega)⟩))
  | west => apply Fin.ext; simp only [Adjacent] at hq; omega

private theorem junction_vertical {j : Fin w} {y : Fin h} {p q : Cell w h}
    (hp : p.1 = j ∧ p.2.val < y.val) (hd : Displacement (junctionBoard j y) p q) :
    q.2 = y ∨ (q.1 = j ∧ q.2.val < y.val) := by
  have hpx := congrArg Fin.val hp.1
  obtain ⟨_, d, rear, hr, hq, hrw, hqw⟩ := hd
  cases d with
  | north =>
    right
    simp only [Adjacent] at hq
    exact ⟨by apply Fin.ext; omega, by omega⟩
  | east =>
    simp only [Adjacent] at hq
    exact False.elim (hqw (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨by omega, by omega⟩⟩))
  | south =>
    simp only [Adjacent] at hq
    by_cases he : q.2 = y
    · exact Or.inl he
    · right
      have hne : q.2.val ≠ y.val := fun hh => he (Fin.ext hh)
      exact ⟨by apply Fin.ext; omega, by omega⟩
  | west =>
    simp only [Adjacent] at hr
    exact False.elim (hrw (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr ⟨by omega, by omega⟩⟩))

/-- The concrete minimal junction classifies every displacement on arbitrary finite dimensions. -/
def junctionClassifier (j : Fin w) (y : Fin h) : AxisClassifier (junctionBoard j y) where
  name := junctionName j y
  supported p := by unfold junctionName; split_ifs <;> simp_all [AxisTrack.Supports]
  displacement p q hd := by
    by_cases hp : p.2 = y
    · left
      simp only [junctionName, hp, junction_horizontal hp hd, ite_true]
    · by_cases hv : p.1 = j ∧ p.2.val < y.val
      · rcases junction_vertical hv hd with hq | hq
        · right
          simp [junctionName, hp, hq, hv, AxisTrack.level]
        · left
          have hqn : q.2 ≠ y := fun he => Nat.lt_irrefl _ (he ▸ hq.2)
          simp [junctionName, hp, hqn, hv, hq]
      · exact of_decide_eq_true (AxisTrack.allowed_from_outside
          (show junctionName j y p = .outside from by simp only [junctionName, hp, hv, ite_false]))

end PushPuzzle.PushFS.GuardStencils
