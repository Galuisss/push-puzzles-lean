/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushFS.GuardStencils

/-! Rail classifiers whose protecting wall may switch sides at a flip. -/

@[expose] public section
namespace PushPuzzle.PushFS.GuardStencils

variable {w h : ℕ} {B : Board w h}

/-- Every cross-section through the row has a wall above or below. -/
def HorizontalGuard (B : Board w h) (y : Fin h) : Prop :=
  ∀ (x : Fin w) (u v : Fin h), u.val+1 = y.val → y.val+1 = v.val →
    (x,u) ∈ B.walls ∨ (x,v) ∈ B.walls

private theorem horizontal_guard_motion {y : Fin h} (G : HorizontalGuard B y)
    {p q : Cell w h} (hp : p.2 = y) (hd : Displacement B p q) : q.2 = y := by
  have hpy := congrArg Fin.val hp
  obtain ⟨_, d, rear, hr, hq, hrw, hqw⟩ := hd
  cases d with
  | north =>
    simp only [Adjacent] at hr hq
    rcases G p.1 q.2 rear.2 (by omega) (by omega) with hwq | hwr
    · exact False.elim (hqw ((show (p.1,q.2) = q from Prod.ext hq.1.symm rfl) ▸ hwq))
    · exact False.elim (hrw ((show (p.1,rear.2) = rear from Prod.ext hr.1 rfl) ▸ hwr))
  | east => simp only [Adjacent] at hq; exact hq.2.trans hp
  | south =>
    simp only [Adjacent] at hr hq
    rcases G p.1 rear.2 q.2 (by omega) (by omega) with hwr | hwq
    · exact False.elim (hrw ((show (p.1,rear.2) = rear from Prod.ext hr.1 rfl) ▸ hwr))
    · exact False.elim (hqw ((show (p.1,q.2) = q from Prod.ext hq.1.symm rfl) ▸ hwq))
  | west => simp only [Adjacent] at hq; exact hq.2.trans hp

/-- A full horizontal rail remains straight through arbitrary side changes of its guarding walls. -/
def horizontalOfGuard (y : Fin h) (G : HorizontalGuard B y) : AxisClassifier B where
  name := horizontalName y
  supported p := by unfold horizontalName; split <;> simp_all [AxisTrack.Supports]
  displacement p q hd := by
    by_cases hp : p.2 = y
    · left
      simp only [horizontalName, hp, horizontal_guard_motion G hp hd, ite_true]
    · exact of_decide_eq_true (AxisTrack.allowed_from_outside
        (show horizontalName y p = .outside from ite_eq_right hp))

/-- Every cross-section through the column has a wall to its left or right. -/
def VerticalGuard (B : Board w h) (x : Fin w) : Prop :=
  ∀ (y : Fin h) (u v : Fin w), u.val+1 = x.val → x.val+1 = v.val →
    (u,y) ∈ B.walls ∨ (v,y) ∈ B.walls

private theorem vertical_guard_motion {x : Fin w} (G : VerticalGuard B x)
    {p q : Cell w h} (hp : p.1 = x) (hd : Displacement B p q) : q.1 = x := by
  have hpx := congrArg Fin.val hp
  obtain ⟨_, d, rear, hr, hq, hrw, hqw⟩ := hd
  cases d with
  | north => simp only [Adjacent] at hq; exact hq.1.trans hp
  | east =>
    simp only [Adjacent] at hr hq
    rcases G p.2 rear.1 q.1 (by omega) (by omega) with hwr | hwq
    · exact False.elim (hrw ((show (rear.1,p.2) = rear from Prod.ext rfl hr.2) ▸ hwr))
    · exact False.elim (hqw ((show (q.1,p.2) = q from Prod.ext rfl hq.2.symm) ▸ hwq))
  | south => simp only [Adjacent] at hq; exact hq.1.trans hp
  | west =>
    simp only [Adjacent] at hr hq
    rcases G p.2 q.1 rear.1 (by omega) (by omega) with hwq | hwr
    · exact False.elim (hqw ((show (q.1,p.2) = q from Prod.ext rfl hq.2.symm) ▸ hwq))
    · exact False.elim (hrw ((show (rear.1,p.2) = rear from Prod.ext rfl hr.2) ▸ hwr))

def verticalOfGuard (x : Fin w) (G : VerticalGuard B x) : AxisClassifier B where
  name := verticalName x
  supported p := by unfold verticalName; split <;> simp_all [AxisTrack.Supports]
  displacement p q hd := by
    by_cases hp : p.1 = x
    · left
      simp only [verticalName, hp, vertical_guard_motion G hp hd, ite_true]
    · exact of_decide_eq_true (AxisTrack.allowed_from_outside
        (show verticalName x p = .outside from ite_eq_right hp))

end PushPuzzle.PushFS.GuardStencils
