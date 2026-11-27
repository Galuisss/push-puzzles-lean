/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushFS.DisplacementCheck

/-! Two distinct normal slots in one SCC determine their represented physical axis. -/

@[expose] public section
namespace PushPuzzle.PushFS.AxisClassifier

variable {W H : ℕ} {B : Board W H}

private theorem reach_name_or_lt (C : AxisClassifier B) {p q : Cell W H} (hr : StaticReach B p q) :
    C.name p = C.name q ∨ (C.name p).level < (C.name q).level := by
  induction hr with
  | refl => exact Or.inl rfl
  | tail _ hd ih =>
    rcases ih with he | hl <;> rcases C.displacement _ _ hd with he' | hl'
    · exact Or.inl (he.trans he')
    · exact Or.inr (he ▸ hl')
    · exact Or.inr (he' ▸ hl)
    · exact Or.inr (hl.trans hl')

theorem name_eq_of_sameComponent (C : AxisClassifier B) {p q : Cell W H} (h : SameComponent B p q) :
    C.name p = C.name q := by
  rcases reach_name_or_lt C h.1 with he | hl
  · exact he
  · rcases reach_name_or_lt C h.2 with he | hl'
    · exact he.symm
    · exact False.elim (Nat.lt_asymm hl hl')

/-- Two different heights in one represented SCC force its literal column name. -/
private theorem vertical_of_component (C : AxisClassifier B) {p q : Cell W H}
    (h : SameComponent B p q) (hne : p.2.val ≠ q.2.val) (hl : 1 ≤ (C.name p).level) :
    C.name p = .vertical p.1.val := by
  have hp := C.supported p
  have hq := C.supported q
  rw [← C.name_eq_of_sameComponent h] at hq
  cases hn : C.name p with
  | outside => simp only [hn,AxisTrack.level] at hl; omega
  | horizontal row =>
    simp only [hn,AxisTrack.Supports] at hp hq
    exact False.elim (hne (hp.trans hq.symm))
  | vertical col =>
    simp only [hn,AxisTrack.Supports] at hp
    exact congrArg AxisTrack.vertical hp.symm
  | sink x y =>
    simp only [hn,AxisTrack.Supports] at hp hq
    exact False.elim (hne (hp.2.trans hq.2.symm))

/-- Initial activity and two different columns already determine the horizontal tag. -/
theorem horizontal_of_active_component (C : AxisClassifier B) {p q : Cell W H}
    (h : SameComponent B p q) (hne : p.1.val ≠ q.1.val) (ha : C.name p ≠ .outside) :
    C.name p = .horizontal p.2.val := by
  have hp := C.supported p
  have hq := C.supported q
  rw [← C.name_eq_of_sameComponent h] at hq
  cases hn : C.name p with
  | outside => exact False.elim (ha hn)
  | horizontal row =>
    simp only [hn,AxisTrack.Supports] at hp
    exact congrArg AxisTrack.horizontal hp.symm
  | vertical col =>
    simp only [hn,AxisTrack.Supports] at hp hq
    exact False.elim (hne (hp.trans hq.symm))
  | sink x y =>
    simp only [hn,AxisTrack.Supports] at hp hq
    exact False.elim (hne (hp.1.trans hq.1.symm))

theorem vertical_of_active_component (C : AxisClassifier B) {p q : Cell W H}
    (h : SameComponent B p q) (hne : p.2.val ≠ q.2.val) (ha : C.name p ≠ .outside) :
    C.name p = .vertical p.1.val := by
  apply C.vertical_of_component h hne
  cases hn : C.name p <;> simp_all [AxisTrack.level]

/-- Every represented starting cell has a genuinely straight complete static SCC. -/
theorem component_linear (C : AxisClassifier B) (p : Cell W H) (ha : C.name p ≠ .outside) :
    ComponentLinear (component B p) := by
  have hs (q : Cell W H) (hq : component B q = component B p) : (C.name p).Supports q := by
    have hh := C.supported q
    rw [C.name_eq_of_sameComponent (component_eq_iff.mp hq)] at hh
    exact hh
  cases hn : C.name p with
  | outside => exact False.elim (ha hn)
  | horizontal row =>
    refine Or.inr (fun q r hq hr => Fin.ext ?_)
    have hq' := hs q hq
    have hr' := hs r hr
    simp only [hn,AxisTrack.Supports] at hq' hr'
    exact hq'.trans hr'.symm
  | vertical col =>
    refine Or.inl (fun q r hq hr => Fin.ext ?_)
    have hq' := hs q hq
    have hr' := hs r hr
    simp only [hn,AxisTrack.Supports] at hq' hr'
    exact hq'.trans hr'.symm
  | sink x y =>
    refine Or.inl (fun q r hq hr => Fin.ext ?_)
    have hq' := hs q hq
    have hr' := hs r hr
    simp only [hn,AxisTrack.Supports] at hq' hr'
    exact hq'.1.trans hr'.1.symm

end PushPuzzle.PushFS.AxisClassifier
