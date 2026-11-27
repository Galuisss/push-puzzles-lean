/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateStatics.Cover

/-! Actual supported displacement classifiers determine straight active SCCs independently of goal separation. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics


variable {w h : ℕ} {B : Board w h}

private theorem reach_name (C : AxisClassifier B) {p q : Cell w h} (hr : StaticReach B p q) :
    C.name p=C.name q ∨(C.name p).level<(C.name q).level := by
  induction hr with
  | refl => exact Or.inl rfl
  | tail _ hd ih =>
    rcases ih with he|hl <;> rcases C.displacement _ _ hd with he'|hl'
    · exact Or.inl (he.trans he')
    · exact Or.inr (he ▸hl')
    · exact Or.inr (he' ▸hl)
    · exact Or.inr (hl.trans hl')

theorem component_name (C : AxisClassifier B) {p q : Cell w h}
    (he : component B p=component B q) : C.name p=C.name q := by
  have hs:=component_eq_iff.mp he
  rcases reach_name C hs.1 with he|hl
  · exact he
  · rcases reach_name C hs.2 with he|hl'
    · have hh:=congrArg AxisTrack.level he
      omega
    · exact False.elim (Nat.lt_asymm hl hl')

theorem active_linear (C : AxisClassifier B) (p : Cell w h) (hp : C.name p≠.outside) :
    ComponentLinear (component B p) := by
  cases hn : C.name p with
  | outside => exact False.elim (hp hn)
  | horizontal y =>
    right
    intro q r hq hr
    have hqs:=C.supported q
    have hrs:=C.supported r
    rw [component_name C hq,hn] at hqs
    rw [component_name C hr,hn] at hrs
    exact Fin.ext (hqs.trans hrs.symm)
  | vertical x =>
    left
    intro q r hq hr
    have hqs:=C.supported q
    have hrs:=C.supported r
    rw [component_name C hq,hn] at hqs
    rw [component_name C hr,hn] at hrs
    exact Fin.ext (hqs.trans hrs.symm)
  | sink x y =>
    left
    intro q r hq hr
    have hqs:=C.supported q
    have hrs:=C.supported r
    rw [component_name C hq,hn] at hqs
    rw [component_name C hr,hn] at hrs
    exact Fin.ext (hqs.1.trans hrs.1.symm)

end PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics
