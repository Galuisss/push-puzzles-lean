/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.AlignedPlacement

/-! Supported local classifiers compose by taking the highest represented axis level at each cell. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics

open scoped Classical
set_option maxHeartbeats 1000000

/-- At a fixed cell, a represented level determines the literal row, column or singleton name. -/
theorem supported_level_injective {W H : ℕ} (p : Cell W H) {a b : AxisTrack}
    (ha : a.Supports p) (hb : b.Supports p) (he : a.level=b.level) : a=b := by
  cases a <;> cases b <;> simp_all [AxisTrack.Supports,AxisTrack.level]

structure Mosaic {W H : ℕ} (B : Board W H) (Chart : Type) where
  chart : Chart→TranslatedAxisChart W H
  walls : ∀c,(chart c).embedding.WallsAgree (chart c).board B
  safe : ∀c p,(chart c).classifier.name p≠.outside→∃d q,
    Gadgets.Wires.Catalog.BoundaryAligned (W:=W) (H:=H) (chart d).dx (chart d).dy q ∧
    (chart d).embedding.cells q=(chart c).embedding.cells p ∧
    ((chart c).classifier.name p).level≤((chart d).classifier.name q).level

namespace Mosaic
variable {W H : ℕ} {B : Board W H} {Chart : Type}

def Represents (M : Mosaic B Chart) (p : Cell W H) (t : AxisTrack) : Prop :=
  ∃c q,(M.chart c).embedding.cells q=p ∧AxisTrack.shift (M.chart c).dx (M.chart c).dy ((M.chart c).classifier.name q)=t

noncomputable def name (M : Mosaic B Chart) (p : Cell W H) : AxisTrack :=
  if M.Represents p (.sink p.1.val p.2.val) then .sink p.1.val p.2.val
  else if M.Represents p (.horizontal p.2.val) then .horizontal p.2.val
  else if M.Represents p (.vertical p.1.val) then .vertical p.1.val else .outside

variable (M : Mosaic B Chart)

theorem supported (p : Cell W H) : (M.name p).Supports p := by
  unfold name
  split_ifs <;> simp [AxisTrack.Supports]

theorem represented_supported {p : Cell W H} {t : AxisTrack} (ht : M.Represents p t) : t.Supports p := by
  obtain ⟨c,q,rfl,rfl⟩:=ht
  exact AxisTrack.shift_supported _ _ _ _ ((M.chart c).classifier.supported q)

theorem represented_le {p : Cell W H} {t : AxisTrack} (ht : M.Represents p t) : t.level≤(M.name p).level := by
  have hs:=M.represented_supported ht
  cases t
  · exact Nat.zero_le _
  · change p.2.val=_ at hs
    subst hs
    unfold name
    split_ifs <;> simp_all [AxisTrack.level]
  · change p.1.val=_ at hs
    subst hs
    unfold name
    split_ifs <;> simp_all [AxisTrack.level]
  · change p.1.val=_ ∧p.2.val=_ at hs
    rcases hs with ⟨rfl,rfl⟩
    simp only [name,ht,ite_true,AxisTrack.level,Nat.le_refl]

theorem attained (p : Cell W H) (hp : M.name p≠.outside) : M.Represents p (M.name p) := by
  unfold name at hp ⊢
  split_ifs at * <;> simp_all

theorem source_active (c : Chart) (q : Cell (M.chart c).width (M.chart c).height)
    (hq : (M.chart c).classifier.name q≠.outside) : M.name ((M.chart c).embedding.cells q)≠.outside := by
  have hh:=M.represented_le (show M.Represents ((M.chart c).embedding.cells q)
    (AxisTrack.shift (M.chart c).dx (M.chart c).dy ((M.chart c).classifier.name q)) from ⟨c,q,rfl,rfl⟩)
  intro he
  rw [he,AxisTrack.level_shift] at hh
  cases ht : (M.chart c).classifier.name q <;> simp_all [AxisTrack.level]

/-- The true whole-board classifier follows from actual safe local displacement stencils. -/
noncomputable def classifier : AxisClassifier B where
  name:=M.name
  supported:=M.supported
  displacement p q hd:=by
    by_cases hp : M.name p=.outside
    · exact of_decide_eq_true (AxisTrack.allowed_from_outside hp)
    · obtain ⟨c,p',he,hn⟩:=M.attained p hp
      have ha : (M.chart c).classifier.name p'≠.outside := by
        intro h
        rw [h] at hn
        exact hp hn.symm
      obtain ⟨d,r,hs,hr,hl⟩:=M.safe c p' ha
      have hrp : (M.chart d).embedding.cells r=p := hr.trans he
      let t:=AxisTrack.shift (M.chart d).dx (M.chart d).dy ((M.chart d).classifier.name r)
      have ht : M.Represents p t := ⟨d,r,hrp,rfl⟩
      have hle:=M.represented_le ht
      have hlevel : t.level=(M.name p).level := by
        have hh:=congrArg AxisTrack.level hn
        dsimp only [t] at *
        rw [AxisTrack.level_shift] at hh hle ⊢
        omega
      have hname : t=M.name p := supported_level_injective p (M.represented_supported ht) (M.supported p) hlevel
      obtain ⟨s,heq,hd'⟩:=Gadgets.Wires.Catalog.displacement_aligned
        (M.chart d).dx (M.chart d).dy (M.chart d).fits_x (M.chart d).fits_y
        (M.walls d) hs (hrp.symm ▸hd)
      have hdest : M.Represents q (AxisTrack.shift (M.chart d).dx (M.chart d).dy ((M.chart d).classifier.name s)) :=
        ⟨d,s,heq,rfl⟩
      have hdestle:=M.represented_le hdest
      rcases (M.chart d).classifier.displacement r s hd' with he'|hl'
      · have he'' : M.name p=AxisTrack.shift (M.chart d).dx (M.chart d).dy ((M.chart d).classifier.name s) :=
          hname.symm.trans (congrArg (AxisTrack.shift (M.chart d).dx (M.chart d).dy) he')
        by_cases helevel : (M.name p).level=(M.name q).level
        · left
          exact he''.trans (supported_level_injective q (M.represented_supported hdest) (M.supported q) (he'' ▸helevel))
        · right
          rw [←he''] at hdestle
          omega
      · right
        rw [←hlevel]
        dsimp only [t]
        rw [AxisTrack.level_shift]
        rw [AxisTrack.level_shift] at hdestle
        exact hl'.trans_le hdestle

end Mosaic
end PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics
