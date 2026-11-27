/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateRailStencils

/-! Literal normal-slot coverage by the complete finite-core wall stencils. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteGateStencils

open PushFS FiniteGeometry FiniteGateTracks
open PushFS.Reduction.GateTileRouting.FullGateStatics

attribute [local irreducible] side

inductive AndChart
  | junction | vertical | west | upperCorner | protectionCorner
  deriving DecidableEq

def andChart (w : ℕ) (hw : 2 ≤ w) : AndChart → TranslatedAxisChart (side w) (side w)
  | .junction => andJunction w
  | .vertical => andVertical w hw
  | .west => andWest w hw
  | .upperCorner => andUpperCorner w
  | .protectionCorner => andProtectionCorner w

theorem andChart_walls (w : ℕ) (hw : 2 ≤ w) (c : AndChart)
    (p : Cell (andChart w hw c).width (andChart w hw c).height)
    (hp : p ∈ (andChart w hw c).board.walls) :
    (andChart w hw c).embedding.cells p ∈ andWalls w := by
  cases c with
  | junction => exact andJunction_walls w hw p hp
  | vertical => exact (andVertical_walls w hw p).mpr hp
  | west => exact (andWest_walls w hw p).mpr hp
  | upperCorner => exact andUpperCorner_walls w hw p hp
  | protectionCorner => exact andProtectionCorner_walls w hw p hp

/-- A chart represents the literal ambient coordinate name at a physical cell. -/
def Represents {W H : ℕ} (C : TranslatedAxisChart W H) (p : Cell W H) (t : AxisTrack) : Prop :=
  ∃ q, C.embedding.cells q = p ∧ AxisTrack.shift C.dx C.dy (C.classifier.name q) = t

private theorem represents_of_level {W H : ℕ} {C : TranslatedAxisChart W H}
    {p : Cell W H} {t : AxisTrack} (q : Cell C.width C.height)
    (hq : C.embedding.cells q = p) (ht : t.Supports p)
    (hl : (C.classifier.name q).level = t.level) : Represents C p t := by
  refine ⟨q,hq,?_⟩
  exact supported_level_injective p
    (hq ▸ AxisTrack.shift_supported C.dx C.dy C.fits_x C.fits_y (C.classifier.supported q))
    ht ((AxisTrack.level_shift _ _ _).trans hl)

private theorem andVertical_represents (w : ℕ) (hw : 2 ≤ w) (p : Cell (side w) (side w))
    (hx : p.1.val = origin w-6*w-9)
    (hy : origin w-6*w-21 ≤ p.2.val ∧ p.2.val ≤ origin w) :
    Represents (andVertical w hw) p (.vertical (origin w-6*w-9)) := by
  obtain ⟨q,hq⟩ : ∃ q, (andVertical w hw).embedding.cells q = p :=
    (GridEmbedding.translate_image_iff _ _ (andVertical w hw).fits_x
      (andVertical w hw).fits_y p).mpr (by dsimp [andVertical]; unfold origin at *; omega)
  have hX := congrArg (fun p : Cell (side w) (side w) => p.1.val) hq
  have hqx : q.1 = (1 : Fin 3) := by
    apply Fin.ext
    change q.1.val = 1
    change origin w-6*w-10+q.1.val = p.1.val at hX
    unfold origin at *
    omega
  apply represents_of_level q hq (by simpa only [AxisTrack.Supports] using hx)
  simp only [andVertical,GuardStencils.verticalOfGuard,GuardStencils.verticalName,hqx,ite_true,
    AxisTrack.level]

private theorem andWest_represents (w : ℕ) (hw : 2 ≤ w) (p : Cell (side w) (side w))
    (hy : p.2.val = origin w-6*w-21)
    (hx : origin w-8*w-18 ≤ p.1.val ∧ p.1.val < origin w-8*w-18+(2*w+11)) :
    Represents (andWest w hw) p (.horizontal (origin w-6*w-21)) := by
  obtain ⟨q,hq⟩ : ∃ q, (andWest w hw).embedding.cells q = p :=
    (GridEmbedding.translate_image_iff _ _ (andWest w hw).fits_x
      (andWest w hw).fits_y p).mpr (by dsimp [andWest]; unfold origin at *; omega)
  have hY := congrArg (fun p : Cell (side w) (side w) => p.2.val) hq
  have hqy : q.2 = (1 : Fin 3) := by
    apply Fin.ext
    change q.2.val = 1
    change origin w-6*w-22+q.2.val = p.2.val at hY
    unfold origin at *
    omega
  apply represents_of_level q hq (by simpa only [AxisTrack.Supports] using hy)
  simp only [andWest,GuardStencils.horizontalOfGuard,GuardStencils.horizontalName,hqy,ite_true,
    AxisTrack.level]

private theorem horizontal_represents {W H : ℕ} (C : TranslatedAxisChart W H)
    (row : Fin C.height) (hn : ∀ q, q.2 = row → C.classifier.name q = .horizontal row.val)
    (p : Cell W H) (hx : C.dx ≤ p.1.val ∧ p.1.val < C.dx+C.width)
    (hy : p.2.val = C.dy+row.val) : Represents C p (.horizontal p.2.val) := by
  have hr := row.isLt
  obtain ⟨q,hq⟩ : ∃ q, C.embedding.cells q = p :=
    (GridEmbedding.translate_image_iff _ _ C.fits_x C.fits_y p).mpr (by omega)
  have hY := congrArg (fun p : Cell W H => p.2.val) hq
  have hqy : q.2 = row := by
    apply Fin.ext
    change C.dy+q.2.val = p.2.val at hY
    omega
  refine ⟨q,hq,?_⟩
  rw [hn q hqy]
  exact congrArg AxisTrack.horizontal hy.symm

private theorem junction_vertical_represents {W H : ℕ}
    (C : TranslatedAxisChart W H)
    (j : Fin C.width) (row : Fin C.height)
    (hn : ∀ q, q.1 = j → q.2.val < row.val → C.classifier.name q = .vertical j.val)
    (p : Cell W H) (hx : p.1.val = C.dx+j.val)
    (hy : C.dy ≤ p.2.val ∧ p.2.val < C.dy+row.val) :
    Represents C p (.vertical p.1.val) := by
  have hj := j.isLt
  have hr := row.isLt
  obtain ⟨q,hq⟩ : ∃ q, C.embedding.cells q = p :=
    (GridEmbedding.translate_image_iff _ _ C.fits_x C.fits_y p).mpr (by omega)
  have hX := congrArg (fun p : Cell W H => p.1.val) hq
  have hY := congrArg (fun p : Cell W H => p.2.val) hq
  change C.dx+q.1.val = p.1.val at hX
  change C.dy+q.2.val = p.2.val at hY
  have hqx : q.1 = j := by apply Fin.ext; omega
  have hqy : q.2.val < row.val := by omega
  refine ⟨q,hq,?_⟩
  rw [hn q hqx hqy]
  exact congrArg AxisTrack.vertical hx.symm

private theorem andJunction_horizontal_represents (w : ℕ) (p : Cell (side w) (side w))
    (hy : p.2.val = origin w)
    (hx : origin w-7*w-9 ≤ p.1.val ∧ p.1.val < origin w-7*w-9+(12*w+33)) :
    Represents (andJunction w) p (.horizontal (origin w)) := by
  rw [← hy]
  apply horizontal_represents (andJunction w) (⟨10*w+41,by dsimp [andJunction]; omega⟩)
  · intro q hq
    simp only [andJunction,GuardStencils.junctionClassifier,GuardStencils.junctionName,hq,ite_true]
  · exact hx
  · dsimp [andJunction]
    unfold origin at *
    omega

private theorem andJunction_vertical_represents (w : ℕ) (p : Cell (side w) (side w))
    (hx : p.1.val = origin w+3)
    (hy : origin w-10*w-41 ≤ p.2.val ∧ p.2.val < origin w) :
    Represents (andJunction w) p (.vertical (origin w+3)) := by
  rw [← hx]
  apply junction_vertical_represents (andJunction w)
    (⟨7*w+12,by dsimp [andJunction]; omega⟩) (⟨10*w+41,by dsimp [andJunction]; omega⟩)
  · intro q hq hr
    have hne : q.2 ≠ (⟨10*w+41,by dsimp [andJunction]; omega⟩ : Fin (andJunction w).height) := by
      intro he
      have := congrArg Fin.val he
      omega
    simp only [andJunction,GuardStencils.junctionClassifier,GuardStencils.junctionName,hq,hr,
      ite_true,and_self]
    split_ifs with he
    · exact False.elim (hne he)
    · rfl
  · dsimp [andJunction]
    unfold origin at *
    omega
  · dsimp [andJunction]
    unfold origin at *
    omega

/-- Every complete AND normal box is represented on its actual declared coordinate rail. -/
theorem andNormal_represented (w : ℕ) (hw : 2 ≤ w) (a b c : Bool) (l : AndLabel w) :
    ∃ chart, Represents (andChart w hw chart) (andCell w a b c l) (andTrack w l) := by
  have ha := Bool.toNat_le a
  have hb := Bool.toNat_le b
  have hc := Bool.toNat_le c
  cases l with
  | west i =>
    refine ⟨.west,?_⟩
    apply andWest_represents w hw _ rfl
    have hi := i.isLt
    simp only [andCell,andPoint]
    unfold origin
    omega
  | upper i =>
    refine ⟨.vertical,?_⟩
    apply andVertical_represents w hw _ rfl
    have hi := i.isLt
    simp only [andCell,andPoint]
    unfold origin
    omega
  | middle =>
    refine ⟨.vertical,?_⟩
    apply andVertical_represents w hw _ rfl
    simp only [andCell,andPoint]
    unfold origin
    omega
  | lower i =>
    refine ⟨.vertical,?_⟩
    apply andVertical_represents w hw _ rfl
    have hi := i.isLt
    simp only [andCell,andPoint]
    unfold origin
    omega
  | guard i =>
    refine ⟨.junction,?_⟩
    apply andJunction_horizontal_represents w _ rfl
    have hi := i.isLt
    simp only [andCell,andPoint]
    unfold origin
    omega
  | triggerA =>
    refine ⟨.junction,?_⟩
    apply andJunction_horizontal_represents w _ rfl
    simp only [andCell,andPoint]
    unfold origin
    omega
  | branchB i =>
    refine ⟨.junction,?_⟩
    apply andJunction_vertical_represents w _ rfl
    have hi := i.isLt
    simp only [andCell,andPoint]
    unfold origin
    omega
  | branchC i =>
    refine ⟨.junction,?_⟩
    apply andJunction_horizontal_represents w _ rfl
    have hi := i.isLt
    simp only [andCell,andPoint]
    unfold origin
    omega

private theorem orJunction_horizontal_represents (w : ℕ) (p : Cell (side w) (side w))
    (hy : p.2.val = origin w)
    (hx : origin w-4*w-17 ≤ p.1.val ∧ p.1.val < origin w-4*w-17+(9*w+42)) :
    Represents (orJunction w) p (.horizontal (origin w)) := by
  rw [← hy]
  apply horizontal_represents (orJunction w) (⟨4*w+23,by dsimp [orJunction]; omega⟩)
  · intro q hq
    simp only [orJunction,GuardStencils.junctionClassifier,GuardStencils.junctionName,hq,ite_true]
  · exact hx
  · dsimp [orJunction]
    unfold origin at *
    omega

private theorem orJunction_vertical_represents (w : ℕ) (p : Cell (side w) (side w))
    (hx : p.1.val = origin w+4)
    (hy : origin w-4*w-23 ≤ p.2.val ∧ p.2.val < origin w) :
    Represents (orJunction w) p (.vertical (origin w+4)) := by
  rw [← hx]
  apply junction_vertical_represents (orJunction w)
    (⟨4*w+21,by dsimp [orJunction]; omega⟩) (⟨4*w+23,by dsimp [orJunction]; omega⟩)
  · intro q hq hr
    have hne : q.2 ≠ (⟨4*w+23,by dsimp [orJunction]; omega⟩ : Fin (orJunction w).height) := by
      intro he
      have := congrArg Fin.val he
      omega
    simp only [orJunction,GuardStencils.junctionClassifier,GuardStencils.junctionName,hq,hr,
      ite_true,and_self]
    split_ifs with he
    · exact False.elim (hne he)
    · rfl
  · dsimp [orJunction]
    unfold origin at *
    omega
  · dsimp [orJunction]
    unfold origin at *
    omega

/-- The complete OR normal inventory is represented by its real junction stencil. -/
theorem orNormal_represented (w : ℕ) (hw : 2 ≤ w) (a b c : Bool) (l : OrLabel w) :
    Represents (orJunction w) (orCell w a b c l) (orTrack w l) := by
  have ha := Bool.toNat_le a
  have hb := Bool.toNat_le b
  have hc := Bool.toNat_le c
  cases l with
  | left i =>
    apply orJunction_horizontal_represents w _ rfl
    have hi := i.isLt
    simp only [orCell,orPoint]
    unfold origin
    omega
  | triggerA =>
    apply orJunction_horizontal_represents w _ rfl
    simp only [orCell,orPoint]
    unfold origin
    omega
  | branchB i =>
    apply orJunction_vertical_represents w _ rfl
    have hi := i.isLt
    simp only [orCell,orPoint]
    unfold origin
    omega
  | branchC i =>
    apply orJunction_horizontal_represents w _ rfl
    have hi := i.isLt
    simp only [orCell,orPoint]
    unfold origin
    omega

end PushPuzzle.PushS.FiniteGateStencils
