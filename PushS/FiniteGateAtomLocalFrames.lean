/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateSelected
public import PushS.FiniteGateRegionBounds

/-! Literal local frames of the selected gate trigger footprints. -/

public section
namespace PushPuzzle.PushS.FiniteGateAtomLocalFrames

open PushFS FiniteGeometry FiniteGateCore FiniteGateMacros FiniteGateState
open FiniteGateAAmbient FiniteGateActiveRegion
open scoped Classical

attribute [local irreducible] FiniteGeometry.side

/-- Erasing the sole moving source leaves every stationary labelled box outside the active footprint. -/
theorem image_erase_frame {N : ℕ} {α : Type} [Fintype α] (slots : α → Cell N N)
    (src : Cell N N) (active : Finset (Cell N N)) (B : Board N N)
    (hd : Disjoint (Finset.univ.image slots) B.walls)
    (hf : ∀ p ∈ active,p ∉ B.walls)
    (hm : ∀ l,slots l ∈ active → slots l = src) :
    FiniteWireFrame.Frame active (GridIsometry.refl N N).embedding B ((Finset.univ.image slots).erase src) where
  floor := hf
  fixed_avoids p hp := by
    intro hh
    obtain ⟨hne,hh⟩ := Finset.mem_erase.mp hh
    obtain ⟨l,_,he⟩ := Finset.mem_image.mp hh
    exact hne (he.symm.trans (hm l (he.symm ▸ hp)))
  fixed_floor := hd.mono_left (Finset.erase_subset _ _)

/-- Membership in the exact push row and adjacent walking lane. -/
theorem parallel_active_iff {W H : ℕ} (hub support src dst : Fin W) (lane row : Fin H) (p : Cell W H) :
    p ∈ FiniteParallelFrames.active hub support src dst lane row ↔
      (p = (support,row) ∨ p = (src,row) ∨ p = (dst,row)) ∨
        (p.2 = lane ∧ min hub.val (min support.val src.val) ≤ p.1.val ∧
          p.1.val ≤ max hub.val (max support.val src.val)) := by
  simp only [FiniteParallelFrames.active,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
    Finset.mem_filter,Finset.mem_univ,true_and]

/-- The exact A-release row cells and its two-cell upper lane. -/
@[expose] def ABackwardShape (w : ℕ) (p : Cell (side w) (side w)) : Prop :=
  (p.2.val = origin w ∧ origin w+1 ≤ p.1.val ∧ p.1.val ≤ origin w+3) ∨
    (p.2.val+1 = origin w ∧ origin w+1 ≤ p.1.val ∧ p.1.val ≤ origin w+2)

theorem a_backward_shape (w : ℕ) (p : Cell (side w) (side w))
    (hp : p ∈ triggerBackwardActive w) : ABackwardShape w p := by
  simp only [triggerBackwardActive,parallel_active_iff,point,Prod.ext_iff,Fin.ext_iff] at hp
  dsimp [ABackwardShape]
  omega

theorem and_A_backward_frame (w : ℕ) (hw : 2 ≤ w) (b c : Bool) :
    FiniteWireFrame.Frame (triggerBackwardActive w) (GridIsometry.refl (side w) (side w)).embedding
      (andBoard w ∅) ((andBoxes w true b c).erase (point w 2 0)) := by
  apply image_erase_frame (andCell w true b c) (point w 2 0) (triggerBackwardActive w) (andBoard w ∅) (andBoxes_disjoint_walls w hw true b c)
  · intro p hp
    have hs := a_backward_shape w p hp
    apply and_core_floor w hw p
    all_goals dsimp [ABackwardShape] at hs; omega
  · intro l hl
    have hs := a_backward_shape w _ hl
    have hb := Bool.toNat_le b
    have hc := Bool.toNat_le c
    cases l <;> simp [ABackwardShape,andCell,andPoint,point,Prod.ext_iff,Fin.ext_iff,origin] at hs ⊢ <;> omega

/-- The prepared A-closing path uses the actual right mouth and the whole row interval to A. -/
@[expose] def AForwardShape (w : ℕ) (p : Cell (side w) (side w)) : Prop :=
  (p.2.val = origin w ∧ origin w+2 ≤ p.1.val ∧ p.1.val ≤ origin w+w+4) ∨
    (p.2.val+1 = origin w ∧ p.1.val = origin w+w+4)

theorem a_forward_shape (w : ℕ) (p : Cell (side w) (side w))
    (hp : p ∈ triggerForwardActive w) : AForwardShape w p := by
  simp only [triggerForwardActive,FiniteMouthFrames.mem_leftActive,point,Prod.ext_iff,Fin.ext_iff] at hp
  dsimp [AForwardShape]
  unfold origin at *
  omega

theorem and_A_forward_frame (w : ℕ) (hw : 2 ≤ w) (b : Bool) :
    FiniteWireFrame.Frame (triggerForwardActive w) (GridIsometry.refl (side w) (side w)).embedding
      (andBoard w ∅) ((andBoxes w true b false).erase (point w 2 0)) := by
  apply image_erase_frame (andCell w true b false) (point w 2 0) (triggerForwardActive w) (andBoard w ∅) (andBoxes_disjoint_walls w hw true b false)
  · intro p hp
    have hs := a_forward_shape w p hp
    apply and_core_floor w hw p
    all_goals dsimp [AForwardShape] at hs; unfold origin at *; omega
  · intro l hl
    have hs := a_forward_shape w _ hl
    have hb := Bool.toNat_le b
    cases l <;> simp [AForwardShape,andCell,andPoint,point,Prod.ext_iff,Fin.ext_iff,origin] at hs ⊢ <;> omega

end PushPuzzle.PushS.FiniteGateAtomLocalFrames
