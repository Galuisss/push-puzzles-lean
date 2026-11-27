/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceAxisReadout
public import Mathlib.Data.Finset.Card

/-! Finite hole inventory of genuine complete half-axis words. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceAxisReadout

open PushFS PushS PushS.PortLayout

/-- The actual holes strictly between the frame and central cut of one endpoint's main half-axis. -/
def halfHoles (p : Scales.Parameters) (e : Endpoint) (u : State (p.W + 1) (p.H + 1)) :
    Finset (Cell (p.W + 1) (p.H + 1)) :=
  (holes u).filter fun q => q.1.val = p.x e.port ∧
    0 < (if e.side = .upper then q.2.val else p.H - q.2.val) ∧
      (if e.side = .upper then q.2.val else p.H - q.2.val) < p.D

/-- A genuine complete half-axis word has at most `4−parameter` holes, including its frame gap. -/
theorem endpoint_half_card_le {p : Scales.Parameters} {e : Endpoint}
    {u : State (p.W + 1) (p.H + 1)} {parameter shift : ℕ}
    (word : EndpointAxisReadout p e u parameter shift) :
    (halfHoles p e u).card ≤ 4 - parameter := by
  let depth := fun q : Cell (p.W + 1) (p.H + 1) =>
    if e.side = .upper then q.2.val else p.H - q.2.val
  let index := fun q : Cell (p.W + 1) (p.H + 1) =>
    if depth q ≤ shift then depth q - 1 else depth q - readDepth p e.level
  have hword (q : Cell (p.W + 1) (p.H + 1)) (hq : q ∈ halfHoles p e u) :
      0 < depth q ∧ (depth q ≤ shift ∨
        (shift : ℤ) ≤ (depth q : ℤ) - readDepth p e.level ∧
          (depth q : ℤ) - readDepth p e.level ≤ 3 - (parameter : ℤ)) := by
    obtain ⟨hq, hx, hlo, hhi⟩ := Finset.mem_filter.mp hq
    exact ⟨hlo, (word.axis_holes q hx ⟨hlo, hhi⟩).mp hq⟩
  have hshape (q : Cell (p.W + 1) (p.H + 1)) (hq : q ∈ halfHoles p e u) :
      (index q < shift ∧ depth q = index q + 1) ∨
        (shift ≤ index q ∧ depth q = readDepth p e.level + index q) := by
    have hw := hword q hq
    by_cases hf : depth q ≤ shift
    · left
      simp only [index, ite_eq_left hf]
      omega
    · right
      have hn := hw.2.resolve_left hf
      simp only [index, ite_eq_right hf]
      omega
  have hbound (q : Cell (p.W + 1) (p.H + 1)) (hq : q ∈ halfHoles p e u) : index q < 4 - parameter := by
    have hw := hword q hq
    have hs := word.shift_le
    by_cases hf : depth q ≤ shift
    · simp only [index, ite_eq_left hf]
      omega
    · have hn := hw.2.resolve_left hf
      simp only [index, ite_eq_right hf]
      omega
  have hinj : Set.InjOn index (halfHoles p e u) := by
    intro a ha b hb he
    have hadepth := hshape a ha
    have hbdepth := hshape b hb
    have hdepth : depth a = depth b := by
      rcases hadepth with h | h <;> rcases hbdepth with h' | h' <;> omega
    have hxa := (Finset.mem_filter.mp ha).2.1
    have hxb := (Finset.mem_filter.mp hb).2.1
    apply Prod.ext <;> apply Fin.ext
    · exact hxa.trans hxb.symm
    · have hya := a.2.isLt
      have hyb := b.2.isLt
      dsimp only [depth] at hdepth
      split at hdepth <;> omega
  have hsub : (halfHoles p e u).image index ⊆ Finset.range (4 - parameter) := by
    intro k hk
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_range.mpr (hbound q hq)
  have hc := Finset.card_le_card hsub
  rwa [Finset.card_image_of_injOn hinj, Finset.card_range] at hc

end PushPuzzle.Push.AcceptanceAxisReadout
