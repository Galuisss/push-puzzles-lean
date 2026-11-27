/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceAxisReadoutInventory
public import PushS.PortLayoutCoordinates

/-! Exact finite inventory of a genuine endpoint's complete physical half-axis word. -/

public section
namespace PushPuzzle.Push.AcceptanceAxisReadout

open PushFS PushS PushS.PortLayout

/-- Every frame-gap and near-gap index names a distinct actual half-axis hole. -/
private theorem endpoint_half_card_ge {p : Scales.Parameters} {e : Endpoint}
    {u : State (p.W + 1) (p.H + 1)} {parameter shift : ℕ}
    (word : EndpointAxisReadout p e u parameter shift) (hp : e.port < p.axes)
    (hY : 4 ≤ readDepth p e.level) : 4 - parameter ≤ (halfHoles p e u).card := by
  let depth := fun i : Fin (4 - parameter) =>
    if i.val < shift then i.val + 1 else readDepth p e.level + i.val
  have hs := word.shift_le
  have hD := readDepth_add_lt_D p e.level
  have hH : p.H = 2 * p.D := rfl
  have hd (i : Fin (4 - parameter)) : 0 < depth i ∧ depth i < p.D := by
    have hi := i.isLt
    dsimp only [depth]
    split <;> omega
  have hxW := x_add_readLength_lt_W p hp 0
  let f : Fin (4 - parameter) → Cell (p.W + 1) (p.H + 1) := fun i =>
    (⟨p.x e.port, by omega⟩,
      ⟨if e.side = .upper then depth i else p.H - depth i, by
        have hdi := hd i
        split <;> omega⟩)
  have hdepth (i : Fin (4 - parameter)) :
      (if e.side = .upper then (f i).2.val else p.H - (f i).2.val) = depth i := by
    have hdi := hd i
    dsimp only [f]
    split_ifs <;> omega
  have hinj : Function.Injective f := by
    intro i j he
    have hde : depth i = depth j := by
      rw [← hdepth i, ← hdepth j, he]
    apply Fin.ext
    dsimp only [depth] at hde
    split_ifs at hde <;> omega
  have hsub : Finset.univ.image f ⊆ halfHoles p e u := by
    intro q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    have hdi := hd i
    have hhalves : 0 < (if e.side = .upper then (f i).2.val else p.H - (f i).2.val) ∧
        (if e.side = .upper then (f i).2.val else p.H - (f i).2.val) < p.D := by
      rwa [hdepth]
    apply Finset.mem_filter.mpr
    refine ⟨(word.axis_holes (f i) rfl hhalves).mpr ?_, rfl, hhalves⟩
    rw [hdepth]
    have hi := i.isLt
    dsimp only [depth]
    split
    next hf => exact Or.inl (by omega)
    next hf => exact Or.inr ⟨by omega, by omega⟩
  have hc := Finset.card_le_card hsub
  simpa only [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] using hc

/-- The complete physical half-axis has exactly four minus its unique endpoint parameter many holes. -/
theorem endpoint_half_card {p : Scales.Parameters} {e : Endpoint}
    {u : State (p.W + 1) (p.H + 1)} {parameter shift : ℕ}
    (word : EndpointAxisReadout p e u parameter shift) (hp : e.port < p.axes)
    (hY : 4 ≤ readDepth p e.level) : (halfHoles p e u).card + parameter = 4 := by
  have hle := endpoint_half_card_le word
  have hge := endpoint_half_card_ge word hp hY
  have hs := word.shift_le
  omega

end PushPuzzle.Push.AcceptanceAxisReadout
