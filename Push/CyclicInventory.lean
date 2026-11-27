/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.Cyclic
public import Push.ColumnScanForward

/-! Actual widened-room inventory pays every auxiliary-row clear in the next cyclic stage. -/

@[expose] public section
namespace PushPuzzle.Push.Cyclic

open PushFS PushS

private theorem turn_mem_holes (I : Push.Instance) (p : Cell I.width I.height) :
    (turnGeometry I.width I.height).cells p ∈ holes (turn I).initial ↔ p ∈ holes I.initial := by
  have hh : (turnGeometry I.width I.height).cells p ∈ holes (turn I).initial ↔
      (turnGeometry I.width I.height).cells p ∉ (turn I).initial.boxes := mem_holes _
  rw [mem_holes]
  apply hh.trans
  have hx := (GridIsometry.reflectX I.width I.height).mem_boxes I.initial p
  have ht := (GridIsometry.transpose I.width I.height).mem_boxes
    ((GridIsometry.reflectX I.width I.height).state I.initial)
    ((GridIsometry.reflectX I.width I.height).cells p)
  change (GridIsometry.transpose I.width I.height).cells
      ((GridIsometry.reflectX I.width I.height).cells p) ∉
      ((GridIsometry.transpose I.width I.height).state
        ((GridIsometry.reflectX I.width I.height).state I.initial)).boxes ↔ p ∉ I.initial.boxes
  exact not_congr (ht.trans hx)

private theorem dock_mem_holes (r : ColumnScan.Input)
    (p : Cell (wideReader r).outputWidth (wideReader r).outputHeight) :
    (dock r).embed p ∈ holes (dock r).compile.initial ↔ p ∈ (wideReader r).empty := by
  change (dock r).embed p ∈ holes ((dock r).extend (dock r).initial).toState ↔ _
  rw [HoleState.holes_toState]
  exact (dock r).embed_mem_extend (dock r).initial p

/-- The cyclic stage initially preserves the exact original source hole bitmap. -/
theorem sourceEmbed_mem_initial (r : ColumnScan.Input) (q : Cell r.width r.height) :
    sourceEmbed r q ∈ holes (nextSource r).initial ↔ q ∈ r.initial.empty := by
  have ht := turn_mem_holes (dock r).compile ((dock r).embed ((wideReader r).embed q))
  have hd := dock_mem_holes r ((wideReader r).embed q)
  exact ht.trans (hd.trans ((wideReader r).embed_mem_empty q))

/-- A literal reserved room cell for each old auxiliary row and each of its `w+2` columns. -/
def reserveCell (r : ColumnScan.Input)
    (q : Fin (r.width + 2) × Fin ((wideReader r).outputHeight - r.height)) :
    Cell (wideReader r).outputWidth (wideReader r).outputHeight :=
  (⟨r.width + 1 + q.1.val, by
    have := q.1.isLt
    change r.width + 1 + q.1.val < r.width + 2 + (r.width + 1 + r.extraWidth)
    omega⟩,
    ⟨r.height + q.2.val, by
      have := q.2.isLt
      have hh : r.height ≤ (wideReader r).outputHeight := by
        change r.height ≤ r.height + (wideReader r).length
        omega
      omega⟩)

private theorem reserveCell_injective (r : ColumnScan.Input) : Function.Injective (reserveCell r) := by
  intro p q he
  have hx := congrArg (fun q => q.1.val) he
  have hy := congrArg (fun q => q.2.val) he
  apply Prod.ext <;> apply Fin.ext
  · change r.width + 1 + p.1.val = r.width + 1 + q.1.val at hx
    omega
  · change r.height + p.2.val = r.height + q.2.val at hy
    omega

/-- Reserved room cells after docking and turning into the next live source. -/
def reserveEmbed (r : ColumnScan.Input)
    (q : Fin (r.width + 2) × Fin ((wideReader r).outputHeight - r.height)) :
    Cell (nextSource r).width (nextSource r).height :=
  (turnGeometry (dock r).outputWidth (dock r).outputHeight).cells ((dock r).embed (reserveCell r q))

private theorem reserveEmbed_injective (r : ColumnScan.Input) : Function.Injective (reserveEmbed r) := by
  intro p q he
  exact reserveCell_injective r ((dock r).embed_injective ((turnGeometry _ _).cells.injective he))

private theorem reserve_mem_initial (r : ColumnScan.Input)
    (q : Fin (r.width + 2) × Fin ((wideReader r).outputHeight - r.height)) :
    reserveEmbed r q ∈ holes (nextSource r).initial := by
  apply (turn_mem_holes (dock r).compile _).mpr
  apply (dock_mem_holes r _).mpr
  apply Finset.mem_union_right
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · change r.width < r.width + 1 + q.1.val
    omega
  · change r.height ≤ r.height + q.2.val
    omega

/-- The original source and the reserved room contribute disjoint actual holes. -/
theorem initial_inventory_lower (r : ColumnScan.Input) :
    r.sourceHoles + (r.width + 2) * ((wideReader r).outputHeight - r.height) ≤
      (holes (nextSource r).initial).card := by
  let A := r.initial.empty.image (sourceEmbed r)
  let R := Finset.univ.image (reserveEmbed r)
  have hA : A ⊆ holes (nextSource r).initial := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact (sourceEmbed_mem_initial r q).mpr hq
  have hR : R ⊆ holes (nextSource r).initial := by
    intro p hp
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hp
    exact reserve_mem_initial r q
  have hd : Disjoint A R := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨b, _, he⟩ := Finset.mem_image.mp hq
    have hx := congrArg (fun q => q.1.val) he
    have ha := a.2.isLt
    change r.height + b.2.val = a.2.val at hx
    omega
  have hc := Finset.card_le_card (Finset.union_subset hA hR)
  rw [Finset.card_union_of_disjoint hd, Finset.card_image_of_injective _ (sourceEmbed_injective r),
    Finset.card_image_of_injective _ (reserveEmbed_injective r)] at hc
  simpa only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, ColumnScan.Input.sourceHoles] using hc

/-- Auxiliary clearing and source-row quotas fit the literal next source's initial inventory. -/
theorem nextQuotas_budget (r : ColumnScan.Input) (rows : List ℕ) (hb : rows.sum ≤ r.sourceHoles) :
    (nextQuotas r rows).sum ≤ (holes (nextSource r).initial).card := by
  have hc := initial_inventory_lower r
  simp only [nextQuotas, List.sum_append, List.sum_replicate, smul_eq_mul, Nat.mul_zero,
    Nat.add_zero]
  rw [Nat.mul_comm]
  omega

/-- The next column-reader input, with all required quotas already justified by the real bitmap. -/
def nextInput (r : ColumnScan.Input) (rows : List ℕ)
    (hlen : rows.length = r.height) (hb : rows.sum ≤ r.sourceHoles) : ColumnScan.Input where
  width := (nextSource r).width
  height := (nextSource r).height
  initial := ⟨(nextSource r).initial.player, holes (nextSource r).initial,
    player_mem_holes (nextSource r).initial_valid⟩
  quotas := nextQuotas r rows
  quotas_width := nextQuotas_length r rows hlen
  quotas_le := nextQuotas_budget r rows hb

@[simp] theorem nextInput_initial (r : ColumnScan.Input) (rows : List ℕ)
    (hlen : rows.length = r.height) (hb : rows.sum ≤ r.sourceHoles) :
    (nextInput r rows hlen hb).initial.toState = (nextSource r).initial := by
  apply State.ext
  · rfl
  · change (nextSource r).initial.boxesᶜᶜ = (nextSource r).initial.boxes
    exact compl_compl _

@[simp] theorem nextInput_corner (r : ColumnScan.Input) (rows : List ℕ)
    (hlen : rows.length = r.height) (hb : rows.sum ≤ r.sourceHoles) :
    (nextInput r rows hlen hb).sourceCorner = (nextSource r).target := by
  have ht := nextSource_target r
  apply Prod.ext <;> apply Fin.ext
  · change (nextSource r).width - 1 = (nextSource r).target.1.val
    omega
  · change (nextSource r).height - 1 = (nextSource r).target.2.val
    omega

end PushPuzzle.Push.Cyclic
