/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.QuotasVector
public import PushPush.WholeParallel

/-! Exact sixth-round payment on every divider-neighbour row. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell Direction)
open Push.AcceptanceProgram

theorem TerminalPinRow.divider_neighbors (storage : Bool) (I : Instance) {row g : ℕ}
    (hr : TerminalPinRow I row) (hg : g ∈ (layout storage I).dividers) :
    row ≠ g + 1 ∧ row + 1 ≠ g := by
  rcases hr with ⟨i, hi, a, ha, rfl⟩ | ⟨v, j, p, hp, rfl⟩
  · have ha' : 2 ≤ a ∧ a + 2 ≤ 90 := by
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    have hgap := door_row_divider_gap storage I hi ha'.1 ha'.2 hg
    omega
  · have hgap := room_row_divider_gap storage I v j (offset := 11 + 8 * p)
      (by omega) (by unfold chamberHeight; omega) hg
    unfold inputRow
    omega

private theorem pins_not_divider_neighbor (storage : Bool) (I : Instance) {p : ℕ × ℕ}
    (hpin : p ∈ (layout storage I).pins) (hrow : p.2 ∈ (layout storage I).dividerNeighbors) : False := by
  obtain ⟨g, hg, hr⟩ := List.mem_flatMap.mp hrow
  change p.2 ∈ [g + (layout storage I).shift - 1, g + (layout storage I).shift + 1] at hr
  have hgfit := dividers_fit storage I hg
  have hs := (layout storage I).shift_ge
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases pins_row_cases storage I hpin with hout | ⟨e, he, hsource | hterminal⟩
  · omega
  · have hn := (wires_launch storage I he).divider_neighbors storage I hg
    omega
  · have hn := (wires_terminalPin storage I he).divider_neighbors storage I hg
    change p.2 = Layout.beside e.targetSouth e.target + (layout storage I).shift at hterminal
    omega

private theorem neighbor_row_interior (storage : Bool) (I : Instance) {row : ℕ}
    (hr : row ∈ (layout storage I).dividerNeighbors) :
    0 < row ∧ row + 1 < (layout storage I).height := by
  obtain ⟨g, hg, hr⟩ := List.mem_flatMap.mp hr
  have hb := (layout storage I).translated_bounds (dividers_fit storage I hg)
  change row ∈ [g + (layout storage I).shift - 1, g + (layout storage I).shift + 1] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  omega

theorem neighbor_prefix_goal_empty (storage : Bool) (I : Instance) {p : ℕ × ℕ}
    (hx : p.1 < (layout storage I).rackX)
    (hy : p.2 ∈ (layout storage I).dividerNeighbors) : p ∉ (layout storage I).goalsRaw := by
  intro hb
  rcases Finset.mem_union.mp hb with hf | hgoals
  · rcases Finset.mem_union.mp hf with hf | hblock
    · rcases Finset.mem_union.mp hf with hpin | hrack
      · exact pins_not_divider_neighbor storage I hpin hy
      · have hc := (layout storage I).rack_column hrack
        omega
    · obtain ⟨y, hy', he⟩ := List.mem_map.mp (List.mem_toFinset.mp hblock)
      have he := congrArg Prod.snd he
      obtain ⟨g, hg, hr⟩ := List.mem_flatMap.mp hy
      have hn := target_rows_no_neighbor storage I (List.mem_append_left _ hy') hg
      have hs := (layout storage I).shift_ge
      change p.2 ∈ [g + (layout storage I).shift - 1, g + (layout storage I).shift + 1] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      dsimp at he
      omega
  · obtain ⟨y, hy', he⟩ := List.mem_map.mp (List.mem_toFinset.mp hgoals)
    have he := congrArg Prod.snd he
    obtain ⟨g, hg, hr⟩ := List.mem_flatMap.mp hy
    have hn := target_rows_no_neighbor storage I (List.mem_append_right _ hy') hg
    have hs := (layout storage I).shift_ge
    change p.2 ∈ [g + (layout storage I).shift - 1, g + (layout storage I).shift + 1] at hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    dsimp at he
    omega

def neighborStart (I : Instance) : Finset (Cell (layout false I).width (layout false I).height) :=
  (Push.AcceptanceProgram.emit ((layout false I).quotaTemplates.take 5)
    (layout false I).referenceHoles).remaining

def neighborQuotas (I : Instance) : List (ℕ × ℕ) :=
  (emitReads .west ((layout false I).dividerNeighbors.map fun row => (row, (layout false I).rackX))
    (neighborStart I)).quotas

private theorem private_not_probe (L : Layout) (p : Cell L.width L.height)
    (hx : p.1.val < L.rackX) : p ∉ readRegion .east L.probeRequests := by
  intro hp
  obtain ⟨⟨row, span⟩, hr, _, hs⟩ := (mem_readRegion _ _ p).mp hp
  simp only [Layout.probeRequests, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨y, _, he⟩ | ⟨y, _, he⟩ <;>
    have he := congrArg Prod.snd he <;> dsimp at he <;>
    simp only [prefixRank] at hs <;> unfold Layout.width Layout.rackX at hx he hs <;> omega

theorem neighborStart_prefix (I : Instance)
    (p : Cell (layout false I).width (layout false I).height)
    (hy : p.2.val ∈ (layout false I).dividerNeighbors)
    (hx : p.1.val < (layout false I).rackX) :
    p ∈ neighborStart I ↔ 0 < p.1.val := by
  have hrow := neighbor_row_interior false I hy
  have hwidth : p.1.val + 1 < (layout false I).width := by unfold Layout.width; omega
  have hhole : p ∈ (layout false I).referenceHoles := by
    apply Finset.mem_compl.mpr
    intro hb
    exact neighbor_prefix_goal_empty false I hx hy (((layout false I).mem_raster _ _).mp hb)
  have hprobe := private_not_probe (layout false I) p hx
  have hregion : p ∈ allRegions ((layout false I).quotaTemplates.take 5) ↔ Boundary p := by
    have he : allRegions (w := (layout false I).width) (h := (layout false I).height)
        ((layout false I).quotaTemplates.take 5) =
        allRegions ((layout false I).quotaTemplates.take 3) ∪
          readRegion .east (layout false I).probeRequests := by
      simp [Layout.quotaTemplates, allRegions, Template.region, readRegion, Finset.union_assoc]
    rw [he, Finset.mem_union, frame_region I p]
    simp only [hprobe, or_false]
  change p ∈ (Push.AcceptanceProgram.emit ((layout false I).quotaTemplates.take 5)
    (layout false I).referenceHoles).remaining ↔ _
  rw [emit_remaining, Finset.mem_sdiff, hregion]
  simp only [hhole, true_and, Boundary]
  omega

private theorem neighbor_front_count (I : Instance) {row : ℕ}
    (hr : row ∈ (layout false I).dividerNeighbors) :
    ((neighborStart I).filter fun p => p ∈ (Push.Scan.lineCells .west row).take (layout false I).rackX).card =
      (layout false I).rackX - 1 := by
  let P := (layout false I).rackX
  have hP := (layout false I).rackX_ge
  have hrow := neighbor_row_interior false I hr
  have hwidth : P < (layout false I).width := by unfold Layout.width; omega
  let cells : Fin (P - 1) → Cell (layout false I).width (layout false I).height :=
    fun i => (⟨i.val + 1, by have hi := i.isLt; omega⟩, ⟨row, by omega⟩)
  have hinj : Function.Injective cells := by
    intro i j he
    have hx := congrArg (fun p => p.1.val) he
    apply Fin.ext
    dsimp [cells] at hx
    omega
  have he : ((neighborStart I).filter fun p => p ∈ (Push.Scan.lineCells .west row).take P) =
      Finset.univ.image cells := by
    ext p
    rw [Finset.mem_filter, mem_line_prefix]
    simp only [Direction.lane, prefixRank]
    constructor
    · rintro ⟨hp, hy, hx⟩
      have hpos := (neighborStart_prefix I p (hy ▸ hr) hx).mp hp
      let i : Fin (P - 1) := ⟨p.1.val - 1, by omega⟩
      apply Finset.mem_image.mpr
      refine ⟨i, Finset.mem_univ _, ?_⟩
      apply Prod.ext <;> apply Fin.ext
      · dsimp [cells, i]
        omega
      · exact hy.symm
    · intro hp
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
      have hi := i.isLt
      have hx : (cells i).1.val < (layout false I).rackX := by dsimp [cells]; change i.val + 1 < P; omega
      exact ⟨(neighborStart_prefix I (cells i) hr hx).mpr (by dsimp [cells]; omega), rfl, hx⟩
  rw [he, Finset.card_image_of_injective _ hinj]
  simp [P]

private theorem neighbor_quotaAt (I : Instance) {row : ℕ}
    (hr : row ∈ (layout false I).dividerNeighbors) :
    Push.Scan.quotaAt (neighborQuotas I) row = (layout false I).rackX - 1 := by
  rw [neighborQuotas, emitReads_lane_quota .west _ _ row (layout false I).rackX
    (List.mem_map.mpr ⟨row, hr, rfl⟩) (by
      intro request hm _
      obtain ⟨y, _, rfl⟩ := List.mem_map.mp hm
      rfl)]
  exact neighbor_front_count I hr

theorem sixth_neighbor_full (I : Instance) {row : ℕ}
    (hr : row ∈ (layout false I).dividerNeighbors)
    {E F : Finset (Cell (layout false I).width (layout false I).height)}
    (H : WholeScan.Exec (.read .west (neighborQuotas I) : Round).instructions E F)
    (hcapacity : ∀ p ∈ E, p.2.val = row → 0 < p.1.val ∧ p.1.val < (layout false I).rackX)
    (p : Cell (layout false I).width (layout false I).height) (hy : p.2.val = row)
    (hpos : 0 < p.1.val) (hx : p.1.val < (layout false I).rackX) : p ∈ E := by
  let allowed := (neighborStart I).filter fun p =>
    p ∈ (Push.Scan.lineCells .west row).take (layout false I).rackX
  have hsub : (E.filter fun p => p.2.val = row) ⊆ allowed := by
    intro q hq
    obtain ⟨hq, hqy⟩ := Finset.mem_filter.mp hq
    obtain ⟨hqpos, hqx⟩ := hcapacity q hq hqy
    apply Finset.mem_filter.mpr
    refine ⟨(neighborStart_prefix I q (hqy ▸ hr) hqx).mpr hqpos, ?_⟩
    rw [mem_line_prefix]
    exact ⟨hqy, hqx⟩
  have hread := H.parallel_read .west (neighborQuotas I) row
  have hcard := hread.card
  rw [neighbor_quotaAt I hr] at hcard
  have he : (E.filter fun p => p.2.val = row) = allowed := by
    apply Finset.eq_of_subset_of_card_le hsub
    have ha : allowed.card = (layout false I).rackX - 1 := neighbor_front_count I hr
    change ((F.filter fun p => Direction.west.lane p = row).card) +
      ((layout false I).rackX - 1) = (E.filter fun p => p.2.val = row).card at hcard
    omega
  have hp : p ∈ allowed := Finset.mem_filter.mpr
    ⟨(neighborStart_prefix I p (hy ▸ hr) hx).mpr hpos, by rw [mem_line_prefix]; exact ⟨hy, hx⟩⟩
  rw [← he] at hp
  exact (Finset.mem_filter.mp hp).1

theorem sixth_neighbors_source_empty (I : Instance)
    {s : PushFS.State (layout false I).width (layout false I).height}
    {E F : Finset (Cell (layout false I).width (layout false I).height)}
    (H : WholeScan.Exec (.read .west (neighborQuotas I) : Round).instructions E F)
    (hsub : E ⊆ s.boxesᶜ)
    (hcapacity : ∀ row ∈ (layout false I).dividerNeighbors,
      ∀ p ∈ E, p.2.val = row → 0 < p.1.val ∧ p.1.val < (layout false I).rackX)
    (p : Cell (layout false I).width (layout false I).height)
    (hx : p.1.val = (layout false I).rackX - 1)
    (hy : p.2.val ∈ (layout false I).dividerNeighbors) : p ∉ s.boxes := by
  have hP := (layout false I).rackX_ge
  apply Finset.mem_compl.mp
  apply hsub
  exact sixth_neighbor_full I hy H (hcapacity _ hy) p rfl (by omega) (by omega)

end PushPuzzle.PushPush.Doors.Source
