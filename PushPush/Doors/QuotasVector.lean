/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.QuotasFrame
public import PushPush.Doors.QuotasCuts
public import Push.AcceptanceProgramEmissionFormula
public import PushPush.Doors.WireSourceClear
public import Push.ScanLaneProjection
import all Push.Scan

/-! Literal fourth-round quotas at the first occurrence of every requested probe row. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors

open PushFS (Cell Direction)
open Push.AcceptanceProgram

private theorem east_front_count {w h lane quota : ℕ} (E : Finset (Cell w h))
    (hw : quota + 2 ≤ w) (hlane : lane < h)
    (hpattern : ∀ p : Cell w h, p.2.val = lane → w - 1 - p.1.val < quota + 1 →
      (p ∈ E ↔ p.1.val + 1 < w)) :
    (E.filter fun p => p ∈ (Push.Scan.lineCells .east lane).take (quota + 1)).card = quota := by
  let cells : Fin quota → Cell w h := fun i =>
    (⟨w - 2 - i.val, by have hi := i.isLt; omega⟩, ⟨lane, hlane⟩)
  have hinj : Function.Injective cells := by
    intro i j he
    have he := congrArg (fun p => p.1.val) he
    have hi := i.isLt
    have hj := j.isLt
    apply Fin.ext
    dsimp [cells] at he
    omega
  have he : (E.filter fun p => p ∈ (Push.Scan.lineCells .east lane).take (quota + 1)) =
      Finset.univ.image cells := by
    ext p
    rw [Finset.mem_filter, mem_line_prefix]
    simp only [Direction.lane, prefixRank]
    constructor
    · rintro ⟨hp, hy, hx⟩
      have hb := (hpattern p hy hx).mp hp
      let i : Fin quota := ⟨w - 2 - p.1.val, by have hp := p.1.isLt; omega⟩
      apply Finset.mem_image.mpr
      refine ⟨i, Finset.mem_univ _, ?_⟩
      apply Prod.ext <;> apply Fin.ext
      · dsimp [cells, i]
        omega
      · exact hy.symm
    · intro hp
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
      have hi := i.isLt
      have hy : (cells i).2.val = lane := rfl
      have hx : w - 1 - (cells i).1.val < quota + 1 := by dsimp [cells]; omega
      exact ⟨(hpattern _ hy hx).mpr (by dsimp [cells]; omega), hy, hx⟩
  rw [he, Finset.card_image_of_injective _ hinj]
  simp

/-- The summed quota of one lane is exactly its literal front, even when it occurs repeatedly. -/
theorem emitReads_lane_quota {w h : ℕ} (side : Direction) (requests : List (ℕ × ℕ))
    (E : Finset (Cell w h)) (lane span : ℕ) (hmem : (lane, span) ∈ requests)
    (hspan : ∀ request ∈ requests, request.1 = lane → request.2 = span) :
    Push.Scan.quotaAt (emitReads side requests E).quotas lane =
      (E.filter fun p => p ∈ (Push.Scan.lineCells side lane).take span).card := by
  let front := (Push.Scan.lineCells (w := w) (h := h) side lane).take span
  let rest := (emitReads side requests E).remaining
  let onLane := E.filter fun p => side.lane p = lane
  have hregion : ∀ p : Cell w h, side.lane p = lane →
      (p ∈ readRegion side requests ↔ p ∈ front) := by
    intro p hp
    rw [mem_readRegion]
    constructor
    · rintro ⟨request, hr, hl, hx⟩
      have he : request.1 = lane := hl.symm.trans hp
      have hs := hspan request hr he
      exact (mem_line_prefix side lane span p).mpr ⟨hp, by simpa only [hs] using hx⟩
    · intro hf
      have hf := (mem_line_prefix side lane span p).mp hf
      exact ⟨(lane, span), hmem, hf.1, hf.2⟩
  have hrest : rest.filter (fun p => side.lane p = lane) =
      onLane.filter fun p => p ∉ front := by
    ext p
    simp only [rest, emitReads_remaining, onLane, Finset.mem_filter, Finset.mem_sdiff]
    by_cases hp : side.lane p = lane
    · rw [hregion p hp]
      tauto
    · tauto
  have hfront : onLane.filter (fun p => p ∈ front) = E.filter fun p => p ∈ front := by
    ext p
    simp only [onLane, Finset.mem_filter]
    constructor
    · exact fun ⟨⟨hp, _⟩, hf⟩ => ⟨hp, hf⟩
    · rintro ⟨hp, hf⟩
      exact ⟨⟨hp, (mem_line_prefix side lane span p).mp hf |>.1⟩, hf⟩
  have hpartition := Finset.card_filter_add_card_filter_not (s := onLane) (fun p => p ∈ front)
  rw [hfront, ← hrest] at hpartition
  have heval := emitReads_eval side requests E
  have hprojection := Push.Scan.lines_lane_projection side (emitReads side requests E).quotas lane heval
  have hcard := Push.Scan.consume_card hprojection
  change (rest.filter fun p => side.lane p = lane).card +
    Push.Scan.quotaAt (emitReads side requests E).quotas lane = onLane.card at hcard
  change Push.Scan.quotaAt (emitReads side requests E).quotas lane =
    (E.filter fun p => p ∈ front).card
  omega

namespace Source

theorem frame_region (I : Instance)
    (p : Cell (layout false I).width (layout false I).height) :
    p ∈ allRegions ((layout false I).quotaTemplates.take 3) ↔ Boundary p := by
  let L := layout false I
  have hs : readRegion (w := L.width) (h := L.height) .south
      [(0, L.height), (L.width - 1, L.height)] =
      Finset.univ.filter (fun p => p.1.val = 0 ∨ p.1.val + 1 = L.width) := frame_columns_region I
  have hw : p ∈ readRegion .west [(0, L.width), (L.height - 1, L.width)] ↔
      p.2.val = 0 ∨ p.2.val + 1 = L.height := by
    rw [mem_readRegion]
    constructor
    · rintro ⟨⟨lane, span⟩, hm, hl, _⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with he | he <;> cases he <;> simp only [Direction.lane] at hl <;>
        have hy := p.2.isLt <;> omega
    · intro hy
      rcases hy with hy | hy
      · exact ⟨(0, L.width), by simp, hy, by simp only [prefixRank]; exact p.1.isLt⟩
      · exact ⟨(L.height - 1, L.width), by simp, by
          simp only [Direction.lane]; have := p.2.isLt; omega,
          by simp only [prefixRank]; exact p.1.isLt⟩
  change p ∈ allRegions (L.quotaTemplates.take 3) ↔ _
  have hstages : L.quotaTemplates.take 3 =
      [.read .south [(0, L.height), (L.width - 1, L.height)],
        .read .west [(0, L.width), (L.height - 1, L.width)], .read .north []] := rfl
  rw [hstages]
  simp only [allRegions, Template.region, show readRegion (w := L.width) (h := L.height) .north [] = ∅ from rfl,
    Finset.union_empty]
  rw [Finset.mem_union, hw, hs]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Boundary]
  exact or_assoc

private theorem stop_rack_empty (I : Instance) :
    ((layout false I).rackX, (layout false I).stop + (layout false I).shift) ∉
      (layout false I).rack := by
  intro hp
  have hshift := (layout false I).shift_ge
  have hodd : (layout false I).stop % 2 = 1 := by
    change (upperRow I (rank I I.target) 0) % 2 = 1
    simp [upperRow, roomBase_even, Nat.add_mod]
  rcases ((layout false I).mem_rack_iff _).mp hp with ⟨y, hy, he⟩ | ⟨g, hg, he | he⟩
  · have hyEven := rackRows_even false I hy
    omega
  · have hgap := stop_divider_gap false I hg
    omega
  · have hgap := stop_divider_gap false I hg
    omega

theorem marker_rack_empty (I : Instance) {row : ℕ} (hr : row ∈ (layout false I).markerRows) :
    ((layout false I).rackX, row) ∉ (layout false I).rack := by
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hr
  simp only [List.mem_append, List.mem_singleton] at hy
  rcases hy with (hy | hy) | rfl
  · exact divider_rack_empty false I hy
  · exact cap_rack_empty false I hy
  · exact stop_rack_empty I

theorem rackProbe_rack (I : Instance) {row : ℕ} (hr : row ∈ (layout false I).rackProbeRows) :
    ((layout false I).rackX, row) ∈ (layout false I).rack := by
  obtain ⟨p, hp, hy⟩ := List.mem_map.mp hr
  have hp : p ∈ (layout false I).rack := List.mem_toFinset.mpr hp
  have hx := (layout false I).rack_column hp
  have he : p = ((layout false I).rackX, row) := Prod.ext hx hy
  exact he ▸ hp

theorem rackProbe_ne_marker (I : Instance) {row : ℕ}
    (hr : row ∈ (layout false I).rackProbeRows) : row ∉ (layout false I).markerRows := by
  intro hm
  exact marker_rack_empty I hm (rackProbe_rack I hr)

/-- The actual target residual immediately before the eastward probe round. -/
def probeStart (I : Instance) : Finset (Cell (layout false I).width (layout false I).height) :=
  (Push.AcceptanceProgram.emit ((layout false I).quotaTemplates.take 3)
    (layout false I).referenceHoles).remaining

/-- The literal emitted fourth-round vector, including zero entries after repeated lanes. -/
def probeQuotas (I : Instance) : List (ℕ × ℕ) :=
  (emitReads .east (layout false I).probeRequests (probeStart I)).quotas

private theorem probeStart_front_count (I : Instance) (row quota : ℕ)
    (hrow : 0 < row ∧ row + 1 < (layout false I).height)
    (hwidth : quota + 2 ≤ (layout false I).width)
    (hempty : ∀ p : Cell (layout false I).width (layout false I).height,
      p.2.val = row → (layout false I).width - 1 - p.1.val < quota + 1 →
      p ∉ (layout false I).raster (layout false I).goalsRaw)
    (hpositive : ∀ p : Cell (layout false I).width (layout false I).height,
      (layout false I).width - 1 - p.1.val < quota + 1 → 0 < p.1.val) :
    ((probeStart I).filter fun p =>
      p ∈ (Push.Scan.lineCells .east row).take (quota + 1)).card = quota := by
  apply east_front_count _ hwidth (by omega)
  intro p hy hx
  change p ∈ (Push.AcceptanceProgram.emit ((layout false I).quotaTemplates.take 3)
    (layout false I).referenceHoles).remaining ↔ _
  rw [emit_remaining, Finset.mem_sdiff, frame_region]
  rw [Layout.referenceHoles, Finset.mem_compl]
  rw [show (p ∉ (layout false I).raster (layout false I).goalsRaw) ↔ True from
    iff_true_intro (hempty p hy hx), true_and]
  have hp := hpositive p hx
  have hpx := p.1.isLt
  simp only [Boundary]
  omega

private theorem rackProbe_front_count (I : Instance) {row : ℕ}
    (hr : row ∈ (layout false I).rackProbeRows) :
    ((probeStart I).filter fun p => p ∈ (Push.Scan.lineCells .east row).take 5).card = 4 := by
  have hfit := (layout_fits false I).rack_interior (rackProbe_rack I hr)
  have hP := (layout false I).rackX_ge
  apply probeStart_front_count I row 4 (by dsimp at hfit; omega)
    (by unfold Layout.width; omega)
  · intro p hy hx hp
    have hw := (layout false I).goalsRaw_west (((layout false I).mem_raster _ _).mp hp)
    unfold Layout.width at hx
    omega
  · intro p hx
    unfold Layout.width at hx
    omega

private theorem marker_front_count (I : Instance) {row : ℕ}
    (hr : row ∈ (layout false I).markerRows) :
    ((probeStart I).filter fun p => p ∈ (Push.Scan.lineCells .east row).take 6).card = 5 := by
  have hP := (layout false I).rackX_ge
  have hrow : 0 < row ∧ row + 1 < (layout false I).height := by
    have hm := (layout false I).marker_mem hr
    rcases Finset.mem_union.mp hm with hm | hm
    · have hi := (layout_fits false I).fixed_interior hm
      dsimp at hi
      omega
    · have he := congrArg Prod.snd (Finset.mem_singleton.mp hm)
      have hi := (layout false I).translated_bounds (stop_fit false I)
      dsimp at he
      omega
  apply probeStart_front_count I row 5 hrow (by unfold Layout.width; omega)
  · intro p hy hx hp
    have hraw := ((layout false I).mem_raster _ _).mp hp
    have hw := (layout false I).goalsRaw_west hraw
    have hpx : p.1.val = (layout false I).rackX := by unfold Layout.width at hx; omega
    have he : (p.1.val, p.2.val) = ((layout false I).rackX, row) := Prod.ext hpx hy
    have hraw' := he ▸ hraw
    exact marker_rack_empty I hr (((layout false I).goalsRaw_rack_iff row).mp hraw')
  · intro p hx
    unfold Layout.width at hx
    omega

theorem rackProbe_quotaAt (I : Instance) {row : ℕ}
    (hr : row ∈ (layout false I).rackProbeRows) : Push.Scan.quotaAt (probeQuotas I) row = 4 := by
  rw [probeQuotas, emitReads_lane_quota .east _ _ row 5]
  · exact rackProbe_front_count I hr
  · exact List.mem_append_left _ (List.mem_map.mpr ⟨row, hr, by
      apply Prod.ext
      · rfl
      · unfold Layout.width; omega⟩)
  · intro request hm he
    simp only [Layout.probeRequests, List.mem_append, List.mem_map] at hm
    rcases hm with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
    · unfold Layout.width; omega
    · change y = row at he
      exact False.elim (rackProbe_ne_marker I hr (he ▸ hy))

theorem marker_quotaAt (I : Instance) {row : ℕ}
    (hr : row ∈ (layout false I).markerRows) : Push.Scan.quotaAt (probeQuotas I) row = 5 := by
  rw [probeQuotas, emitReads_lane_quota .east _ _ row 6]
  · exact marker_front_count I hr
  · exact List.mem_append_right _ (List.mem_map.mpr ⟨row, hr, by
      apply Prod.ext
      · rfl
      · unfold Layout.width; omega⟩)
  · intro request hm he
    simp only [Layout.probeRequests, List.mem_append, List.mem_map] at hm
    rcases hm with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
    · change y = row at he
      exact False.elim (rackProbe_ne_marker I hy (he.symm ▸ hr))
    · unfold Layout.width; omega

end Source
end PushPuzzle.PushPush.Doors
