/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.WholeBlockConstruct
public import PushPush.WholeSourceTransport
import all PushPush.WholeSourceTransport
import all Push.ScanNormalize

/-! Whole parallel blocks project through the translated original source rectangle. -/

@[expose] public section
namespace PushPuzzle.PushPush.WholeBlocks

open PushFS (Cell Direction Adjacent)
open Push.Cyclic

variable (r : Push.ColumnScan.Input)

def sourceRequests (side : Direction) (requests : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  requests.map fun a => (sourceLane side a.1, a.2)

def SourceLanesOff (side : Direction)
    (A : Finset (Cell (dock r).outputWidth (dock r).outputHeight)) : Prop :=
  ∀ lane < Push.Scan.laneCount side r.width r.height,
    ∀ q ∈ A, side.lane q ≠ sourceLane side lane

private theorem sourceLane_inj (side : Direction) : Function.Injective (sourceLane side) := by
  intro a b he
  cases side <;> simp only [sourceLane] at he <;> omega

private theorem sourceRequests_quotaAt (side : Direction) (requests : List (ℕ × ℕ)) (lane : ℕ) :
    Push.Scan.quotaAt (sourceRequests side requests) (sourceLane side lane) = Push.Scan.quotaAt requests lane := by
  induction requests with
  | nil => rfl
  | cons a rest ih =>
    simp only [sourceRequests, List.map_cons, Push.Scan.quotaAt_cons, (sourceLane_inj side).eq_iff]
    exact congrArg (fun n => (if a.1 = lane then a.2 else 0) + n) ih

private theorem source_lane_lt (side : Direction) (lane : ℕ)
    (hl : lane < Push.Scan.laneCount side r.width r.height) :
    sourceLane side lane < Push.Scan.laneCount side (dock r).outputWidth (dock r).outputHeight := by
  cases side with
  | north | south =>
    exact ((sourceEmbedding r) (⟨lane, hl⟩, r.initial.player.2)).1.isLt
  | east | west =>
    exact ((sourceEmbedding r) (r.initial.player.1, ⟨lane, hl⟩)).2.isLt

private theorem cell_lane_lt (side : Direction) (p : Cell r.width r.height) :
    side.lane p < Push.Scan.laneCount side r.width r.height := by
  cases side <;> first | exact p.1.isLt | exact p.2.isLt

private theorem source_lt (side : Direction) (p q : Cell r.width r.height) :
    side.position ((sourceEmbedding r) p) < side.position ((sourceEmbedding r) q) ↔
      side.position p < side.position q := by
  cases side <;> simp only [Direction.position, sourceEmbedding_x, sourceEmbedding_y] <;> omega

private theorem source_filter_map (side : Direction) (lane : ℕ)
    (E : Finset (Cell r.width r.height))
    (A : Finset (Cell (dock r).outputWidth (dock r).outputHeight))
    (hoff : ∀ q ∈ A, side.lane q ≠ sourceLane side lane) :
    ((E.map (sourceEmbedding r) ∪ A).filter fun q => side.lane q = sourceLane side lane) =
      (E.filter fun p => side.lane p = lane).map (sourceEmbedding r) := by
  ext q
  constructor
  · rintro hq
    obtain ⟨hq, hline⟩ := Finset.mem_filter.mp hq
    rcases Finset.mem_union.mp hq with hm | ha
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hm
      rw [sourceEmbedding_lane] at hline
      exact Finset.mem_map.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, sourceLane_inj side hline⟩, rfl⟩
    · exact False.elim (hoff q ha hline)
  · intro hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hq
    obtain ⟨hp, hl⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_union_left _ (Finset.mem_map.mpr ⟨p, hp, rfl⟩),
      by rw [sourceEmbedding_lane, hl]⟩

private theorem sourceData_filter_map (side : Direction) (lane : ℕ)
    (E : Finset (Cell (dock r).outputWidth (dock r).outputHeight))
    (hrows : ∀ q ∈ E, q.2.val < r.height → 2 ≤ q.1.val ∧ q.1.val < r.width + 2)
    (hoff : ∀ q ∈ auxData r E, side.lane q ≠ sourceLane side lane) :
    (E.filter fun q => side.lane q = sourceLane side lane) =
      ((sourceData r E).filter fun p => side.lane p = lane).map (sourceEmbedding r) := by
  exact (congrArg (fun S => S.filter fun q => side.lane q = sourceLane side lane)
    (source_data_decomposition r E hrows)).trans (source_filter_map r side lane _ _ hoff)

private theorem Block.source {side : Direction} {requests : List (ℕ × ℕ)}
    {E F : Finset (Cell (dock r).outputWidth (dock r).outputHeight)}
    (H : Block side (sourceRequests side requests) E F)
    (hrows : ∀ q ∈ E, q.2.val < r.height → 2 ≤ q.1.val ∧ q.1.val < r.width + 2)
    (hoff : SourceLanesOff r side (auxData r E)) :
    Block side requests (sourceData r E) (sourceData r F) := by
  have hc := H.characterization
  apply Block.of_characterization
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc.subset (Finset.mem_filter.mp hp).2⟩
  · intro p hp q hq hl
    have hp' : sourceEmbedding r p ∈ E \ F := by
      simpa only [sourceData, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] using hp
    have hq' : sourceEmbedding r q ∈ F := (Finset.mem_filter.mp hq).2
    exact (source_lt r side q p).mp (hc.front _ hp' _ hq'
      (by rw [sourceEmbedding_lane, sourceEmbedding_lane, hl]))
  · intro p hp q hq ha
    have hp' : sourceEmbedding r p ∈ E \ F := by
      simpa only [sourceData, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] using hp
    exact hc.no_split _ hp' _ (Finset.mem_filter.mp hq).2 (WholeScan.source_adjacent r side.opposite ha)
  · intro lane hl
    have hp := hc.paid (sourceLane side lane) (source_lane_lt r side lane hl)
    rw [sourceRequests_quotaAt] at hp
    have hoffF : ∀ q ∈ auxData r F, side.lane q ≠ sourceLane side lane := by
      intro q hq
      exact hoff lane hl q (Finset.mem_filter.mpr
        ⟨hc.subset (Finset.mem_filter.mp hq).1, (Finset.mem_filter.mp hq).2⟩)
    rw [sourceData_filter_map r side lane E hrows (hoff lane hl),
      sourceData_filter_map r side lane F (fun q hq hy => hrows q (hc.subset hq) hy) hoffF,
      ← Finset.map_sdiff, Finset.card_map] at hp
    exact hp

private theorem quotaAt_zero (requests : List (ℕ × ℕ)) (lane : ℕ)
    (hnone : ∀ a ∈ requests, a.1 ≠ lane) : Push.Scan.quotaAt requests lane = 0 := by
  induction requests with
  | nil => rfl
  | cons a rest ih =>
    rw [Push.Scan.quotaAt_cons, ite_eq_right (hnone a (List.mem_cons_self ..)), Nat.zero_add]
    exact ih (fun b hb => hnone b (List.mem_cons_of_mem _ hb))

private theorem Block.source_lift {side : Direction} {requests : List (ℕ × ℕ)}
    {E F : Finset (Cell r.width r.height)} (H : Block side requests E F)
    (hbound : ∀ a ∈ requests, a.1 < Push.Scan.laneCount side r.width r.height)
    (A : Finset (Cell (dock r).outputWidth (dock r).outputHeight))
    (hoff : SourceLanesOff r side A) :
    Block side (sourceRequests side requests)
      (E.map (sourceEmbedding r) ∪ A) (F.map (sourceEmbedding r) ∪ A) := by
  have hc := H.characterization
  apply Block.of_characterization
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hp
      exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨q, hc.subset hq, rfl⟩)
    · exact Finset.mem_union_right _ hp
  · intro p hp q hq hl
    obtain ⟨hp, hnot⟩ := Finset.mem_sdiff.mp hp
    have hmap : p ∈ E.map (sourceEmbedding r) :=
      (Finset.mem_union.mp hp).resolve_right (fun h => hnot (Finset.mem_union_right _ h))
    obtain ⟨p, hpE, rfl⟩ := Finset.mem_map.mp hmap
    have hpF : p ∉ F := fun h => hnot (Finset.mem_union_left _ (Finset.mem_map.mpr ⟨p, h, rfl⟩))
    rcases Finset.mem_union.mp hq with hq | hq
    · obtain ⟨q, hqF, rfl⟩ := Finset.mem_map.mp hq
      apply (source_lt r side q p).mpr
      apply hc.front p (Finset.mem_sdiff.mpr ⟨hpE, hpF⟩) q hqF
      rw [sourceEmbedding_lane, sourceEmbedding_lane] at hl
      exact sourceLane_inj side hl
    · exact False.elim (hoff (side.lane p) (cell_lane_lt r side p) q hq
        (hl.trans (sourceEmbedding_lane r side p)))
  · intro p hp q hq ha
    obtain ⟨hp, hnot⟩ := Finset.mem_sdiff.mp hp
    have hmap : p ∈ E.map (sourceEmbedding r) :=
      (Finset.mem_union.mp hp).resolve_right (fun h => hnot (Finset.mem_union_right _ h))
    obtain ⟨p, hpE, rfl⟩ := Finset.mem_map.mp hmap
    have hpF : p ∉ F := fun h => hnot (Finset.mem_union_left _ (Finset.mem_map.mpr ⟨p, h, rfl⟩))
    rcases Finset.mem_union.mp hq with hq | hq
    · obtain ⟨q, hqF, rfl⟩ := Finset.mem_map.mp hq
      exact hc.no_split p (Finset.mem_sdiff.mpr ⟨hpE, hpF⟩) q hqF
        (WholeScan.source_adjacent_reflect r side.opposite ha)
    · apply hoff (side.lane p) (cell_lane_lt r side p) q hq
      have hl : side.lane q = side.lane ((sourceEmbedding r) p) := by cases side <;> exact ha.lane
      exact hl.trans (sourceEmbedding_lane r side p)
  · intro target _
    by_cases hex : ∃ lane < Push.Scan.laneCount side r.width r.height, target = sourceLane side lane
    · obtain ⟨lane, hlane, rfl⟩ := hex
      rw [sourceRequests_quotaAt, source_filter_map r side lane E A (hoff lane hlane),
        source_filter_map r side lane F A (hoff lane hlane), ← Finset.map_sdiff, Finset.card_map]
      exact hc.paid lane hlane
    · have hzero : Push.Scan.quotaAt (sourceRequests side requests) target = 0 := by
        apply quotaAt_zero
        intro a ha he
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
        exact hex ⟨b.1, hbound b hb, he.symm⟩
      rw [hzero]
      exact Nat.zero_le _

private theorem sourceLanesOff_of_orthogonal (side : Direction)
    (A : Finset (Cell (dock r).outputWidth (dock r).outputHeight))
    (H : SourceOrthogonal r A) : SourceLanesOff r side A := by
  intro lane hlane q hq he
  obtain ⟨hy, hx⟩ := H q hq
  cases side <;> simp only [Push.Scan.laneCount, Direction.lane, sourceLane] at hlane he <;> omega

theorem Block.source_orthogonal {side : Direction} {requests : List (ℕ × ℕ)}
    {E F : Finset (Cell (dock r).outputWidth (dock r).outputHeight)}
    (H : Block side (sourceRequests side requests) E F)
    (hrows : ∀ q ∈ E, q.2.val < r.height → 2 ≤ q.1.val ∧ q.1.val < r.width + 2)
    (hoff : SourceOrthogonal r (auxData r E)) :
    Block side requests (sourceData r E) (sourceData r F) :=
  H.source r hrows (sourceLanesOff_of_orthogonal r side _ hoff)

theorem Block.source_lift_orthogonal {side : Direction} {requests : List (ℕ × ℕ)}
    {E F : Finset (Cell r.width r.height)} (H : Block side requests E F)
    (hbound : ∀ a ∈ requests, a.1 < Push.Scan.laneCount side r.width r.height)
    (A : Finset (Cell (dock r).outputWidth (dock r).outputHeight))
    (hoff : SourceOrthogonal r A) :
    Block side (sourceRequests side requests)
      (E.map (sourceEmbedding r) ∪ A) (F.map (sourceEmbedding r) ∪ A) :=
  H.source_lift r hbound A (sourceLanesOff_of_orthogonal r side A hoff)

end PushPuzzle.PushPush.WholeBlocks
