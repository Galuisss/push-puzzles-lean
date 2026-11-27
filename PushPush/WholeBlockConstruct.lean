/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.WholeBlockReadout
import all PushPush.ReadScan
import all Push.ScanNormalize

/-! Construct a parallel whole-run block from its simultaneous lane inventories. -/

@[expose] public section
namespace PushPuzzle.PushPush.WholeBlocks

open PushFS (Cell Direction)

variable {w h : ℕ}

private theorem quotaAt_zero (requests : List (ℕ × ℕ)) (lane : ℕ)
    (hnone : ∀ a ∈ requests, a.1 ≠ lane) : Push.Scan.quotaAt requests lane = 0 := by
  induction requests with
  | nil => rfl
  | cons a rest ih =>
    rw [Push.Scan.quotaAt_cons, ite_eq_right (hnone a (List.mem_cons_self ..)), Nat.zero_add]
    exact ih (fun b hb => hnone b (List.mem_cons_of_mem a hb))

theorem quotaAt_of_nodup {requests : List (ℕ × ℕ)}
    (hnd : (requests.map Prod.fst).Nodup) {a : ℕ × ℕ} (ha : a ∈ requests) :
    Push.Scan.quotaAt requests a.1 = a.2 := by
  induction requests with
  | nil => exact False.elim (List.not_mem_nil ha)
  | cons b rest ih =>
    obtain ⟨hnot, hnd⟩ := List.nodup_cons.mp hnd
    rcases List.mem_cons.mp ha with he | ha
    · subst a
      rw [Push.Scan.quotaAt_cons, ite_eq_left rfl, quotaAt_zero rest b.1
        (fun c hc he => hnot (List.mem_map.mpr ⟨c, hc, he⟩)), Nat.add_zero]
    · have hne : b.1 ≠ a.1 := fun he => hnot (List.mem_map.mpr ⟨a, ha, he.symm⟩)
      rw [Push.Scan.quotaAt_cons, ite_eq_right hne, Nat.zero_add]
      exact ih hnd ha

/-- Every simultaneous whole cut paying the sparse per-lane sums executes as
one physical lower-bound block, including additional consumption on zero lanes. -/
theorem Block.of_characterization {side : Direction} {requests : List (ℕ × ℕ)}
    {E F : Finset (Cell w h)} (H : Block.Characterization side requests E F) :
    Block side requests E F := by
  let amount (lane : ℕ) :=
    ((E.filter fun p => side.lane p = lane) \ (F.filter fun p => side.lane p = lane)).card
  let actualQuotas := List.ofFn fun lane : Fin (Push.Scan.laneCount side w h) => amount lane.val
  let actual := Push.Scan.ofQuotas actualQuotas
  have hnd : (actual.map Prod.fst).Nodup := Push.Scan.ofQuotas_nodup actualQuotas
  have hmem : ∀ lane < Push.Scan.laneCount side w h, (lane, amount lane) ∈ actual := by
    intro lane hlane
    have hi : lane < actualQuotas.length := by simpa only [actualQuotas, List.length_ofFn] using hlane
    have hm := Push.Scan.ofQuotas_mem actualQuotas ⟨lane, hi⟩
    simpa only [actualQuotas, List.getElem_ofFn, Fin.getElem_fin] using hm
  have hquota : ∀ a ∈ actual, a.2 ≤ (E.filter fun p => side.lane p = a.1).card := by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    simp only [Fin.getElem_fin, actualQuotas, List.getElem_ofFn]
    exact Finset.card_le_card Finset.sdiff_subset
  obtain ⟨G, hread⟩ := Push.Scan.lines_accepts side actual E hnd hquota
  have heq : G = F := by
    ext p
    let lane := side.lane p
    have hlane : lane < Push.Scan.laneCount side w h := by
      cases side <;> first | exact p.1.isLt | exact p.2.isLt
    have hproject := Push.Scan.lines_lane_projection side actual lane hread
    rw [quotaAt_of_nodup hnd (hmem lane hlane)] at hproject
    have hfront := Reader.consume_of_front side.position (Push.Scan.lineCells side lane)
      (E.filter fun p => side.lane p = lane) (F.filter fun p => side.lane p = lane)
      (Push.Scan.lineCells_pairwise side lane)
      (by intro q hq; exact (Push.Scan.mem_lineCells side lane q).mpr (Finset.mem_filter.mp hq).2)
      (Finset.filter_subset_filter _ H.subset) (by
        intro q hq z hz
        obtain ⟨hqE, hqF⟩ := Finset.mem_sdiff.mp hq
        obtain ⟨hqE, hqlane⟩ := Finset.mem_filter.mp hqE
        obtain ⟨hzF, hzlane⟩ := Finset.mem_filter.mp hz
        exact H.front q (Finset.mem_sdiff.mpr ⟨hqE,
          fun hqF' => hqF (Finset.mem_filter.mpr ⟨hqF', hqlane⟩)⟩) z hzF (hzlane.trans hqlane.symm))
    have hline : (G.filter fun q => side.lane q = lane) = (F.filter fun q => side.lane q = lane) :=
      Option.some.inj (hproject.symm.trans hfront)
    have hm : p ∈ (G.filter fun q => side.lane q = lane) ↔ p ∈ (F.filter fun q => side.lane q = lane) :=
      hline ▸ Iff.rfl
    simpa only [Finset.mem_filter, lane, eq_self_iff_true, and_true] using hm
  rw [heq] at hread
  have hexact := WholeScan.Exec.lines_of_eval hnd hread H.no_split
  apply hexact.loosen_lines
  apply List.forall₂_of_length_eq_of_get
  · simp only [Push.Scan.ofQuotas, List.length_ofFn, Push.Scan.denseQuotas_length, actual, actualQuotas]
  · intro lane hi hj
    simp only [Push.Scan.ofQuotas, List.get_eq_getElem, List.getElem_ofFn,
      Fin.getElem_fin, Push.Scan.denseQuotas, actual, actualQuotas]
    exact ⟨trivial, H.paid lane (by
      simpa only [Push.Scan.ofQuotas, List.length_ofFn, Push.Scan.denseQuotas_length] using hi)⟩

end PushPuzzle.PushPush.WholeBlocks
