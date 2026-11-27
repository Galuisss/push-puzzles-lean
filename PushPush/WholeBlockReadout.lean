/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.WholeBlocks
import all PushPush.ReadScan
import all Push.Scan

/-! Simultaneous retained-order and per-lane payment facts of a whole parallel block. -/

@[expose] public section
namespace PushPuzzle.PushPush.WholeBlocks

open PushFS (Cell Direction)

variable {w h : ℕ}

private theorem read_front {side : Direction} {lane quota : ℕ} {E F : Finset (Cell w h)}
    (H : WholeScan.Read side lane quota E F) :
    ∀ p ∈ E \ F, ∀ q ∈ F, side.lane q = side.lane p → side.position q < side.position p := by
  have hread := Push.Scan.read_lane_restrict H.eval
  have hc := Reader.consume_result side.position (Push.Scan.lineCells side lane) quota
    (E.filter fun p => side.lane p = lane) (F.filter fun p => side.lane p = lane)
    (Push.Scan.lineCells_pairwise side lane)
    (by intro p hp; exact (Push.Scan.mem_lineCells side lane p).mpr (Finset.mem_filter.mp hp).2) hread
  intro p hp q hq hl
  have hpl : side.lane p = lane := by
    by_contra hne
    exact (Finset.mem_sdiff.mp hp).2
      ((Push.Scan.Instruction.read_outside H.eval hne).mpr (Finset.mem_sdiff.mp hp).1)
  apply hc.2.2 p ?_ q (Finset.mem_filter.mpr ⟨hq, hl.trans hpl⟩)
  exact Finset.mem_sdiff.mpr
    ⟨Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hp).1, hpl⟩,
      fun hf => (Finset.mem_sdiff.mp hp).2 (Finset.mem_filter.mp hf).1⟩

private theorem lines_front {side : Direction} {requests : List (ℕ × ℕ)} {E F : Finset (Cell w h)}
    (H : WholeScan.LooseExec (Push.Scan.lines side requests) E F) :
    ∀ p ∈ E \ F, ∀ q ∈ F, side.lane q = side.lane p → side.position q < side.position p := by
  induction requests generalizing E with
  | nil => cases H; simp
  | cons a rest ih =>
    cases H with
    | @cons _ _ _ _ _ _ G _ _ head tail =>
      intro p hp q hq hl
      obtain ⟨hpE, hpF⟩ := Finset.mem_sdiff.mp hp
      by_cases hpG : p ∈ G
      · exact ih tail p (Finset.mem_sdiff.mpr ⟨hpG, hpF⟩) q hq hl
      · exact read_front head p (Finset.mem_sdiff.mpr ⟨hpE, hpG⟩) q (tail.subset hq) hl

private theorem lines_paid {side : Direction} {requests : List (ℕ × ℕ)} {E F : Finset (Cell w h)}
    (H : WholeScan.LooseExec (Push.Scan.lines side requests) E F) {a : ℕ × ℕ} (ha : a ∈ requests) :
    (F.filter fun p => side.lane p = a.1).card + a.2 ≤ (E.filter fun p => side.lane p = a.1).card := by
  induction requests generalizing E with
  | nil => exact False.elim (List.not_mem_nil ha)
  | cons b rest ih =>
    cases H with
    | @cons _ _ _ actual _ _ G _ paid head tail =>
      rcases List.mem_cons.mp ha with he | ha
      · subst a
        have hcard := Push.Scan.Instruction.read_line_card head.eval
        have hle : (F.filter fun p => side.lane p = b.1).card ≤
            (G.filter fun p => side.lane p = b.1).card :=
          Finset.card_le_card (Finset.filter_subset_filter _ tail.subset)
        change (G.filter fun p => side.lane p = b.1).card + actual =
          (E.filter fun p => side.lane p = b.1).card at hcard
        omega
      · have hp := ih tail ha
        have hle : (G.filter fun p => side.lane p = a.1).card ≤
            (E.filter fun p => side.lane p = a.1).card :=
          Finset.card_le_card (Finset.filter_subset_filter _ head.subset)
        omega

theorem Block.characterization {side : Direction} {requests : List (ℕ × ℕ)}
    {E F : Finset (Cell w h)} (H : Block side requests E F) : Block.Characterization side requests E F := by
  refine ⟨H.subset, lines_front H, H.lines_no_split, ?_⟩
  intro lane hlane
  let quotas := Push.Scan.denseQuotas side w h requests
  have hi : lane < quotas.length := by simpa only [quotas, Push.Scan.denseQuotas_length] using hlane
  have hm := Push.Scan.ofQuotas_mem quotas ⟨lane, hi⟩
  have hm' : (lane, Push.Scan.quotaAt requests lane) ∈ Push.Scan.ofQuotas quotas := by
    simpa only [quotas, Push.Scan.denseQuotas, List.getElem_ofFn, Fin.getElem_fin] using hm
  have hp := lines_paid H hm'
  rw [Finset.card_sdiff_of_subset (Finset.filter_subset_filter _ H.subset)]
  dsimp only at hp
  omega

end PushPuzzle.PushPush.WholeBlocks
