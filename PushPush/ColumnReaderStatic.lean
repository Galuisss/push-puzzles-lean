/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.ColumnReaderForward
public import PushPush.WholeColumnReadout
public import PushPush.ColumnReaderCrop
public import PushPush.ColumnReaderResult

/-! Realize an entire loose column program with its prescribed exact remainder. -/

@[expose] public section
namespace PushPuzzle.PushPush.ColumnReader

open PushFS (Cell State)
open Reader

variable (r : Push.ColumnScan.Input)

private theorem exactRead_image {E F : Finset (Cell r.width r.height)} (H : ExactNorthRead E F) :
    ExactNorthRead (E.image r.embed) (F.image r.embed) := by
  refine ⟨Finset.image_subset_image H.subset, ?_, ?_⟩
  · intro p hp q hq
    obtain ⟨hpE, hpF⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hpE
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq
    exact H.front a (Finset.mem_sdiff.mpr ⟨ha, fun hf =>
      hpF (Finset.mem_image.mpr ⟨a, hf, rfl⟩)⟩) b hb
  · intro p hp q hq ha
    obtain ⟨hpE, hpF⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨a, haE, rfl⟩ := Finset.mem_image.mp hpE
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hq
    exact H.no_split a (Finset.mem_sdiff.mpr ⟨haE, fun hf =>
      hpF (Finset.mem_image.mpr ⟨a, hf, rfl⟩)⟩) b hb ((embed_adjacent r .north a b).mp ha)

private theorem sourceColumn_literal (i : Fin r.width) : sourceColumn r i =
    (r.initial.empty.filter fun p => p.1.val = i.val).image r.embed := by
  rw [sourceColumn_eq]
  congr 1

/-- A successful static whole-run column word executes on the literal reader board. -/
theorem compile_loose_frame {E : Finset (Cell r.width r.height)}
    (hcorner : r.initial.player = r.sourceCorner)
    (H : WholeScan.LooseExec (Push.Scan.columns (Push.Scan.ofQuotas r.quotas)) r.initial.empty E) :
    ∃ t : State r.outputWidth r.outputHeight, ReadPath r.compile.initial t ∧ t.player = r.target ∧
      (∀ p : Cell r.width r.height, r.embed p ∈ PushS.holes t ↔ p ∈ E) ∧
      r.room ⊆ PushS.holes t ∧ ∀ q ∈ PushS.holes t, q.2.val < r.height → q.1.val < r.width := by
  let F := fun i : Fin r.width => (E.filter fun p => p.1.val = i.val).image r.embed
  have hread (i : Fin r.width) : ExactNorthRead (sourceColumn r i) (F i) := by
    rw [sourceColumn_literal]
    exact exactRead_image r (H.ofQuotas_readout r.quotas i.val).1
  have hpaid (i : Fin r.width) : r.quotas.getD i.val 0 ≤ (sourceColumn r i \ F i).card := by
    rw [sourceColumn_literal]
    change r.quotas.getD i.val 0 ≤
      ((r.initial.empty.filter fun p => p.1.val = i.val).image r.embed \
        (E.filter fun p => p.1.val = i.val).image r.embed).card
    rw [← Finset.image_sdiff _ _ r.embed_injective, Finset.card_image_of_injective _ r.embed_injective]
    exact (H.ofQuotas_readout r.quotas i.val).2
  obtain ⟨t, hr, hp, hF, hroom, hsupport⟩ := compile_run_frame r hcorner F hread hpaid
  refine ⟨t, hr, hp, ?_, hroom, hsupport⟩
  intro p
  have hm : r.embed p ∈ remainingColumn r t p.1 ↔ r.embed p ∈ PushS.holes t := by
    simp only [remainingColumn, Finset.mem_filter]
    exact and_iff_left ⟨rfl, p.2.isLt⟩
  rw [← hm, hF]
  simp only [F, Finset.mem_image, r.embed_injective.eq_iff, exists_eq_right, Finset.mem_filter,
    and_true]

end PushPuzzle.PushPush.ColumnReader
