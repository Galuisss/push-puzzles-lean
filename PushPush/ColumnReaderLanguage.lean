/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.ColumnReaderCorrectness
public import PushPush.WholeColumnReadout
public import PushPush.WholeColumns

/-! The full maximum-reader language is exactly the loose whole-column scan language. -/

@[expose] public section
namespace PushPuzzle.PushPush.ColumnReader

open PushFS (Cell State)
open PushS Push.ReaderResidual Push.ReflectedFrontier

variable (r : Push.ColumnScan.Input)

private theorem source_embed_iff (s : State r.outputWidth r.outputHeight)
    (p : Cell r.width r.height) :
    r.embed p ∈ source r.width r.height s ↔ p ∈ holes (r.cropState s) := by
  rw [← r.cropState_holes_image]
  simp only [Finset.mem_image, r.embed_injective.eq_iff, exists_eq_right]

private theorem crop_whole_remainder {s t : State r.outputWidth r.outputHeight}
    (H : WholeBottomRemainder (source r.width r.height s) (source r.width r.height t)) :
    WholeBottomRemainder (holes (r.cropState s)) (holes (r.cropState t)) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro p hp
    exact (source_embed_iff r s p).mp (H.subset ((source_embed_iff r t p).mpr hp))
  · intro p hp q hq hx hy
    apply (source_embed_iff r t q).mp
    apply H.northern (r.embed p) ((source_embed_iff r t p).mpr hp)
      (r.embed q) ((source_embed_iff r s q).mpr hq)
    · apply Fin.ext
      change q.1.val = p.1.val
      exact congrArg Fin.val hx
    · exact hy
  · intro p hp q hq ha
    exact H.no_split (r.embed p)
      (Finset.mem_sdiff.mpr ⟨(source_embed_iff r s p).mpr (Finset.mem_sdiff.mp hp).1,
        fun ht => (Finset.mem_sdiff.mp hp).2 ((source_embed_iff r t p).mp ht)⟩)
      (r.embed q) ((source_embed_iff r t q).mpr hq) ((embed_adjacent r .north p q).mpr ha)

/-- The exact cropped terminal bitmap is the remainder of the committed whole-column scan. -/
private theorem SourceWitness.whole_scan {finish : State r.outputWidth r.outputHeight}
    (w : SourceWitness r finish) (hp : finish.player = r.target) :
    WholeScan.LooseExec (Push.Scan.columns (Push.Scan.ofQuotas r.quotas))
      (holes (r.cropState w.state)) (holes (r.cropState finish)) := by
  have hfx : finish.player.1.val = 0 := congrArg (fun p => p.1.val) hp
  have hfy : finish.player.2.val = r.targetLevel := congrArg (fun p => p.2.val) hp
  have H := crop_whole_remainder r (w.whole_remainder r hfx hfy.ge)
  refine WholeScan.loose_columns (Push.Scan.ofQuotas_nodup r.quotas) ?_ H.toBottomRemainder H.no_split ?_
  · intro x
    let i : Fin r.quotas.length := ⟨x.val, by rw [r.quotas_width]; exact x.isLt⟩
    exact ⟨r.quotas[i], Push.Scan.ofQuotas_mem r.quotas i⟩
  · intro a ha
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    let i : Fin r.width := ⟨j.val, by rw [← r.quotas_width]; exact j.isLt⟩
    have hc := r.landing_column_consumed_quotas w.before w.suffix hfx hfy w.landing i
    rw [r.crop_column_card finish i, r.crop_column_card w.state i] at hc
    simpa only [i, Fin.ext_iff, List.getD_eq_getElem _ _ j.isLt, Fin.getElem_fin] using hc

/-- The maximum-sliding destination tests the complete loose whole-column word
in one reachable source-corner state. -/
theorem compile_solvable_iff_whole_scan : PushPush.Instance.Solvable r.compile ↔
    ∃ s : State r.width r.height, Reachable r.initial.toState s ∧ s.player = r.sourceCorner ∧
      ∃ F, WholeScan.LooseExec (Push.Scan.columns (Push.Scan.ofQuotas r.quotas)) (holes s) F := by
  constructor
  · rintro ⟨finish, hr, hp⟩
    have hfx : finish.player.1.val = 0 := congrArg (fun p => p.1.val) hp
    have hfy : r.targetLevel ≤ finish.player.2.val := by
      have hy := congrArg (fun p => p.2.val) hp
      change finish.player.2.val = r.targetLevel at hy
      omega
    obtain ⟨w⟩ := source_witness r hr hfx hfy
    refine ⟨r.cropState w.state, w.source, ?_, holes (r.cropState finish), w.whole_scan r hp⟩
    apply r.cropPlayer_outside
    intro hs
    have hx := hs.1
    rw [w.landing] at hx
    change r.width < r.width at hx
    omega
  · rintro ⟨s, hr, hp, F, H⟩
    apply compile_solvable_of_source r hr hp
    intro i
    have hpaid := (H.ofQuotas_readout r.quotas i.val).2
    have hcard := Finset.card_le_card (Finset.sdiff_subset :
      ((holes s).filter fun p => p.1.val = i.val) \ (F.filter fun p => p.1.val = i.val) ⊆
        (holes s).filter fun p => p.1.val = i.val)
    have hbound := hpaid.trans hcard
    simpa only [holes, Fin.ext_iff] using hbound

end PushPuzzle.PushPush.ColumnReader
