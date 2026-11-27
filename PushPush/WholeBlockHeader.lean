/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.WholePeelingForward
public import PushPush.WholeBlocksSourceProgram

/-! The next reader's first dense vector clears all old auxiliary source lanes. -/

@[expose] public section
namespace PushPuzzle.PushPush.Cyclic

open PushFS (Cell Direction)
open Push.Cyclic WholeScan

/-- Exact data and orthogonal auxiliary holes after the actual next-reader header. -/
structure HeaderRemainder (r : Push.ColumnScan.Input) (rows : List ℕ)
    (D : Finset (Cell (dock r).outputWidth (dock r).outputHeight))
    (F : Finset (Cell (dock r).outputHeight (dock r).outputWidth)) where
  remaining : Finset (Cell (dock r).outputWidth (dock r).outputHeight)
  data : LooseExec (Push.Scan.lines .west (Push.Scan.ofQuotas rows)) (sourceData r D)
    (sourceData r remaining)
  source_rows : ∀ q ∈ remaining, q.2.val < r.height → 2 ≤ q.1.val ∧ q.1.val < r.width + 2
  orthogonal : SourceOrthogonal r (auxData r remaining)
  turned : remaining.map (turnEmbedding (dock r).outputWidth (dock r).outputHeight) = F

theorem next_header_sound (r : Push.ColumnScan.Input) (rows : List ℕ)
    (hlen : rows.length = r.height)
    (D : Finset (Cell (dock r).outputWidth (dock r).outputHeight))
    (hrows : ∀ q ∈ D, q.2.val < r.height → 2 ≤ q.1.val ∧ q.1.val < r.width + 2)
    (hsouth : ∀ q ∈ D, (wideReader r).outputHeight ≤ q.2.val → q.1.val < 2)
    {F : Finset (Cell (dock r).outputHeight (dock r).outputWidth)}
    (H : LooseExec (Push.Scan.columns (Push.Scan.ofQuotas (nextQuotas r rows)))
      (D.map (turnEmbedding (dock r).outputWidth (dock r).outputHeight)) F) :
    Nonempty (HeaderRemainder r rows D F) := by
  have hprogram : turnProgram (paddedUnturned r rows []) =
      Push.Scan.columns (Push.Scan.ofQuotas (nextQuotas r rows)) := by
    rw [paddedUnturned_turned r rows hlen []]
    simp only [nextTail, List.map_nil, turnProgram, List.append_nil]
  have H' := H
  rw [← hprogram] at H'
  obtain ⟨G, hwhole, hturn⟩ := H'.unturn _ (paddedUnturned_bounded r rows hlen [] (by simp)) D
  simp only [paddedUnturned, List.map_nil, List.append_nil] at hwhole
  obtain ⟨M, hfirst, hpadding⟩ := (LooseExec.append_iff _ _ _ _).mp hwhole
  obtain ⟨J, hdata, hcleanup⟩ := (LooseExec.append_iff _ _ _ _).mp hfirst
  have hdataRows := hdata.source_rows r rows hlen hrows
  have hcleanData := hcleanup.rowProgram_sourceData r (by
    intro row hr
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
    omega)
  have hpadData := hpadding.rowProgram_sourceData r (by
    intro row hr
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
    have hh : r.height ≤ (wideReader r).outputHeight := by
      change r.height ≤ r.height + (wideReader r).length
      omega
    omega)
  have horth := hcleanup.cleanup_orthogonal r (fun q hq hy => hsouth q (hdata.subset hq) hy)
  have hGE := hpadding.subset.trans (hcleanup.subset.trans hdata.subset)
  refine ⟨⟨G, ?_, (fun q hq hy => hrows q (hGE hq) hy), ?_, hturn.symm⟩⟩
  · exact Eq.mpr (congrArg (fun A => LooseExec (Push.Scan.lines .west (Push.Scan.ofQuotas rows))
      (sourceData r D) A) (hpadData.trans hcleanData)) hdataRows
  · intro q hq
    obtain ⟨hq, hy⟩ := Finset.mem_filter.mp hq
    exact horth q (Finset.mem_filter.mpr ⟨hpadding.subset hq, hy⟩)

theorem next_header_complete (r : Push.ColumnScan.Input) (rows : List ℕ)
    (hlen : rows.length = r.height)
    {E F : Finset (Cell r.width r.height)}
    (D : Finset (Cell (dock r).outputWidth (dock r).outputHeight))
    (hdata : sourceData r D = E)
    (hrows : ∀ q ∈ D, q.2.val < r.height → 2 ≤ q.1.val ∧ q.1.val < r.width + 2)
    (hstock : ∀ row ∈ auxiliaryRows r, r.width + 2 ≤ (D.filter fun q => q.2.val = row).card)
    (H : LooseExec (Push.Scan.lines .west (Push.Scan.ofQuotas rows)) E F) :
    LooseExec (Push.Scan.columns (Push.Scan.ofQuotas (nextQuotas r rows)))
      (D.map (turnEmbedding (dock r).outputWidth (dock r).outputHeight))
      ((F.map (sourceEmbedding r)).map (turnEmbedding (dock r).outputWidth (dock r).outputHeight)) := by
  have hh := next_loose_complete r rows hlen [] (by simp) D hdata hrows hstock
    (show LooseExec (Push.Scan.lines .west (Push.Scan.ofQuotas rows) ++ []) E F from
      by simpa only [List.append_nil] using H)
  simpa only [nextTail, List.map_nil, turnProgram, List.append_nil] using hh

end PushPuzzle.PushPush.Cyclic
