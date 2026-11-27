/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicStaticCleanup
public import Push.ScanColumns
public import Push.ScanComposition

/-! One complete cyclic peeling step preserves every bounded future source scan. -/

@[expose] public section
namespace PushPuzzle.Push.Cyclic

open PushFS PushS

/-- Source data is exact in a translated source bitmap with auxiliary holes below it. -/
theorem sourceData_frame (r : ColumnScan.Input) (E : Finset (Cell r.width r.height))
    (A : Finset (Cell (dock r).outputWidth (dock r).outputHeight))
    (hA : ∀ q ∈ A, r.height ≤ q.2.val) :
    sourceData r (E.map (sourceEmbedding r) ∪ A) = E := by
  ext p
  simp only [sourceData, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
    Finset.mem_map, (sourceEmbedding r).injective.eq_iff, exists_eq_right]
  have hn : (sourceEmbedding r) p ∉ A := by
    intro hp
    have := hA _ hp
    change r.height ≤ p.2.val at this
    omega
  simp only [hn, or_false]

private theorem west_source_off (r : ColumnScan.Input) (rows : List ℕ)
    (hlen : rows.length = r.height)
    (A : Finset (Cell (dock r).outputWidth (dock r).outputHeight))
    (hA : ∀ q ∈ A, r.height ≤ q.2.val) :
    ∀ i ∈ Scan.lines .west (Scan.ofQuotas rows), SourceOff r A i := by
  intro i hi
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hi
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
  intro q hq he
  have hj : j.val < r.height := j.isLt.trans_eq hlen
  have hy := hA q hq
  change q.2.val = j.val at he
  omega

/-- Row reads, old auxiliary cleanup, then the translated future source program. -/
def unturnedProgram (r : ColumnScan.Input) (rows : List ℕ)
    (tail : List (Scan.Instruction r.width r.height)) :
    List (Scan.Instruction (dock r).outputWidth (dock r).outputHeight) :=
  (Scan.lines .west (Scan.ofQuotas rows)).map (sourceInstruction r) ++
    rowProgram (auxiliaryRows r) (r.width + 2) ++ tail.map (sourceInstruction r)

/-- West data-row reads produce exactly the same original-coordinate remainder. -/
theorem source_rows_eval (r : ColumnScan.Input) (rows : List ℕ)
    (hlen : rows.length = r.height)
    {E F : Finset (Cell (dock r).outputWidth (dock r).outputHeight)}
    (hrows : ∀ q ∈ E, q.2.val < r.height → 2 ≤ q.1.val ∧ q.1.val < r.width + 2)
    (heval : Scan.eval ((Scan.lines .west (Scan.ofQuotas rows)).map (sourceInstruction r)) E = some F) :
    Scan.eval (Scan.lines .west (Scan.ofQuotas rows)) (sourceData r E) = some (sourceData r F) := by
  have htransport := source_program_eval r (Scan.lines .west (Scan.ofQuotas rows))
    (sourceData r E) (auxData r E) (west_source_off r rows hlen _ (by
      intro q hq
      exact (Finset.mem_filter.mp hq).2))
  rw [← source_data_decomposition r E hrows, heval] at htransport
  cases he : Scan.eval (Scan.lines .west (Scan.ofQuotas rows)) (sourceData r E) with
  | none => simp only [he, Option.map_none] at htransport; contradiction
  | some H =>
    rw [he, Option.map_some, Option.some.injEq] at htransport
    have hdata : sourceData r F = H := by
      rw [htransport]
      exact sourceData_frame r H _ (fun q hq => (Finset.mem_filter.mp hq).2)
    exact hdata.symm ▸ rfl

/-- Every accepted dock bitmap yields the exact source row read and every later source instruction. -/
theorem unturned_accepts_sound (r : ColumnScan.Input) (rows : List ℕ)
    (hlen : rows.length = r.height) (tail : List (Scan.Instruction r.width r.height))
    (hbound : ∀ i ∈ tail, SourceBounded r i)
    (E : Finset (Cell (dock r).outputWidth (dock r).outputHeight))
    (hrows : ∀ q ∈ E, q.2.val < r.height → 2 ≤ q.1.val ∧ q.1.val < r.width + 2)
    (hsouth : ∀ q ∈ E, (wideReader r).outputHeight ≤ q.2.val → q.1.val < 2)
    (haccept : Scan.Accepts (unturnedProgram r rows tail) E) :
    Scan.Accepts (Scan.lines .west (Scan.ofQuotas rows) ++ tail) (sourceData r E) := by
  unfold unturnedProgram at haccept
  rw [List.append_assoc] at haccept
  obtain ⟨F, hrow, hrest⟩ := (Scan.accepts_append_iff _ _ E).mp haccept
  obtain ⟨G, hclean, htail⟩ := (Scan.accepts_append_iff _ _ F).mp hrest
  have hFE := Scan.eval_subset hrow
  have hsourceTail := (after_cleanup_accepts_iff r hclean
    (fun q hq hy => hrows q (hFE hq) hy)
    (fun q hq hy => hsouth q (hFE hq) hy) tail hbound).mp htail
  apply (Scan.accepts_append_iff _ _ _).mpr
  exact ⟨sourceData r F, source_rows_eval r rows hlen hrows hrow, hsourceTail⟩

end PushPuzzle.Push.Cyclic
