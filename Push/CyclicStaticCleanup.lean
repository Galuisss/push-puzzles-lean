/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicEmbeddedScan
public import Push.CyclicClear

/-! Auxiliary-row cleanup isolates exact source data for every subsequent read or clear. -/

@[expose] public section
namespace PushPuzzle.Push.Cyclic

open PushFS PushS

/-- The original source cells of a static dock hole set. -/
def sourceData (r : ColumnScan.Input)
    (E : Finset (Cell (dock r).outputWidth (dock r).outputHeight)) : Finset (Cell r.width r.height) :=
  Finset.univ.filter fun q => (sourceEmbedding r) q ∈ E

/-- All current holes below the original source rows. -/
def auxData (r : ColumnScan.Input)
    (E : Finset (Cell (dock r).outputWidth (dock r).outputHeight)) :
    Finset (Cell (dock r).outputWidth (dock r).outputHeight) := E.filter fun q => r.height ≤ q.2.val

/-- When source rows contain only source cells, data and auxiliary rows exhaust the complete bitmap. -/
theorem source_data_decomposition (r : ColumnScan.Input)
    (E : Finset (Cell (dock r).outputWidth (dock r).outputHeight))
    (hrows : ∀ q ∈ E, q.2.val < r.height → 2 ≤ q.1.val ∧ q.1.val < r.width + 2) :
    E = (sourceData r E).map (sourceEmbedding r) ∪ auxData r E := by
  ext q
  constructor
  · intro hq
    by_cases hy : q.2.val < r.height
    · obtain ⟨hl, hr⟩ := hrows q hq hy
      let p : Cell r.width r.height := (⟨q.1.val - 2, by omega⟩, ⟨q.2.val, hy⟩)
      have he : (sourceEmbedding r) p = q := by
        apply Prod.ext <;> apply Fin.ext
        · change q.1.val - 2 + 2 = q.1.val
          omega
        · rfl
      exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨p,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, he.symm ▸ hq⟩, he⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hq, by omega⟩)
  · intro hq
    rcases Finset.mem_union.mp hq with hq | hq
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hq
      exact (Finset.mem_filter.mp hp).2
    · exact (Finset.mem_filter.mp hq).1

private theorem auxiliary_row_lower (r : ColumnScan.Input) {row : ℕ} (hr : row ∈ auxiliaryRows r) :
    r.height ≤ row := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
  omega

/-- The old auxiliary-row reads leave every original source bit unchanged. -/
private theorem auxiliary_cleanup_sourceData (r : ColumnScan.Input)
    {E F : Finset (Cell (dock r).outputWidth (dock r).outputHeight)}
    (he : Scan.eval (rowProgram (auxiliaryRows r) (r.width + 2)) E = some F) :
    sourceData r F = sourceData r E := by
  ext p
  simp only [sourceData, Finset.mem_filter, Finset.mem_univ, true_and]
  apply Scan.eval_mem_outside he
  intro i hi
  obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hi
  intro q hq
  have heq : q = (sourceEmbedding r) p := Finset.mem_singleton.mp hq
  rw [heq]
  have hrow := auxiliary_row_lower r hr
  have hpy := p.2.isLt
  change p.2.val ≠ row
  omega

/-- The exact remaining auxiliary holes avoid every original source row and column. -/
private theorem auxiliary_cleanup_orthogonal (r : ColumnScan.Input)
    {E F : Finset (Cell (dock r).outputWidth (dock r).outputHeight)}
    (he : Scan.eval (rowProgram (auxiliaryRows r) (r.width + 2)) E = some F)
    (hsouth : ∀ q ∈ E, (wideReader r).outputHeight ≤ q.2.val → q.1.val < 2) :
    SourceOrthogonal r (auxData r F) := by
  intro q hq
  obtain ⟨hq, hy⟩ := Finset.mem_filter.mp hq
  exact ⟨hy, auxiliary_clear_separates r he hsouth q hq hy⟩

/-- Any later bounded source program reads exactly the data left before auxiliary cleanup. -/
theorem after_cleanup_accepts_iff (r : ColumnScan.Input)
    {E F : Finset (Cell (dock r).outputWidth (dock r).outputHeight)}
    (he : Scan.eval (rowProgram (auxiliaryRows r) (r.width + 2)) E = some F)
    (hrows : ∀ q ∈ E, q.2.val < r.height → 2 ≤ q.1.val ∧ q.1.val < r.width + 2)
    (hsouth : ∀ q ∈ E, (wideReader r).outputHeight ≤ q.2.val → q.1.val < 2)
    (program : List (Scan.Instruction r.width r.height))
    (hbound : ∀ i ∈ program, SourceBounded r i) :
    Scan.Accepts (program.map (sourceInstruction r)) F ↔ Scan.Accepts program (sourceData r E) := by
  have hsub := Scan.eval_subset he
  have hdecomp := source_data_decomposition r F (fun q hq hy => hrows q (hsub hq) hy)
  rw [auxiliary_cleanup_sourceData r he] at hdecomp
  rw [hdecomp]
  apply source_program_accepts_iff
  intro i hi
  exact sourceOff_of_orthogonal r _ (auxiliary_cleanup_orthogonal r he hsouth) i (hbound i hi)

end PushPuzzle.Push.Cyclic
