/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.WholeSourceTransport
public import Push.AcceptanceProgramRounds

/-! Auxiliary cleanup may overpay whole runs while retaining source data and separating source columns. -/

@[expose] public section
namespace PushPuzzle.PushPush.WholeScan

open PushFS (Cell Direction)
open Push.Cyclic

/-- Reading an entire row consumes complete hole components regardless of its box pattern. -/
private theorem Read.full_west {w h lane : ℕ} (E : Finset (Cell w h)) :
    Read .west lane (E.filter fun p => p.2.val = lane).card E
      (E.filter fun p => p.2.val ≠ lane) := by
  let line := Push.Scan.lineCells (w := w) (h := h) .west lane
  have hfront : (E.filter fun p => p ∈ line) = E.filter fun p => p.2.val = lane := by
    ext p
    simp only [Finset.mem_filter, line, Push.Scan.mem_lineCells, Direction.lane]
  have hrest : E \ line.toFinset = E.filter fun p => p.2.val ≠ lane := by
    ext p
    simp only [Finset.mem_sdiff, List.mem_toFinset, Finset.mem_filter, line,
      Push.Scan.mem_lineCells, Direction.lane]
  constructor
  · have he := Push.AcceptanceProgram.consume_prefix line [] E
    rw [List.append_nil, hfront, hrest] at he
    exact he
  · intro p hp q hq ha
    obtain ⟨hp, hpnot⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨_, hq⟩ := Finset.mem_filter.mp hq
    have hpy : p.2.val = lane := by
      by_contra hy
      exact hpnot (Finset.mem_filter.mpr ⟨hp, hy⟩)
    exact hq ((congrArg Fin.val ha.2).trans hpy)

/-- Clearing every requested row uses its entire current hole inventory as the actual payment. -/
theorem LooseExec.full_rows {w h quota : ℕ} (rows : List ℕ) (E : Finset (Cell w h))
    (hn : rows.Nodup)
    (hstock : ∀ row ∈ rows, quota ≤ (E.filter fun p => p.2.val = row).card) :
    LooseExec (rowProgram rows quota) E (E.filter fun p => p.2.val ∉ rows) := by
  induction rows generalizing E with
  | nil => simpa only [rowProgram, List.map_nil, List.not_mem_nil, not_false_eq_true, Finset.filter_true]
      using LooseExec.nil E
  | cons row rows ih =>
    have hn' := List.nodup_cons.mp hn
    have htail := ih (E.filter fun p => p.2.val ≠ row) hn'.2 (by
      intro j hj
      have hne : j ≠ row := fun he => hn'.1 (he ▸ hj)
      have he : ((E.filter fun p => p.2.val ≠ row).filter fun p => p.2.val = j) =
          E.filter fun p => p.2.val = j := by
        ext p
        simp only [Finset.mem_filter]
        exact ⟨fun ⟨⟨hp, _⟩, hy⟩ => ⟨hp, hy⟩,
          fun ⟨hp, hy⟩ => ⟨⟨hp, fun hy' => hne (hy.symm.trans hy')⟩, hy⟩⟩
      rw [he]
      exact hstock j (List.mem_cons_of_mem _ hj))
    have hresult : ((E.filter fun p => p.2.val ≠ row).filter fun p => p.2.val ∉ rows) =
        E.filter fun p => p.2.val ∉ row :: rows := by
      ext p
      simp only [Finset.mem_filter, List.mem_cons, not_or]
      tauto
    rw [hresult] at htail
    exact .cons (hstock row (List.mem_cons_self ..)) (Read.full_west E) htail

private theorem LooseExec.rowProgram_bounds {w h quota : ℕ} {rows : List ℕ} {E F : Finset
    (Cell w h)}
    (H : LooseExec (rowProgram rows quota) E F) :
    F ⊆ E ∧ ∀ row ∈ rows, ∀ q ∈ F, q.2.val = row → quota ≤ q.1.val := by
  induction rows generalizing E with
  | nil => cases H; exact ⟨Finset.Subset.refl _, by simp⟩
  | cons row rows ih =>
    cases H with
    | cons paid head tail =>
      obtain ⟨hsub, hrows⟩ := ih tail
      refine ⟨hsub.trans head.subset, ?_⟩
      intro j hj q hq hy
      rcases List.mem_cons.mp hj with rfl | hj
      · exact paid.trans (west_read_prefix head.eval q (hsub hq) hy)
      · exact hrows j hj q hq hy

theorem LooseExec.rowProgram_sourceData (r : Push.ColumnScan.Input) {rows : List ℕ} {quota : ℕ}
    {E F : Finset (Cell (dock r).outputWidth (dock r).outputHeight)}
    (H : LooseExec (rowProgram rows quota) E F) (hrows : ∀ row ∈ rows, r.height ≤ row) :
    sourceData r F = sourceData r E := by
  induction rows generalizing E with
  | nil => cases H; rfl
  | cons row rows ih =>
    cases H with
    | cons paid head tail =>
      rw [ih tail (fun j hj => hrows j (List.mem_cons_of_mem _ hj))]
      ext p
      simp only [sourceData, Finset.mem_filter, Finset.mem_univ, true_and]
      apply Push.Scan.Instruction.read_outside head.eval
      have hlo := hrows row (List.mem_cons_self ..)
      change p.2.val ≠ row
      have hi := p.2.isLt
      omega

theorem LooseExec.cleanup_orthogonal (r : Push.ColumnScan.Input)
    {E F : Finset (Cell (dock r).outputWidth (dock r).outputHeight)}
    (H : LooseExec (rowProgram (auxiliaryRows r) (r.width + 2)) E F)
    (hsouth : ∀ q ∈ E, (wideReader r).outputHeight ≤ q.2.val → q.1.val < 2) :
    SourceOrthogonal r (auxData r F) := by
  obtain ⟨hsub, hrows⟩ := H.rowProgram_bounds
  intro q hq
  obtain ⟨hq, hy⟩ := Finset.mem_filter.mp hq
  refine ⟨hy, ?_⟩
  by_cases hs : (wideReader r).outputHeight ≤ q.2.val
  · exact Or.inl (hsouth q (hsub hq) hs)
  · apply Or.inr
    apply hrows q.2.val _ q hq rfl
    exact List.mem_map.mpr ⟨q.2.val - r.height, List.mem_range.mpr (by omega), by omega⟩

end PushPuzzle.PushPush.WholeScan
