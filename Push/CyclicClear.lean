/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.Cyclic
public import Push.Scan
import all Push.Scan

/-! Paying one prefix-width quota per old auxiliary row separates every auxiliary source column. -/

public section
namespace PushPuzzle.Push.Cyclic

open PushFS

private theorem consume_remaining_index {α : Type*} [DecidableEq α] {cells : List α}
    {quota : ℕ} {E F : Finset α} (he : Scan.consume cells quota E = some F)
    (k : ℕ) (hk : k < cells.length) (hmem : cells[k] ∈ F) : quota ≤ k := by
  induction cells generalizing quota E k with
  | nil => simp only [List.length_nil] at hk; omega
  | cons a cells ih =>
    cases quota with
    | zero => omega
    | succ q =>
      simp only [Scan.consume] at he
      by_cases ha : a ∈ E
      · rw [ite_eq_left ha] at he
        cases k with
        | zero => exact False.elim ((Finset.mem_erase.mp (Scan.consume_subset he hmem)).1 rfl)
        | succ k =>
          have hh := ih he k (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hk) hmem
          omega
      · rw [ite_eq_right ha] at he
        cases k with
        | zero => exact False.elim (ha (Scan.consume_subset he hmem))
        | succ k =>
          have hh := ih he k (by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hk) hmem
          omega

/-- After paying `p` holes from the west, every remaining hole in that row lies beyond its first `p` cells. -/
theorem west_read_prefix {w h : ℕ} {lane p : ℕ} {E F : Finset (Cell w h)}
    (he : (Scan.Instruction.read .west lane p).eval E = some F)
    (q : Cell w h) (hq : q ∈ F) (hy : q.2.val = lane) : p ≤ q.1.val := by
  have hlay : lane < h := hy ▸ q.2.isLt
  change Scan.consume (Scan.lineCells .west lane) p E = some F at he
  rw [Scan.lineCells, dite_eq_left hlay] at he
  have hpair : (q.1, (⟨lane, hlay⟩ : Fin h)) = q := Prod.ext rfl (Fin.ext hy.symm)
  apply consume_remaining_index he q.1.val (by simp only [List.length_ofFn]; exact q.1.isLt)
  simpa only [List.getElem_ofFn, Fin.eta, hpair] using hq

/-- A family of equal westward row quotas. -/
@[expose] def rowProgram {w h : ℕ} (rows : List ℕ) (p : ℕ) : List (Scan.Instruction w h) :=
  rows.map fun row => .read .west row p

private theorem rowProgram_bounds {w h : ℕ} {rows : List ℕ} {p : ℕ} {E F : Finset (Cell w h)}
    (he : Scan.eval (rowProgram rows p) E = some F) :
    F ⊆ E ∧ ∀ row ∈ rows, ∀ q ∈ F, q.2.val = row → p ≤ q.1.val := by
  induction rows generalizing E with
  | nil =>
    simp only [rowProgram, List.map_nil, Scan.eval, Option.some.injEq] at he
    exact ⟨he ▸ Finset.Subset.refl _, by simp⟩
  | cons row rows ih =>
    simp only [rowProgram, List.map_cons, Scan.eval, Option.bind_eq_some_iff] at he
    obtain ⟨G, hrow, htail⟩ := he
    obtain ⟨hFG, hrest⟩ := ih htail
    refine ⟨hFG.trans (Scan.Instruction.eval_subset hrow), ?_⟩
    intro j hj q hq hqy
    rcases List.mem_cons.mp hj with rfl | hj
    · exact west_read_prefix hrow q (hFG hq) hqy
    · exact hrest j hj q hq hqy

private theorem different_row_unchanged {w h : ℕ} {row p j : ℕ} {E F : Finset (Cell w h)}
    (he : (Scan.Instruction.read .west row p).eval E = some F) (hne : j ≠ row) :
    (F.filter fun q => q.2.val = j) = E.filter fun q => q.2.val = j := by
  ext q
  simp only [Finset.mem_filter]
  by_cases hq : q.2.val = j
  · have hnot : q ∉ Scan.lineCells .west row := by
      intro hh
      exact hne (hq.symm.trans ((Scan.mem_lineCells .west row q).mp hh))
    exact and_congr_left (fun _ => Scan.consume_outside he hnot)
  · simp only [hq, and_false]

/-- Disjoint row quotas can all be paid from their original row inventories. -/
theorem rowProgram_accepts {w h : ℕ} {rows : List ℕ} {p : ℕ} {E : Finset (Cell w h)}
    (hn : rows.Nodup) (hq : ∀ row ∈ rows, p ≤ (E.filter fun q => q.2.val = row).card) :
    Scan.Accepts (rowProgram rows p) E := by
  induction rows generalizing E with
  | nil => exact ⟨E, rfl⟩
  | cons row rows ih =>
    obtain ⟨G, hrow⟩ := (Scan.Instruction.read_accepts_iff .west row p E).mpr (hq row (by simp))
    have htail : Scan.Accepts (rowProgram rows p) G := ih hn.of_cons (by
      intro j hj
      rw [different_row_unchanged hrow (fun he => (List.nodup_cons.mp hn).1 (he ▸ hj))]
      exact hq j (List.mem_cons_of_mem row hj))
    obtain ⟨F, hF⟩ := htail
    exact ⟨F, by simp only [rowProgram, List.map_cons, Scan.eval, hrow, Option.bind_some]; exact hF⟩

/-- Clear every old reader auxiliary row while leaving the new dock rows uncharged. -/
@[expose] def auxiliaryRows (r : ColumnScan.Input) : List ℕ :=
  (List.range ((wideReader r).outputHeight - r.height)).map fun j => r.height + j

/-- Residual auxiliary holes avoid all columns occupied by the original source rectangle. -/
theorem auxiliary_clear_separates {w h : ℕ} (r : ColumnScan.Input) {E F : Finset (Cell w h)}
    (he : Scan.eval (rowProgram (auxiliaryRows r) (r.width + 2)) E = some F)
    (hsouth : ∀ q ∈ E, (wideReader r).outputHeight ≤ q.2.val → q.1.val < 2) :
    ∀ q ∈ F, r.height ≤ q.2.val → q.1.val < 2 ∨ r.width + 2 ≤ q.1.val := by
  obtain ⟨hFE, hrows⟩ := rowProgram_bounds he
  intro q hq hy
  by_cases hs : (wideReader r).outputHeight ≤ q.2.val
  · exact Or.inl (hsouth q (hFE hq) hs)
  · right
    apply hrows q.2.val ?_ q hq rfl
    apply List.mem_map.mpr
    refine ⟨q.2.val - r.height, List.mem_range.mpr (by omega), by omega⟩

end PushPuzzle.Push.Cyclic
