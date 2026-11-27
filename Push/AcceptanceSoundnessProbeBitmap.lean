/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessProbeHorizontal
public import Push.AcceptanceUpperProbeColumns
import all PushS.Holes
import all Push.AcceptanceSoundnessCentral

/-! The complete non-main upper probe bitmap is fixed throughout every actual accepted trajectory. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate

private theorem probe_bitmap_step
    {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (hsource : ∀ q : Cell (p.W + 1) (p.H + 1), q.2.val ∈ probeRows l p → q.1 ∉ l.mainColumnSet p →
      (q ∈ PushS.holes u ↔ q ∈ PushS.holes (I).initial)) :
    ∀ q : Cell (p.W + 1) (p.H + 1), q.2.val ∈ probeRows l p → q.1 ∉ l.mainColumnSet p →
      (q ∈ PushS.holes v ↔ q ∈ PushS.holes (I).initial) := by
  have hut := (Relation.ReflTransGen.single hm).trans hvt
  obtain ⟨d, move⟩ := hm
  cases move with
  | walk _ _ _ _ boxes =>
    intro q hrow hnmain
    simpa only [PushS.mem_holes, boxes] using hsource q hrow hnmain
  | @push n _ hn _ run hp boxes =>
    let run : Run (w := p.W + 1) (h := p.H + 1) (I).board d u n := run
    have hholes : (PushS.holes v : Finset (Cell (p.W + 1) (p.H + 1))) =
        insert (run.cell 1) ((PushS.holes u).erase (run.cell ⟨n + 1, by omega⟩)) := holes_push run hn boxes
    have actual : Step (I).board none u v := ⟨d, .push (hsu.valid (I).initial_valid) hn trivial run hp boxes⟩
    intro q hrow hnmain
    have horizontal (hd : d = .east ∨ d = .west)
        (hfield : q = run.cell 1 ∨ q = run.cell ⟨n + 1, by omega⟩) : False := by
      have hy : (run.cell ⟨n + 1, by omega⟩).2.val = q.2.val := by
        rcases hfield with hfirst | hlast
        · rcases hd with rfl | rfl <;>
            exact ((run.lane ⟨n + 1, by omega⟩).trans (run.lane 1).symm).trans (congrArg (fun q => q.2.val) hfirst.symm)
        · exact congrArg (fun q => q.2.val) hlast.symm
      exact canonical_probe_horizontal_impossible_of_source l p hl hM haxes initial target hgate hsu actual hvt ha
        run hn hp boxes hd (hy ▸ hrow) (fun r hr hmain hhole => (hsource r hr hmain).mp hhole)
    have noFirst (hd : d = .north ∨ d = .south) : q ≠ run.cell 1 := by
      intro heq
      have hcol : q.1 ∈ l.pageColumnSet p .upper := by
        have hi : (⟨0, by omega⟩ : Fin (n + 1)).succ = (1 : Fin (n + 2)) := by
          apply Fin.ext
          simp only [Fin.val_succ, Fin.val_one]
        have hc := canonical_vertical_probe_page_column l p hl hM haxes initial target hsu hvt ha run hn hp boxes hd
          (⟨0, by omega⟩ : Fin (n + 1)) (by rw [hi]; exact heq ▸ hrow)
        rw [hi, ← heq] at hc
        exact hc
      have hu := canonical_upper_probe_page_column_constant l p hl hM haxes initial target hgate hsu hut ha hrow hcol hnmain
      have hv := canonical_upper_probe_page_column_constant l p hl hM haxes initial target hgate (hsu.tail actual) hvt ha hrow hcol hnmain
      have hafter : q ∈ PushS.holes v := by rw [hholes]; exact heq ▸ Finset.mem_insert_self _ _
      exact (PushS.mem_holes _).mp (hu.mpr (hv.mp hafter)) (heq ▸ run.first_occupied hn)
    have noLast (hd : d = .north ∨ d = .south) : q ≠ run.cell ⟨n + 1, by omega⟩ := by
      intro heq
      have hcol : q.1 ∈ l.pageColumnSet p .upper := by
        have hi : (⟨n, by omega⟩ : Fin (n + 1)).succ = (⟨n + 1, by omega⟩ : Fin (n + 2)) := rfl
        have hc := canonical_vertical_probe_page_column l p hl hM haxes initial target hsu hvt ha run hn hp boxes hd
          (⟨n, by omega⟩ : Fin (n + 1)) (by rw [hi]; exact heq ▸ hrow)
        rw [hi, ← heq] at hc
        exact hc
      have hu := canonical_upper_probe_page_column_constant l p hl hM haxes initial target hgate hsu hut ha hrow hcol hnmain
      have hv := canonical_upper_probe_page_column_constant l p hl hM haxes initial target hgate (hsu.tail actual) hvt ha hrow hcol hnmain
      have hbefore : q ∈ PushS.holes u := (PushS.mem_holes _).mpr (heq ▸ run.empty)
      have hafter : q ∈ v.boxes := by rw [boxes]; exact heq ▸ Finset.mem_insert_self _ _
      exact (PushS.mem_holes _).mp (hv.mpr (hu.mp hbefore)) hafter
    have hfirst : q ≠ run.cell 1 := by
      cases d with
      | north => exact noFirst (Or.inl rfl)
      | south => exact noFirst (Or.inr rfl)
      | east => exact fun h => horizontal (Or.inl rfl) (Or.inl h)
      | west => exact fun h => horizontal (Or.inr rfl) (Or.inl h)
    have hlast : q ≠ run.cell ⟨n + 1, by omega⟩ := by
      cases d with
      | north => exact noLast (Or.inl rfl)
      | south => exact noLast (Or.inr rfl)
      | east => exact fun h => horizontal (Or.inl rfl) (Or.inr h)
      | west => exact fun h => horizontal (Or.inr rfl) (Or.inr h)
    rw [hholes]
    simp only [Finset.mem_insert, Finset.mem_erase, hfirst, false_or]
    constructor
    · intro h
      exact (hsource q hrow hnmain).mp h.2
    · intro h
      exact ⟨hlast, (hsource q hrow hnmain).mpr h⟩

/-- Every real accepted prefix has exactly the original non-main upper probe holes, cell by cell. -/
theorem canonical_upper_probe_nonmain_constant
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)} (hrow : q.2.val ∈ probeRows l p) (hnmain : q.1 ∉ l.mainColumnSet p) :
    (q ∈ PushS.holes u ↔ q ∈ PushS.holes (I).initial) := by
  let P := fun s : State (p.W + 1) (p.H + 1) =>
    ∀ q : Cell (p.W + 1) (p.H + 1), q.2.val ∈ probeRows l p → q.1 ∉ l.mainColumnSet p →
      (q ∈ PushS.holes s ↔ q ∈ PushS.holes (I).initial)
  have decorated : Relation.ReflTransGen (fun a b => Step (I).board none a b ∧ (P a → P b)) (I).initial u := by
    apply Path.enrich hsu
    intro a b hsa hm hbu
    exact ⟨hm, probe_bitmap_step l p hl hM haxes initial target hgate hsa hm (hbu.trans hut) ha⟩
  have hp : P u := by
    clear hsu hut
    induction decorated with
    | refl => exact fun _ _ _ => Iff.rfl
    | tail _ step ih => exact step.2 ih
  exact hp q hrow hnmain

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
