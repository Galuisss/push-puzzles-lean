/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicEraseBackup
public import Push.CyclicClear
public import Push.ScanEmbedding
import all Push.CyclicClear

/-! Exact clearing of original data columns by north reads paid from actual prepared backup holes. -/

public section
namespace PushPuzzle.Push.CyclicErase

open PushFS PushS

/-- Original data cells in the actual wider southwest dock. -/
@[expose] def sourceCell (r : ColumnScan.Input) (p : Cell r.width r.height) :
    Cell (eraseDock r).outputWidth (eraseDock r).outputHeight :=
  (eraseDock r).embed ((wideEraseReader r).embed p)

/-- Original-coordinate holes in an arbitrary static dock bitmap. -/
@[expose] def dataHoles (r : ColumnScan.Input)
    (E : Finset (Cell (eraseDock r).outputWidth (eraseDock r).outputHeight)) : Finset (Cell r.width r.height) :=
  Finset.univ.filter fun p => sourceCell r p ∈ E

/-- Enumerate the selected source columns in their actual numerical order. -/
@[expose] def selectedColumns (r : ColumnScan.Input) (selected : Finset (Fin r.width)) : List (Fin r.width) :=
  (List.finRange r.width).filter fun x => x ∈ selected

@[simp] private theorem mem_selectedColumns (r : ColumnScan.Input) (selected : Finset (Fin r.width))
    (x : Fin r.width) : x ∈ selectedColumns r selected ↔ x ∈ selected := by
  simp [selectedColumns]

/-- One top-down read of height `h` in every selected original source-aligned column. -/
@[expose] def eraseRequests (r : ColumnScan.Input) (selected : Finset (Fin r.width)) : List (ℕ × ℕ) :=
  (selectedColumns r selected).map fun x => (x.val + 2, r.height)

/-- Clear selected data columns by top-down height quotas backed by real prepared holes. -/
@[expose] def eraseProgram (r : ColumnScan.Input) (selected : Finset (Fin r.width)) :
    List (Scan.Instruction (eraseDock r).outputWidth (eraseDock r).outputHeight) :=
  Scan.lines .north (eraseRequests r selected)

private theorem eraseRequests_nodup (r : ColumnScan.Input) (selected : Finset (Fin r.width)) :
    ((eraseRequests r selected).map Prod.fst).Nodup := by
  simp only [eraseRequests, List.map_map, Function.comp_def]
  apply List.Nodup.map _ ((List.nodup_finRange r.width).filter _)
  intro a b he
  apply Fin.ext
  change a.val + 2 = b.val + 2 at he
  omega

private theorem lines_outside {w h : ℕ} {side : Direction} {requests : List (ℕ × ℕ)}
    {E F : Finset (Cell w h)} (heval : Scan.eval (Scan.lines side requests) E = some F)
    (q : Cell w h) (hout : ∀ a ∈ requests, side.lane q ≠ a.1) : q ∈ F ↔ q ∈ E := by
  apply Scan.eval_mem_outside heval
  intro i hi
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hi
  intro p hp
  obtain rfl := Finset.mem_singleton.mp hp
  exact hout a ha

private theorem north_read_prefix {w h : ℕ} {lane quota : ℕ} {E F : Finset (Cell w h)}
    (heval : (Scan.Instruction.read .north lane quota).eval E = some F)
    (q : Cell w h) (hq : q ∈ F) (hx : q.1.val = lane) : quota ≤ q.2.val := by
  have hlay : lane < w := hx ▸ q.1.isLt
  change Scan.consume (Scan.lineCells .north lane) quota E = some F at heval
  rw [Scan.lineCells, dite_eq_left hlay] at heval
  have hq' : ((⟨lane, hlay⟩ : Fin w), q.2) = q := Prod.ext (Fin.ext hx.symm) rfl
  apply Cyclic.consume_remaining_index heval q.2.val (by simp only [List.length_ofFn]; exact q.2.isLt)
  simpa only [List.getElem_ofFn, Fin.eta, hq'] using hq

private theorem north_lines_prefix {w h : ℕ} {requests : List (ℕ × ℕ)}
    {E F : Finset (Cell w h)} (heval : Scan.eval (Scan.lines .north requests) E = some F)
    {a : ℕ × ℕ} (ha : a ∈ requests) (q : Cell w h) (hq : q ∈ F) (hx : q.1.val = a.1) : a.2 ≤ q.2.val := by
  induction requests generalizing E with
  | nil => simp only [List.not_mem_nil] at ha
  | cons b rest ih =>
    simp only [Scan.lines, List.map_cons, Scan.eval, Option.bind_eq_some_iff] at heval
    obtain ⟨G, hread, hrest⟩ := heval
    rcases List.mem_cons.mp ha with rfl | ha
    · exact north_read_prefix hread q (Scan.eval_subset hrest hq) hx
    · exact ih hrest ha

/-- The `h` physically prepared holes pay a selected column even when it has no original data. -/
private theorem erase_accepts (r : ColumnScan.Input) (hk : r.height ≤ r.quota) (selected : Finset
    (Fin r.width))
    (E : Finset (Cell (eraseDock r).outputWidth (eraseDock r).outputHeight))
    (hbackup : ∀ x : Fin r.width, ∀ i : Fin r.height, backupCell r hk x i ∈ E) :
    Scan.Accepts (eraseProgram r selected) E := by
  apply Scan.lines_accepts _ _ _ (eraseRequests_nodup r selected)
  intro a ha
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
  let f := fun i : Fin r.height => backupCell r hk x i
  have hinj : Function.Injective f := by
    intro i j he
    have hy := congrArg (fun q => q.2.val) he
    apply Fin.ext
    change (wideEraseReader r).targetLevel + i.val = (wideEraseReader r).targetLevel + j.val at hy
    omega
  have hsub : Finset.univ.image f ⊆ E.filter (fun q => Direction.north.lane q = x.val + 2) := by
    intro q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_filter.mpr ⟨hbackup x i, rfl⟩
  have hc := Finset.card_le_card hsub
  simpa only [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] using hc

/-- Every selected source column is completely cleared; each unselected source cell keeps its exact status. -/
theorem erase_data (r : ColumnScan.Input) (selected : Finset (Fin r.width))
    {E F : Finset (Cell (eraseDock r).outputWidth (eraseDock r).outputHeight)}
    (heval : Scan.eval (eraseProgram r selected) E = some F) :
    dataHoles r F = (dataHoles r E).filter fun p => p.1 ∉ selected := by
  ext p
  simp only [dataHoles, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hp : p.1 ∈ selected
  · have hnot : sourceCell r p ∉ F := by
      intro hq
      have ha : (p.1.val + 2, r.height) ∈ eraseRequests r selected :=
        List.mem_map.mpr ⟨p.1, (mem_selectedColumns r selected _).mpr hp, rfl⟩
      have hh := north_lines_prefix heval ha (sourceCell r p) hq rfl
      change r.height ≤ p.2.val at hh
      exact (Nat.not_le_of_gt p.2.isLt) hh
    simp only [hnot, hp, not_true_eq_false, and_false]
  · have hh := lines_outside heval (sourceCell r p) (by
      intro a ha
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      intro he
      have hpx : p.1 = x := Fin.ext (by change p.1.val + 2 = x.val + 2 at he; omega)
      exact hp (hpx ▸ (mem_selectedColumns r selected _).mp hx))
    simp only [hp, not_false_eq_true, and_true]
    exact hh

/-- North reads touch only the selected source-aligned columns, preserving every eastern room inventory exactly. -/
private theorem erase_room (r : ColumnScan.Input) (selected : Finset (Fin r.width))
    {E F : Finset (Cell (eraseDock r).outputWidth (eraseDock r).outputHeight)}
    (heval : Scan.eval (eraseProgram r selected) E = some F) (row : Fin (eraseDock r).outputHeight) :
    F.filter (fun q => q.2 = row ∧ r.width + 3 ≤ q.1.val) =
      E.filter (fun q => q.2 = row ∧ r.width + 3 ≤ q.1.val) := by
  ext q
  simp only [Finset.mem_filter]
  by_cases hq : q.2 = row ∧ r.width + 3 ≤ q.1.val
  · apply and_congr_left
    intro _
    apply lines_outside heval q
    intro a ha
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
    change q.1.val ≠ x.val + 2
    have := x.isLt
    omega
  · simp only [hq, and_false]

/-- North clearing preserves the room stock, so every old auxiliary row can still pay its full prefix cleanup. -/
theorem erase_and_cleanup (r : ColumnScan.Input) (hk : r.height ≤ r.quota) (selected : Finset (Fin r.width))
    (E : Finset (Cell (eraseDock r).outputWidth (eraseDock r).outputHeight))
    (hbackup : ∀ x : Fin r.width, ∀ i : Fin r.height, backupCell r hk x i ∈ E)
    (hstock : ∀ row : Fin (eraseDock r).outputHeight, r.height ≤ row.val →
      row.val < (wideEraseReader r).outputHeight →
        r.width + 2 ≤ (E.filter fun q => q.2 = row ∧ r.width + 3 ≤ q.1.val).card)
    (hsouth : ∀ q ∈ E, (wideEraseReader r).outputHeight ≤ q.2.val → q.1.val < 2) :
    ∃ F G : Finset (Cell (eraseDock r).outputWidth (eraseDock r).outputHeight),
      Scan.eval (eraseProgram r selected) E = some F ∧
      Scan.eval (Cyclic.rowProgram (Cyclic.auxiliaryRows r) (r.width + 2)) F = some G ∧
      dataHoles r G = (dataHoles r E).filter (fun p => p.1 ∉ selected) ∧
      ∀ q ∈ G, r.height ≤ q.2.val → q.1.val < 2 ∨ r.width + 2 ≤ q.1.val := by
  obtain ⟨F, hF⟩ := erase_accepts r hk selected E hbackup
  have hnd : (Cyclic.auxiliaryRows r).Nodup := by
    apply List.Nodup.map _ List.nodup_range
    intro i j he
    change r.height + i = r.height + j at he
    omega
  have hrow : ∀ row ∈ Cyclic.auxiliaryRows r, r.width + 2 ≤ (F.filter fun q => q.2.val = row).card := by
    intro row hr
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
    have hj' := List.mem_range.mp hj
    have hhi : r.height + j < (wideEraseReader r).outputHeight := by
      change j < (wideEraseReader r).outputHeight - r.height at hj'
      omega
    let y : Fin (eraseDock r).outputHeight := ⟨r.height + j, hhi.trans_le (by
      change (wideEraseReader r).outputHeight ≤ (wideEraseReader r).outputHeight + (eraseDock r).distance
      omega)⟩
    have hs := hstock y (by dsimp [y]; omega) hhi
    rw [← erase_room r selected hF y] at hs
    apply hs.trans (Finset.card_le_card ?_)
    intro q hq
    obtain ⟨hq, hy, _⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨hq, congrArg Fin.val hy⟩
  obtain ⟨G, hG⟩ := Cyclic.rowProgram_accepts hnd hrow
  refine ⟨F, G, hF, hG, ?_, Cyclic.auxiliary_clear_separates r hG ?_⟩
  · rw [← erase_data r selected hF]
    ext p
    simp only [dataHoles, Finset.mem_filter, Finset.mem_univ, true_and]
    have hG' : Scan.eval (Scan.lines .west
        ((Cyclic.auxiliaryRows r).map fun row => (row, r.width + 2))) F = some G := by
      simpa only [Scan.lines, List.map_map, Function.comp_def, Cyclic.rowProgram] using hG
    apply lines_outside hG' (sourceCell r p)
    intro a ha
    obtain ⟨row, hr, rfl⟩ := List.mem_map.mp ha
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
    change p.2.val ≠ r.height + j
    have := p.2.isLt
    omega
  · intro q hq hy
    exact hsouth q (Scan.eval_subset hF hq) hy

end PushPuzzle.Push.CyclicErase
