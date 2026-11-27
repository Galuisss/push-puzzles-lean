/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicErase
public import Push.CyclicTwoRoundCompletenessReader
import all Push.CornerDockBackupRows

/-! The actual wide reader pays every backup sweep and retains the required cleanup inventories. -/

public section
namespace PushPuzzle.Push.CyclicErase

open PushFS PushS CornerDock.Backup

private def roomCell (r : ColumnScan.Input) (row : Fin (eraseDock r).outputHeight)
    (hhi : row.val < (wideEraseReader r).outputHeight) (j : Fin (2 * r.width + 2)) :
    Cell (eraseDock r).width (eraseDock r).height :=
  (⟨r.width + 1 + j.val, by
    have := j.isLt
    change r.width + 1 + j.val < r.width + 2 + (r.width + 1 + r.width)
    omega⟩, ⟨row.val, hhi⟩)

private theorem room_stock (r : ColumnScan.Input)
    (source : State (eraseDock r).width (eraseDock r).height)
    (a : HoleState (eraseDock r).outputWidth (eraseDock r).outputHeight)
    (hready : Ready (eraseDock r) source a) (hroom : (wideEraseReader r).room ⊆ holes source)
    (row : Fin (eraseDock r).outputHeight) (hlo : r.height ≤ row.val)
    (hhi : row.val < (wideEraseReader r).outputHeight) :
    2 * r.width + 2 ≤ (rowStock a row (r.width + 3)).card := by
  let f := fun j : Fin (2 * r.width + 2) => (eraseDock r).embed (roomCell r row hhi j)
  have hinj : Function.Injective f := by
    intro i j he
    have hx := congrArg (fun q => q.1.val) ((eraseDock r).embed_injective he)
    apply Fin.ext
    change r.width + 1 + i.val = r.width + 1 + j.val at hx
    omega
  have hsub : Finset.univ.image f ⊆ rowStock a row (r.width + 3) := by
    intro q hq
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hq
    apply Finset.mem_filter.mpr
    refine ⟨(hready.source _).mpr (hroom ?_), Fin.ext rfl, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, hlo⟩
      change r.width < r.width + 1 + j.val
      omega
    · change r.width + 3 ≤ r.width + 1 + j.val + 2
      omega
  have hc := Finset.card_le_card hsub
  simpa only [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] using hc

/-- Literal holes prepared in every original source-aligned column of every selected backup row. -/
@[expose] def backupCell (r : ColumnScan.Input) (hk : r.height ≤ r.quota)
    (x : Fin r.width) (i : Fin r.height) : Cell (eraseDock r).outputWidth (eraseDock r).outputHeight :=
  (⟨x.val + 2, by have := x.isLt; change x.val + 2 < r.width + 2 + (r.width + 1 + r.width) + 2; omega⟩,
    backupRow r hk i)

theorem run_backup_rows_frame (r : ColumnScan.Input) (hk : r.height ≤ r.quota)
    (source : State (eraseDock r).width (eraseDock r).height)
    (a : HoleState (eraseDock r).outputWidth (eraseDock r).outputHeight)
    (ha : a.player = (eraseDock r).target) (hready : Ready (eraseDock r) source a)
    (hroom : (wideEraseReader r).room ⊆ holes source) :
    ∃ t : HoleState (eraseDock r).outputWidth (eraseDock r).outputHeight,
      Reachable (eraseDock r).compile.board none a.toState t.toState ∧ t.player = (eraseDock r).target ∧
      (∀ x : Fin r.width, ∀ i : Fin r.height, backupCell r hk x i ∈ t.empty) ∧
      (∀ p : Cell r.width r.height,
        (eraseDock r).embed ((wideEraseReader r).embed p) ∈ t.empty ↔
          (eraseDock r).embed ((wideEraseReader r).embed p) ∈ a.empty) ∧
      (∀ q : Cell (eraseDock r).outputWidth (eraseDock r).outputHeight, q.2.val < r.height →
        (q ∈ t.empty ↔ q ∈ a.empty)) ∧
      ∀ row : Fin (eraseDock r).outputHeight, r.height ≤ row.val → row.val < (wideEraseReader r).outputHeight →
        r.width + 2 ≤ (rowStock t row (r.width + 3)).card := by
  obtain ⟨t, ht, htp, hfilled, hframe, hstock⟩ := run_rows (eraseDock r) a ha source hready
    (backupRows r hk) (backupRows_nodup r hk) (by
      intro row hr
      have h := backupRows_bounds r hk row hr
      exact ⟨h.1, h.2.le⟩) r.width (r.width + 3) (r.width + 2) (by omega) (by
      intro row hr
      have h := backupRows_bounds r hk row hr
      have hc := room_stock r source a hready hroom row (backupRows_source_below r hk row hr) h.2
      omega)
  refine ⟨t, ht, htp, ?_, ?_, ?_, ?_⟩
  · intro x i
    apply hfilled (backupRow r hk i) (List.mem_ofFn.mpr ⟨i, rfl⟩) (backupCell r hk x i) rfl
    · change 1 ≤ x.val + 2; omega
    · change x.val + 2 ≤ 1 + r.width; have := x.isLt; omega
  · intro p
    apply hframe _ (Or.inl ?_)
    intro hm
    have h := backupRows_source_below r hk _ hm
    change r.height ≤ p.2.val at h
    have := p.2.isLt
    omega
  · intro q hy
    apply hframe q (Or.inl ?_)
    intro hm
    have h := backupRows_source_below r hk _ hm
    omega
  · intro row hlo hhi
    by_cases hr : row ∈ backupRows r hk
    · exact hstock row hr
    · rw [rowStock_frame a t row (r.width + 3) (fun q hq => hframe q (Or.inl (hq ▸ hr)))]
      have hc := room_stock r source a hready hroom row hlo hhi
      omega

end PushPuzzle.Push.CyclicErase
