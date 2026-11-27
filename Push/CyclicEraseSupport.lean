/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicEraseBackup
public import Push.CyclicEraseScan
public import Push.ConvexSupport
import all Push.CornerDockReverse

/-! Actual backup preparation retains both source-row support and the full southern quadrant. -/

public section
namespace PushPuzzle.Push.CyclicErase

open PushFS PushS CornerDock.Backup

/-- Every hole on a data row lies in its original translated data rectangle. -/
@[expose] def DataSupported (r : ColumnScan.Input)
    (E : Finset (Cell (eraseDock r).outputWidth (eraseDock r).outputHeight)) : Prop :=
  ∀ q ∈ E, q.2.val < r.height → 2 ≤ q.1.val ∧ q.1.val < r.width + 2

private theorem western_hole_below (r : ColumnScan.Input)
    {s : State (eraseDock r).outputWidth (eraseDock r).outputHeight}
    (hr : Reachable (eraseDock r).compile.board none (eraseDock r).compile.initial s)
    (q : Cell (eraseDock r).outputWidth (eraseDock r).outputHeight) (hq : q ∈ holes s) :
    2 ≤ q.1.val ∨ (wideEraseReader r).targetLevel ≤ q.2.val := by
  have hi : PushS.Support.Supported {p : Cell (eraseDock r).outputWidth (eraseDock r).outputHeight |
      2 ≤ p.1.val ∨ (wideEraseReader r).targetLevel ≤ p.2.val} (eraseDock r).compile.initial := by
    intro p hp
    have hh : p ∈ ((eraseDock r).extend (eraseDock r).initial).empty :=
      ((eraseDock r).extend (eraseDock r).initial).holes_toState ▸ (mem_holes _).mpr hp
    rcases Finset.mem_union.mp hh with hsource | haux
    · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hsource
      exact Or.inl (by change 2 ≤ a.1.val + 2; omega)
    · rcases Finset.mem_insert.mp haux with rfl | hwalk
      · exact Or.inr le_rfl
      · have hwork := (Finset.mem_filter.mp hwalk).2.2
        have hlevel := (wideEraseReader r).targetLevel_le_needleLevel ⟨0, r.width_pos⟩
        have hbound := (wideEraseReader r).needleLevel_lt_height ⟨0, r.width_pos⟩
        exact Or.inr (by change (wideEraseReader r).outputHeight ≤ p.2.val at hwork; omega)
  exact (Push.Support.northwest_compl_axisConvex 2 (wideEraseReader r).targetLevel).reachable_target
    hr hi q ((mem_holes _).mp hq)

/-- The physical preparation creates only auxiliary holes and leaves the southern source-aligned region full. -/
theorem compile_backups_supported (r : ColumnScan.Input) (hk : r.height ≤ r.quota)
    {s : State r.width r.height} (hr : Reachable r.sourceBoard none r.initial.toState s)
    (hcorner : s.player = r.sourceCorner) {E : Finset (Cell r.width r.height)}
    (heval : Scan.eval (Scan.columns (Scan.ofQuotas r.quotas)) (holes s) = some E) :
    ∃ t : HoleState (eraseDock r).outputWidth (eraseDock r).outputHeight,
      Reachable (eraseDock r).compile.board none (eraseDock r).compile.initial t.toState ∧
      t.player = (eraseDock r).target ∧
      (∀ p : Cell r.width r.height, sourceCell r p ∈ t.empty ↔ p ∈ E) ∧
      (∀ x : Fin r.width, ∀ i : Fin r.height, backupCell r hk x i ∈ t.empty) ∧
      (∀ row : Fin (eraseDock r).outputHeight, r.height ≤ row.val → row.val < (wideEraseReader r).outputHeight →
        r.width + 2 ≤ (rowStock t row (r.width + 3)).card) ∧
      DataSupported r t.empty ∧
      ∀ q ∈ t.empty, (wideEraseReader r).outputHeight ≤ q.2.val → q.1.val < 2 := by
  obtain ⟨source, hs, hsp, hE, hroom, hsupport⟩ :=
    Cyclic.first_round_exact_supported (wideEraseReader r) hr hcorner heval
  obtain ⟨a, ha, hap, hready⟩ := compile_ready (eraseDock r) (hs.reboard rfl) hsp
  obtain ⟨t, ht, htp, hbackup, hsource, hrows, hstock⟩ := run_backup_rows_frame r hk source a hap hready hroom
  have hfull := ha.trans ht
  refine ⟨t, hfull, htp, ?_, hbackup, hstock, ?_, ?_⟩
  · intro p
    exact (hsource p).trans ((hready.source ((wideEraseReader r).embed p)).trans (hE p))
  · intro q hq hy
    have hleft := western_hole_below r hfull q (t.holes_toState.symm ▸ hq)
    have hlevel := (wideEraseReader r).targetLevel_lower
    have hx : 2 ≤ q.1.val := by change r.height + max r.sourceHoles r.width < _ at hlevel; omega
    refine ⟨hx, ?_⟩
    have hqa := (hrows q hy).mp hq
    let p : Cell (eraseDock r).width (eraseDock r).height :=
      (⟨q.1.val - 2, by have := q.1.isLt; change q.1.val < (eraseDock r).width + 2 at this; omega⟩,
        ⟨q.2.val, by
          have hh := (wideEraseReader r).length_ge_seven
          change q.2.val < r.height + (wideEraseReader r).length
          omega⟩)
    have hp : (eraseDock r).embed p = q := Prod.ext (Fin.ext (by dsimp [p, CornerDock.Input.embed]; omega)) (Fin.ext rfl)
    have hps := (hready.source p).mp (hp.symm ▸ hqa)
    have hright := hsupport p hps hy
    change q.1.val - 2 < r.width at hright
    omega
  · intro q hq hy
    have h := (eraseDock r).hole_support hfull q (t.holes_toState.symm ▸ hq)
    change q.1.val < 2 ∨ q.2.val < (wideEraseReader r).outputHeight at h
    omega

end PushPuzzle.Push.CyclicErase
