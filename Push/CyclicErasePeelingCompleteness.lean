/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicErasePeelingSoundness
import all Push.CyclicStaticSuffix

/-! Prepared physical backups preserve arbitrary source row reads and every bounded post-erase program. -/

public section
namespace PushPuzzle.Push.CyclicErase

open PushFS PushS

private theorem source_rows_outside (r : ColumnScan.Input) (rows : List ℕ)
    (hlen : rows.length = r.height)
    {E F : Finset (Cell (eraseDock r).outputWidth (eraseDock r).outputHeight)}
    (he : Scan.eval ((Scan.lines .west (Scan.ofQuotas rows)).map
      (Cyclic.sourceInstruction (asReader r))) E = some F)
    (q : Cell (eraseDock r).outputWidth (eraseDock r).outputHeight)
    (hy : r.height ≤ q.2.val) : q ∈ F ↔ q ∈ E := by
  apply Scan.eval_mem_outside he
  intro i hi
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hi
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hold
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
  intro p hp
  have hpq : p = q := Finset.mem_singleton.mp hp
  rw [hpq]
  have hj : j.val < r.height := j.isLt.trans_eq hlen
  change q.2.val ≠ j.val
  omega

/-- Every exact source read/clear suffix is accepted by one actual backed dock endpoint. -/
theorem dock_peeling_complete (r : ColumnScan.Input) (hk : r.height ≤ r.quota)
    (rows : List ℕ) (hlen : rows.length = r.height) (selected : Finset (Fin r.width))
    (tail : List (Scan.Instruction r.width r.height))
    (hbound : ∀ i ∈ tail, Cyclic.SourceBounded (asReader r) i)
    {s : State r.width r.height} (hr : Reachable r.sourceBoard none r.initial.toState s)
    (hp : s.player = r.sourceCorner) {E : Finset (Cell r.width r.height)}
    (heval : Scan.eval (Scan.columns (Scan.ofQuotas r.quotas)) (holes s) = some E)
    (ha : Scan.Accepts (Scan.lines .west (Scan.ofQuotas rows) ++
      [.clear .north (clearColumns selected)] ++ tail) E) :
    ∃ finish : State (eraseDock r).outputWidth (eraseDock r).outputHeight,
      Reachable (eraseDock r).compile.board none (eraseDock r).compile.initial finish ∧
      finish.player = (eraseDock r).target ∧
        Scan.Accepts (unturnedProgram r rows selected tail) (holes finish) := by
  rw [List.append_assoc] at ha
  obtain ⟨H, hrow, htail⟩ := (Scan.accepts_append_iff _ _ _).mp ha
  have htail' : Scan.Accepts tail (H.filter fun p => p.1 ∉ selected) := by
    simpa only [Scan.Accepts, List.singleton_append, Scan.eval, clearColumns_eval,
      Option.bind_some] using htail
  obtain ⟨t, ht, htp, hdata, hbackup, hstock, hs, hsouth⟩ := compile_backups_supported r hk hr hp heval
  let A := Cyclic.auxData (asReader r) t.empty
  let F := H.map (Cyclic.sourceEmbedding (asReader r)) ∪ A
  have haux : ∀ q ∈ A, r.height ≤ q.2.val := fun q hq => (Finset.mem_filter.mp hq).2
  have hdataT : Cyclic.sourceData (asReader r) t.empty = E := by
    ext p
    simp only [Cyclic.sourceData, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hdata p
  have hdecomp : t.empty = E.map (Cyclic.sourceEmbedding (asReader r)) ∪ A := by
    rw [Cyclic.source_data_decomposition (asReader r) t.empty hs, hdataT]
  have hrowActual : Scan.eval ((Scan.lines .west (Scan.ofQuotas rows)).map
      (Cyclic.sourceInstruction (asReader r))) t.empty = some F := by
    rw [hdecomp, Cyclic.source_program_eval (asReader r) _ E A
      (Cyclic.west_source_off (asReader r) rows hlen A haux), hrow, Option.map_some]
  have hsub := Scan.eval_subset hrowActual
  have hbackupF : ∀ x : Fin r.width, ∀ i : Fin r.height, backupCell r hk x i ∈ F := by
    intro x i
    apply (source_rows_outside r rows hlen hrowActual _ ?_).mpr (hbackup x i)
    have hlev := r.targetLevel_lower
    change r.height ≤ r.targetLevel + i.val
    omega
  have hstockF : ∀ row : Fin (eraseDock r).outputHeight, r.height ≤ row.val →
      row.val < (wideEraseReader r).outputHeight →
        r.width + 2 ≤ (F.filter fun q => q.2 = row ∧ r.width + 3 ≤ q.1.val).card := by
    intro row hlo hhi
    have heq : F.filter (fun q => q.2 = row ∧ r.width + 3 ≤ q.1.val) =
        t.empty.filter (fun q => q.2 = row ∧ r.width + 3 ≤ q.1.val) := by
      ext q
      simp only [Finset.mem_filter]
      by_cases hq : q.2 = row ∧ r.width + 3 ≤ q.1.val
      · exact and_congr_left (fun _ => source_rows_outside r rows hlen hrowActual q (by
          rw [hq.1]; exact hlo))
      · simp only [hq, and_false]
    rw [heq]
    exact hstock row hlo hhi
  obtain ⟨G, J, B, hG, hJ, hframe, hB⟩ := erase_cleanup_orthogonal r hk selected F hbackupF hstockF
    (fun q hq hy => hs q (hsub hq) hy) (fun q hq hy => hsouth q (hsub hq) hy)
  have hdataF : dataHoles r F = H := Cyclic.sourceData_frame (asReader r) H A haux
  have htailActual : Scan.Accepts (tail.map (Cyclic.sourceInstruction (asReader r))) J := by
    rw [hdataF] at hframe
    have hframe' : J = (H.filter fun p => p.1 ∉ selected).map
        (Cyclic.sourceEmbedding (asReader r)) ∪ B := by
      have hemb : (Cyclic.sourceEmbedding (asReader r) : Cell r.width r.height →
          Cell (eraseDock r).outputWidth (eraseDock r).outputHeight) = sourceCell r := rfl
      rw [Finset.map_eq_image, hemb]
      exact hframe
    rw [hframe']
    apply (Cyclic.source_program_accepts_iff (asReader r) tail _ B ?_).mpr htail'
    intro i hi
    exact Cyclic.sourceOff_of_orthogonal (asReader r) B hB i (hbound i hi)
  refine ⟨t.toState, ht, htp, ?_⟩
  rw [t.holes_toState]
  unfold unturnedProgram
  simp only [List.append_assoc]
  apply (Scan.accepts_append_iff _ _ _).mpr
  refine ⟨F, hrowActual, (Scan.accepts_append_iff _ _ _).mpr ?_⟩
  refine ⟨G, hG, (Scan.accepts_append_iff _ _ _).mpr ?_⟩
  exact ⟨J, hJ, htailActual⟩

end PushPuzzle.Push.CyclicErase
