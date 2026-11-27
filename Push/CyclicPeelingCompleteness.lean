/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicPeelingCompletenessDock
import all Push.CyclicStaticSuffix
import all Push.CyclicStaticCleanup

/-! Every accepted source suffix is paid on the actual canonical dock endpoint. -/

public section
namespace PushPuzzle.Push.Cyclic

open PushFS PushS

private theorem cleanup_stock (r : ColumnScan.Input) {E : Finset (Cell r.width r.height)}
    (c : CanonicalDock r E) (H : Finset (Cell r.width r.height)) :
    ∀ row ∈ auxiliaryRows r, r.width + 2 ≤
      ((H.map (sourceEmbedding r) ∪ auxData r c.state.empty).filter fun q => q.2.val = row).card := by
  intro row hr
  apply (c.stock row hr).trans (Finset.card_le_card ?_)
  intro q hq
  obtain ⟨hq, hy⟩ := Finset.mem_filter.mp hq
  apply Finset.mem_filter.mpr
  refine ⟨?_, hy⟩
  apply Finset.mem_union_right
  apply Finset.mem_filter.mpr
  refine ⟨hq, ?_⟩
  rw [hy]
  exact auxiliary_row_lower r hr

/-- The canonical dock bitmap pays the original row read, all auxiliary cleanup, and every bounded future source instruction. -/
private theorem CanonicalDock.accepts_unturned (r : ColumnScan.Input) {E : Finset
    (Cell r.width r.height)}
    (c : CanonicalDock r E) (rows : List ℕ) (hlen : rows.length = r.height)
    (tail : List (Scan.Instruction r.width r.height)) (hbound : ∀ i ∈ tail, SourceBounded r i)
    (haccept : Scan.Accepts (Scan.lines .west (Scan.ofQuotas rows) ++ tail) E) :
    Scan.Accepts (unturnedProgram r rows tail) c.state.empty := by
  obtain ⟨H, hrow, htail⟩ := (Scan.accepts_append_iff _ _ _).mp haccept
  let A := auxData r c.state.empty
  let F := H.map (sourceEmbedding r) ∪ A
  have haux : ∀ q ∈ A, r.height ≤ q.2.val := fun q hq => (Finset.mem_filter.mp hq).2
  have htransport := source_program_eval r (Scan.lines .west (Scan.ofQuotas rows)) E A
    (west_source_off r rows hlen A haux)
  have hdecomp : c.state.empty = E.map (sourceEmbedding r) ∪ A := by
    rw [source_data_decomposition r c.state.empty c.sourceRows, c.data]
  have hrowActual : Scan.eval ((Scan.lines .west (Scan.ofQuotas rows)).map (sourceInstruction r))
      c.state.empty = some F := by
    rw [hdecomp, htransport, hrow, Option.map_some]
  have hnd : (auxiliaryRows r).Nodup := by
    apply List.Nodup.map _ List.nodup_range
    intro i j he
    change r.height + i = r.height + j at he
    omega
  obtain ⟨G, hclean⟩ := rowProgram_accepts hnd (cleanup_stock r c H)
  have hsub := Scan.eval_subset hrowActual
  have hdataF : sourceData r F = H := sourceData_frame r H A haux
  have htailActual : Scan.Accepts (tail.map (sourceInstruction r)) G := by
    apply (after_cleanup_accepts_iff r hclean (fun q hq hy => c.sourceRows q (hsub hq) hy)
      (fun q hq hy => c.southern q (hsub hq) hy) tail hbound).mpr
    exact hdataF.symm ▸ htail
  unfold unturnedProgram
  rw [List.append_assoc]
  apply (Scan.accepts_append_iff _ _ _).mpr
  refine ⟨F, hrowActual, (Scan.accepts_append_iff _ _ _).mpr ?_⟩
  exact ⟨G, hclean, htailActual⟩

/-- An accepted exact source computation has one real dock target endpoint accepting the complete unturned suffix. -/
theorem peeling_complete (r : ColumnScan.Input) {s : State r.width r.height}
    (hr : Reachable r.sourceBoard none r.initial.toState s) (hcorner : s.player = r.sourceCorner)
    {E : Finset (Cell r.width r.height)}
    (heval : Scan.eval (Scan.columns (Scan.ofQuotas r.quotas)) (holes s) = some E)
    (rows : List ℕ) (hlen : rows.length = r.height)
    (tail : List (Scan.Instruction r.width r.height)) (hbound : ∀ i ∈ tail, SourceBounded r i)
    (haccept : Scan.Accepts (Scan.lines .west (Scan.ofQuotas rows) ++ tail) E) :
    ∃ finish : State (dock r).outputWidth (dock r).outputHeight,
      Reachable (dock r).compile.board none (dock r).compile.initial finish ∧
      finish.player = (dock r).target ∧ Scan.Accepts (unturnedProgram r rows tail) (holes finish) := by
  obtain ⟨c⟩ := canonical_dock r hr hcorner heval
  refine ⟨c.state.toState, c.reachable, c.player, ?_⟩
  exact c.state.holes_toState.symm ▸ c.accepts_unturned r rows hlen tail hbound haccept

end PushPuzzle.Push.Cyclic
