/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicEraseCleanup
public import Push.CyclicPeelingSoundness

/-! Every actual erase-stage observation preserves the complete original read/clear suffix. -/

@[expose] public section
namespace PushPuzzle.Push.CyclicErase

open PushFS PushS

/-- The original source column family, named by its actual finite column indices. -/
def clearColumns {w : ℕ} (selected : Finset (Fin w)) : Finset ℕ := selected.image Fin.val

/-- Clearing the named source columns removes exactly their original finite column indices. -/
theorem clearColumns_eval {w h : ℕ} (selected : Finset (Fin w)) (E : Finset (Cell w h)) :
    (Scan.Instruction.clear .north (clearColumns selected)).eval E =
      some (E.filter fun p => p.1 ∉ selected) := by
  simp only [Scan.Instruction.eval, clearColumns, Direction.lane, Finset.mem_image,
    Fin.val_injective.eq_iff, exists_eq_right]

/-- Data row reads, backed north reads, auxiliary cleanup, and the full future source program. -/
def unturnedProgram (r : ColumnScan.Input) (rows : List ℕ) (selected : Finset (Fin r.width))
    (tail : List (Scan.Instruction r.width r.height)) :
    List (Scan.Instruction (eraseDock r).outputWidth (eraseDock r).outputHeight) :=
  (Scan.lines .west (Scan.ofQuotas rows)).map (Cyclic.sourceInstruction (asReader r)) ++
    eraseProgram r selected ++ Cyclic.rowProgram (Cyclic.auxiliaryRows r) (r.width + 2) ++
      tail.map (Cyclic.sourceInstruction (asReader r))

private theorem static_suffix_sound (r : ColumnScan.Input) (rows : List ℕ)
    (hlen : rows.length = r.height) (selected : Finset (Fin r.width))
    (tail : List (Scan.Instruction r.width r.height))
    (hbound : ∀ i ∈ tail, Cyclic.SourceBounded (asReader r) i)
    (E : Finset (Cell (eraseDock r).outputWidth (eraseDock r).outputHeight))
    (hrows : DataSupported r E)
    (hsouth : ∀ q ∈ E, (wideEraseReader r).outputHeight ≤ q.2.val → q.1.val < 2)
    (ha : Scan.Accepts (unturnedProgram r rows selected tail) E) :
    Scan.Accepts (Scan.lines .west (Scan.ofQuotas rows) ++
      [.clear .north (clearColumns selected)] ++ tail) (dataHoles r E) := by
  unfold unturnedProgram at ha
  rw [List.append_assoc, List.append_assoc] at ha
  obtain ⟨F, hread, hrest⟩ := (Scan.accepts_append_iff _ _ _).mp ha
  obtain ⟨G, herase, hrest⟩ := (Scan.accepts_append_iff _ _ _).mp hrest
  obtain ⟨H, hclean, htail⟩ := (Scan.accepts_append_iff _ _ _).mp hrest
  have hFE := Scan.eval_subset hread
  have hGE := (Scan.eval_subset herase).trans hFE
  have hsource := (Cyclic.after_cleanup_accepts_iff (asReader r) hclean
    (fun q hq hy => hrows q (hGE hq) hy)
    (fun q hq hy => hsouth q (hGE hq) hy) tail hbound).mp htail
  have hdata : Cyclic.sourceData (asReader r) G =
      (dataHoles r F).filter fun p => p.1 ∉ selected := erase_data r selected herase
  rw [hdata] at hsource
  rw [List.append_assoc]
  apply (Scan.accepts_append_iff _ _ _).mpr
  refine ⟨dataHoles r F, Cyclic.source_rows_eval (asReader r) rows hlen hrows hread, ?_⟩
  obtain ⟨T, hT⟩ := hsource
  exact ⟨T, by simpa only [List.singleton_append, Scan.eval, clearColumns_eval, Option.bind_some] using hT⟩

/-- Arbitrary physical erasure endpoints recover one source corner accepting the exact original program. -/
theorem dock_peeling_sound (r : ColumnScan.Input) (rows : List ℕ)
    (hlen : rows.length = r.height) (selected : Finset (Fin r.width))
    (tail : List (Scan.Instruction r.width r.height))
    (hbound : ∀ i ∈ tail, Cyclic.SourceBounded (asReader r) i)
    {finish : State (eraseDock r).outputWidth (eraseDock r).outputHeight}
    (hr : Reachable (eraseDock r).compile.board none (eraseDock r).compile.initial finish)
    (hp : finish.player = (eraseDock r).target)
    (ha : Scan.Accepts (unturnedProgram r rows selected tail) (holes finish)) :
    ∃ s : State r.width r.height, Reachable r.sourceBoard none r.initial.toState s ∧
      s.player = r.sourceCorner ∧ Scan.Accepts
        (Scan.columns (Scan.ofQuotas r.quotas) ++ Scan.lines .west (Scan.ofQuotas rows) ++
          [.clear .north (clearColumns selected)] ++ tail) (holes s) := by
  obtain ⟨c⟩ := Cyclic.exists_commit (asReader r) hr hp
  have hs := static_suffix_sound r rows hlen selected tail hbound (holes finish)
    (c.source_row_columns c.suffix)
    (fun q hq hy => (Cyclic.dock_source_support (asReader r) hr q hq).resolve_right
      (Nat.not_lt.mpr hy)) ha
  refine ⟨c.sourceState, c.source_reachable, c.source_player, ?_⟩
  simp only [List.append_assoc] at hs ⊢
  exact c.lift_source_suffix hs

end PushPuzzle.Push.CyclicErase
