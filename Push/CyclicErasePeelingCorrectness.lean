/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicErasePeelingCompleteness
public import Push.CyclicPeelingCorrectness
import all Push.CyclicPeelingCorrectness

/-! Complete one-round elimination of a source-column clear, with all future scans preserved. -/

@[expose] public section
namespace PushPuzzle.Push.CyclicErase

open PushFS PushS

/-- The actual next live source after the wider backed dock. -/
abbrev nextSource (r : ColumnScan.Input) : Push.Instance := Cyclic.nextSource (asReader r)

private theorem unturned_bounded (r : ColumnScan.Input) (rows : List ℕ)
    (hlen : rows.length = r.height) (selected : Finset (Fin r.width))
    (tail : List (Scan.Instruction r.width r.height))
    (hb : ∀ i ∈ tail, Cyclic.SourceBounded (asReader r) i) :
    Scan.Bounded (unturnedProgram r rows selected tail) := by
  have hbase := Cyclic.unturnedProgram_bounded (asReader r) rows hlen tail hb
  intro i hi
  simp only [unturnedProgram, List.mem_append] at hi
  rcases hi with ((hrow | herase) | hclean) | htail
  · exact hbase i (by simp only [Cyclic.unturnedProgram, List.mem_append]; tauto)
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp herase
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp ha
    have hx := x.isLt
    change x.val + 2 < r.width + 2 + (r.width + 1 + r.width) + 2
    omega
  · exact hbase i (by simp only [Cyclic.unturnedProgram, List.mem_append]; tauto)
  · exact hbase i (by simp only [Cyclic.unturnedProgram, List.mem_append]; tauto)

/-- The pure-read replacement and complete mapped future program on the actual turned source. -/
def peeledProgram (r : ColumnScan.Input) (rows : List ℕ) (selected : Finset (Fin r.width))
    (tail : List (Scan.Instruction r.width r.height)) :
    List (Scan.Instruction (eraseDock r).outputHeight (eraseDock r).outputWidth) :=
  Cyclic.turnProgram (unturnedProgram r rows selected tail)

/-- The actual backed expansion preserves the entire corner-acceptance language. -/
theorem next_peeling_iff (r : ColumnScan.Input) (hk : r.height ≤ r.quota)
    (rows : List ℕ) (hlen : rows.length = r.height) (selected : Finset (Fin r.width))
    (tail : List (Scan.Instruction r.width r.height))
    (hbound : ∀ i ∈ tail, Cyclic.SourceBounded (asReader r) i) :
    (∃ t : State (eraseDock r).outputHeight (eraseDock r).outputWidth,
      Reachable (nextSource r).board none (nextSource r).initial t ∧
      t.player = (nextSource r).target ∧
        Scan.Accepts (peeledProgram r rows selected tail) (holes t)) ↔
    ∃ s : State r.width r.height, Reachable r.sourceBoard none r.initial.toState s ∧
      s.player = r.sourceCorner ∧ Scan.Accepts
        (Scan.columns (Scan.ofQuotas r.quotas) ++ Scan.lines .west (Scan.ofQuotas rows) ++
          [.clear .north (clearColumns selected)] ++ tail) (holes s) := by
  constructor
  · rintro ⟨t, hr, hp, ha⟩
    obtain ⟨obs⟩ := Cyclic.observe_nextSource (asReader r) hr hp
    have hh : holes t = (holes obs.state).map
        (Cyclic.turnEmbedding (eraseDock r).outputWidth (eraseDock r).outputHeight) :=
      (congrArg holes obs.turned.symm).trans (Cyclic.turn_holes _ _ obs.state)
    rw [hh] at ha
    have hu := (Cyclic.accepts_turn_iff _ (unturned_bounded r rows hlen selected tail hbound) _).mp ha
    exact dock_peeling_sound r rows hlen selected tail hbound obs.reachable obs.player hu
  · rintro ⟨s, hr, hp, ha⟩
    simp only [List.append_assoc] at ha
    obtain ⟨E, hread, htail⟩ := (Scan.accepts_append_iff _ _ _).mp ha
    have htail' : Scan.Accepts (Scan.lines .west (Scan.ofQuotas rows) ++
        [.clear .north (clearColumns selected)] ++ tail) E := by
      simpa only [List.append_assoc] using htail
    obtain ⟨finish, hf, hfp, hfa⟩ := dock_peeling_complete r hk rows hlen selected tail hbound hr hp hread htail'
    let e := Cyclic.turnGeometry (eraseDock r).outputWidth (eraseDock r).outputHeight
    refine ⟨e.state finish, Cyclic.turn_dock_reachable (asReader r) hf, congrArg e.cells hfp, ?_⟩
    have ht := (Cyclic.accepts_turn_iff _ (unturned_bounded r rows hlen selected tail hbound) _).mpr hfa
    have hh := Cyclic.turn_holes (eraseDock r).outputWidth (eraseDock r).outputHeight finish
    exact hh.symm ▸ ht

end PushPuzzle.Push.CyclicErase
