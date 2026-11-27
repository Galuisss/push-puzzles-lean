/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicPeelingSoundness
public import Push.CyclicTurnProgram
public import Push.CyclicObservation

/-! The actual cyclic next-source step with an arbitrary future bounded scan program. -/

@[expose] public section
namespace PushPuzzle.Push.Cyclic

open PushFS PushS

/-- Translating an actual original source lane keeps it inside the complete dock. -/
theorem sourceInstruction_bounded (r : ColumnScan.Input)
    (i : Scan.Instruction r.width r.height) (hi : SourceBounded r i) :
    (sourceInstruction r i).Bounded := by
  have hlane : ∀ side lane, lane < sourceLaneBound r side →
      sourceLane side lane < Scan.laneCount side (dock r).outputWidth (dock r).outputHeight := by
    intro side lane hb
    have hs := r.length_ge_seven
    cases side <;> simp only [sourceLaneBound, sourceLane, Scan.laneCount] at hb ⊢
    all_goals
      first
      | change lane + 2 < r.width + 2 + (r.width + 1 + r.extraWidth) + 2; omega
      | change lane < r.height + (wideReader r).length + (dock r).distance; omega
  cases i with
  | read side lane quota => exact hlane side lane hi
  | clear side lanes =>
    intro lane hm
    obtain ⟨old, hold, rfl⟩ := Finset.mem_image.mp hm
    exact hlane side old (hi old hold)

/-- The complete unturned step selects only actual source and auxiliary rows. -/
theorem unturnedProgram_bounded (r : ColumnScan.Input) (rows : List ℕ)
    (hlen : rows.length = r.height) (tail : List (Scan.Instruction r.width r.height))
    (hb : ∀ i ∈ tail, SourceBounded r i) : Scan.Bounded (unturnedProgram r rows tail) := by
  intro i hi
  simp only [unturnedProgram, rowProgram, List.mem_append, List.mem_map] at hi
  rcases hi with (⟨old, ho, rfl⟩ | ⟨row, hr, rfl⟩) | ⟨old, ho, rfl⟩
  · apply sourceInstruction_bounded
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ho
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    exact j.isLt.trans_eq hlen
  · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hr
    have hj' := List.mem_range.mp hj
    change r.height + j < (wideReader r).outputHeight + (dock r).distance
    omega
  · exact sourceInstruction_bounded r old (hb old ho)

/-- The next live source's exact static continuation, including all old auxiliary cleanup. -/
def peeledProgram (r : ColumnScan.Input) (rows : List ℕ)
    (tail : List (Scan.Instruction r.width r.height)) :
    List (Scan.Instruction (dock r).outputHeight (dock r).outputWidth) :=
  turnProgram (unturnedProgram r rows tail)

/-- A next-source corner accepting its full future program recovers one original source corner witness. -/
theorem peeling_sound (r : ColumnScan.Input) (rows : List ℕ)
    (hlen : rows.length = r.height) (tail : List (Scan.Instruction r.width r.height))
    (hbound : ∀ i ∈ tail, SourceBounded r i)
    {t : State (dock r).outputHeight (dock r).outputWidth}
    (hr : Reachable (nextSource r).board none (nextSource r).initial t)
    (hp : t.player = (nextSource r).target)
    (haccept : Scan.Accepts (peeledProgram r rows tail) (holes t)) :
    ∃ s : State r.width r.height, Reachable r.sourceBoard none r.initial.toState s ∧
      s.player = r.sourceCorner ∧ Scan.Accepts
        (Scan.columns (Scan.ofQuotas r.quotas) ++ Scan.lines .west (Scan.ofQuotas rows) ++ tail)
        (holes s) := by
  obtain ⟨obs⟩ := observe_nextSource r hr hp
  have hh : holes t = (holes obs.state).map
      (turnEmbedding (dock r).outputWidth (dock r).outputHeight) := by
    have hmap : holes ((turnGeometry (dock r).outputWidth (dock r).outputHeight).state obs.state) =
        (holes obs.state).map (turnEmbedding (dock r).outputWidth (dock r).outputHeight) := by
      ext q
      obtain ⟨p, rfl⟩ := (turnGeometry (dock r).outputWidth (dock r).outputHeight).cells.surjective q
      simp only [mem_holes, GridIsometry.mem_boxes, Finset.mem_map, turnEmbedding,
        Equiv.toEmbedding_apply, (turnGeometry (dock r).outputWidth (dock r).outputHeight).cells.injective.eq_iff,
        exists_eq_right]
    exact (congrArg holes obs.turned.symm).trans hmap
  rw [hh] at haccept
  have hu := (accepts_turn_iff _ (unturnedProgram_bounded r rows hlen tail hbound) _).mp haccept
  exact dock_peeling_sound r rows hlen tail hbound obs.reachable obs.player hu

end PushPuzzle.Push.Cyclic
