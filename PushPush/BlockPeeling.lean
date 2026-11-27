/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.BlockLanguage
public import PushPush.CyclicForward
public import PushPush.CyclicWhole
public import PushPush.CyclicObservation
public import PushPush.WholeBlockHeader
public import PushPush.WholeBlocksTurn

/-! A complete physical maximum-reader round preserves every future whole-round program. -/

@[expose] public section
namespace PushPuzzle.PushPush.CyclicReader

open PushFS (Cell State)
open Push.AcceptanceProgram Push.Cyclic

variable (r : Push.ColumnScan.Input) (requests : List (ℕ × ℕ))
  (hb : (rowQuotas r requests).sum ≤ r.sourceHoles) (rest : List Round)
  (hbound : ∀ i ∈ instructions rest, SourceBounded r i)

include hbound

private theorem next_language_sound
    (H : Language (nextInput r (rowQuotas r requests) (rowQuotas_length r requests) hb)
      (nextRounds r rest)) : Language r (.read .west requests :: rest) := by
  obtain ⟨t, hr, hp, E, F, hhead, htail⟩ := H
  obtain ⟨o⟩ := Cyclic.observe_nextInput r _ _ hb hr hp
  obtain ⟨c⟩ := Cyclic.exists_commit r o.reachable o.player
  let e := turnGeometry (dock r).outputWidth (dock r).outputHeight
  have hh : PushS.holes (e.state o.state) = (PushS.holes o.state).map (turnEmbedding (dock r).outputWidth (dock r).outputHeight) :=
    reorient_holes e o.state
  have hstart : t.boxesᶜ = (PushS.holes o.state).map (turnEmbedding (dock r).outputWidth (dock r).outputHeight) :=
    (congrArg (fun s => s.boxesᶜ) o.turned).symm.trans hh
  have hhead' : WholeScan.LooseExec
      (Push.Scan.columns (Push.Scan.ofQuotas (nextQuotas r (rowQuotas r requests))))
      ((PushS.holes o.state).map (turnEmbedding (dock r).outputWidth (dock r).outputHeight)) E := hstart ▸ hhead
  have hordinary := Reachable.unit_expansion o.reachable (dock r).compile.board rfl
  obtain ⟨R⟩ := Cyclic.next_header_sound r (rowQuotas r requests) (rowQuotas_length r requests)
    (PushS.holes o.state) (c.trace.source_row_columns c.trace.suffix)
    (fun q hq hy => (dock_source_support r hordinary q hq).resolve_right (by omega)) hhead'
  have hbRest : Push.Scan.Bounded (instructions (w := r.width) (h := r.height) rest) :=
    fun i hi => (sourceBounded_iff_bounded r i).mp (hbound i hi)
  have htail' : WholeBlocks.Exec ((rest.map sourceRound).map (turnRound (dock r).outputWidth))
      (R.remaining.map (turnEmbedding (dock r).outputWidth (dock r).outputHeight)) F := by
    have heq : (rest.map sourceRound).map (turnRound (dock r).outputWidth) = nextRounds r rest :=
      List.map_map
    apply Eq.mpr (congrArg (fun rounds => WholeBlocks.Exec rounds
      (R.remaining.map (turnEmbedding (dock r).outputWidth (dock r).outputHeight)) F) heq)
    exact Eq.mpr (congrArg (fun A => WholeBlocks.Exec (nextRounds r rest) A F) R.turned) htail
  obtain ⟨G, hsourceTail, _⟩ := htail'.unturn (rest.map sourceRound) R.remaining
    (WholeBlocks.sourceRounds_bounded r rest hbRest)
  have hfuture := hsourceTail.source r rest R.source_rows R.orthogonal
  refine ⟨c.trace.sourceState, c.source, c.trace.source_player,
    originalHoles r o.state, sourceData r G, c.loose_columns, .cons R.data hfuture⟩

private theorem next_language_complete (H : Language r (.read .west requests :: rest)) :
    Language (nextInput r (rowQuotas r requests) (rowQuotas_length r requests) hb)
      (nextRounds r rest) := by
  obtain ⟨s, hr, hp, E, F, hfirst, hrounds⟩ := H
  cases hrounds with
  | @cons _ _ _ _ G _ hrow htail =>
    obtain ⟨c⟩ := Cyclic.canonical_dock r hr hp hfirst
    have hnext := Cyclic.next_header_complete r (rowQuotas r requests) (rowQuotas_length r requests)
      c.state.empty c.data c.sourceRows c.stock hrow
    have hbRest : Push.Scan.Bounded (instructions (w := r.width) (h := r.height) rest) :=
      fun i hi => (sourceBounded_iff_bounded r i).mp (hbound i hi)
    have hsource := htail.source_lift r rest hbRest ∅ (by simp [SourceOrthogonal])
    simp only [Finset.union_empty] at hsource
    have hturned := hsource.turn (rest.map sourceRound)
      (WholeBlocks.sourceRounds_bounded r rest hbRest)
    let e := turnGeometry (dock r).outputWidth (dock r).outputHeight
    obtain ⟨hre, hpe⟩ := Cyclic.turn_nextInput r (rowQuotas r requests) (rowQuotas_length r requests)
      hb c.actual c.player
    have hh : (e.state c.state.toState).boxesᶜ = c.state.empty.map (turnEmbedding (dock r).outputWidth (dock r).outputHeight) :=
      (reorient_holes e c.state.toState).trans
        (congrArg (Finset.map (turnEmbedding (dock r).outputWidth (dock r).outputHeight)) c.state.holes_toState)
    refine ⟨e.state c.state.toState, hre, hpe,
      (G.map (sourceEmbedding r)).map (turnEmbedding (dock r).outputWidth (dock r).outputHeight),
      (F.map (sourceEmbedding r)).map (turnEmbedding (dock r).outputWidth (dock r).outputHeight), ?_, ?_⟩
    · exact Eq.mpr (congrArg (fun A => WholeScan.LooseExec
        (Push.Scan.columns (w := (dock r).outputHeight) (h := (dock r).outputWidth)
          (Push.Scan.ofQuotas (nextQuotas r (rowQuotas r requests)))) A
        ((G.map (sourceEmbedding r)).map (turnEmbedding (dock r).outputWidth (dock r).outputHeight))) hh) hnext
    · change @WholeBlocks.Exec (dock r).outputHeight (dock r).outputWidth (nextRounds r rest)
        ((G.map (sourceEmbedding r)).map (turnEmbedding (dock r).outputWidth (dock r).outputHeight))
        ((F.map (sourceEmbedding r)).map (turnEmbedding (dock r).outputWidth (dock r).outputHeight))
      simpa only [nextRounds, List.map_map, Function.comp_def] using hturned

theorem next_language_iff :
    Language (nextInput r (rowQuotas r requests) (rowQuotas_length r requests) hb) (nextRounds r rest) ↔
      Language r (.read .west requests :: rest) :=
  ⟨next_language_sound r requests hb rest hbound, next_language_complete r requests hb rest hbound⟩

end PushPuzzle.PushPush.CyclicReader
