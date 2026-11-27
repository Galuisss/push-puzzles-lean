/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.CyclicCommit
public import PushPush.WholeColumns

/-! Complete original hole runs survive the entire physical maximum-sliding dock suffix. -/

@[expose] public section
namespace PushPuzzle.PushPush.Cyclic

open PushFS (Cell State Direction Adjacent)
open Push.Cyclic

variable {r : Push.ColumnScan.Input}
  {finish : State (dock r).outputWidth (dock r).outputHeight} (c : Commit r finish)

private theorem embed_north (p q : Cell r.width r.height) (ha : Adjacent .north p q) :
    Adjacent .north (unturnedSourceEmbed r p) (unturnedSourceEmbed r q) := by
  constructor
  · apply Fin.ext
    change q.1.val + 2 = p.1.val + 2
    have := congrArg Fin.val ha.1
    omega
  · exact ha.2

private theorem original_subset {s t : State (dock r).outputWidth (dock r).outputHeight}
    (hcs : PushFS.Reachable (dock r).compile.board none c.trace.state s)
    (hst : Reachable s t) : originalHoles r t ⊆ originalHoles r s := by
  intro p hp
  have hphys := (mem_originalHoles r t p).mp hp
  have hh := c.trace.source_between_subset hcs
    (hst.unit_expansion (dock r).compile.board rfl)
    (Finset.mem_filter.mpr ⟨hphys, by
      change p.1.val + 2 < r.width + 2
      have := p.1.isLt
      omega, p.2.isLt⟩)
  exact (mem_originalHoles r s p).mpr (Finset.mem_filter.mp hh).1

private theorem move_original_no_split {s t : State (dock r).outputWidth (dock r).outputHeight}
    {d : Direction} (hm : Move d s t) (hbelow : r.height ≤ s.player.2.val) :
    ColumnReader.NoNorthSplit (originalHoles r s) (originalHoles r t) := by
  cases hm with
  | walk _ _ _ hb => simp [ColumnReader.NoNorthSplit, originalHoles, PushS.holes, hb]
  | @push n k _ _ _ slide _ hb =>
    intro p hp q hq ha
    obtain ⟨hp, hpnot⟩ := Finset.mem_sdiff.mp hp
    have hpEmpty := (PushS.mem_holes _).mp ((mem_originalHoles r s p).mp hp)
    have hpBox : unturnedSourceEmbed r p ∈ t.boxes := by
      by_contra hn
      exact hpnot ((mem_originalHoles r t p).mpr ((PushS.mem_holes _).mpr hn))
    have hpAfter : unturnedSourceEmbed r p ∈ slide.after := by
      rw [hb] at hpBox
      rcases Finset.mem_union.mp hpBox with hstat | ha
      · exact False.elim (hpEmpty (Finset.mem_sdiff.mp hstat).1)
      · exact ha
    have hd : d = .north := by
      obtain ⟨i, _, he⟩ := Finset.mem_image.mp hpAfter
      have hy := slide.position ⟨k + i.val + 1, by omega⟩
      have hx := slide.lane ⟨k + i.val + 1, by omega⟩
      rw [he] at hy hx
      have hpy : (unturnedSourceEmbed r p).2.val < r.height := p.2.isLt
      dsimp only at hy
      cases d <;> simp only [Direction.position, Direction.lane] at hy hx <;> first | rfl | omega
    subst d
    exact (PushS.mem_holes _).mp ((mem_originalHoles r t q).mp hq)
      (by rw [hb]; exact slide.after_forward_full hpAfter (embed_north p q ha))

theorem Commit.whole_remainder : ColumnReader.WholeBottomRemainder
    (PushS.holes c.trace.sourceState) (originalHoles r finish) := by
  refine ⟨c.trace.original_remainder c.trace.suffix, ?_⟩
  have hpre : PushFS.Reachable (dock r).compile.board none c.trace.state c.trace.readerEnd :=
    Relation.ReflTransGen.mono (fun _ _ hm => hm.1) _ _ c.trace.untilGoal
  have extend {s t : State (dock r).outputWidth (dock r).outputHeight}
      (hcs : PushFS.Reachable (dock r).compile.board none c.trace.state s)
      (hr : Reachable s t) :
      ColumnReader.NoNorthSplit (originalHoles r s) (originalHoles r t) := by
    induction hr with
    | refl => exact .refl _
    | tail hsu hm ih =>
      have hnow := hcs.trans (Reachable.unit_expansion hsu (dock r).compile.board rfl)
      exact ih.trans (move_original_no_split hm.choose_spec (c.trace.below_source hnow))
        (original_subset c hnow (Relation.ReflTransGen.single hm))
  exact c.reader_whole.trans (extend hpre c.after) (original_subset c hpre c.after)

theorem Commit.loose_columns : WholeScan.LooseExec (Push.Scan.columns (Push.Scan.ofQuotas r.quotas))
    (PushS.holes c.trace.sourceState) (originalHoles r finish) := by
  have hw := c.whole_remainder
  refine WholeScan.loose_columns (Push.Scan.ofQuotas_nodup r.quotas) ?_
    hw.toBottomRemainder hw.no_split ?_
  · intro x
    let i : Fin r.quotas.length := ⟨x.val, r.quotas_width.symm ▸ x.isLt⟩
    exact ⟨r.quotas[i], Push.Scan.ofQuotas_mem r.quotas i⟩
  · intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    let j : Fin r.width := ⟨i.val, r.quotas_width ▸ i.isLt⟩
    have hq := c.trace.original_consumed_quotas j
    rw [List.getD_eq_getElem r.quotas 0 i.isLt] at hq
    simpa only [Fin.ext_iff, j, Fin.val_mk, Fin.getElem_fin] using hq

end PushPuzzle.PushPush.Cyclic
