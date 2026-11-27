/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.QuotasNeighborWitness
public import PushPush.Doors.PrivateColumnInventory

/-! The final north round restores the exact original box count in every private column. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell Direction)
open Push.AcceptanceProgram WholeScan

def finalStart (I : Instance) : Finset (Cell (layout false I).width (layout false I).height) :=
  (Push.AcceptanceProgram.emit ((layout false I).quotaTemplates.take 6)
    (layout false I).referenceHoles).remaining

def finalQuotas (I : Instance) : List (ℕ × ℕ) :=
  (emitReads .north (layout false I).finalRequests (finalStart I)).quotas

private theorem readerRounds_final (I : Instance) :
    (readerRounds I).drop 6 = [.read .north (finalQuotas I)] := rfl

private theorem final_quotaAt (I : Instance) (x : Fin (layout false I).width) :
    Push.Scan.quotaAt (finalQuotas I) x.val =
      ((finalStart I).filter fun p => p.1.val = x.val).card := by
  rw [finalQuotas, emitReads_lane_quota .north (layout false I).finalRequests (finalStart I) x.val (layout false I).height
    (List.mem_map.mpr ⟨x.val, List.mem_range.mpr x.isLt, rfl⟩) (by
      intro request hr _
      obtain ⟨y, _, rfl⟩ := List.mem_map.mp hr
      rfl)]
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro p _
  rw [mem_line_prefix]
  simp only [Direction.lane, prefixRank]
  exact ⟨And.left, fun hp => ⟨hp, p.2.isLt⟩⟩

private theorem prefix_region (I : Instance) :
    allRegions (w := (layout false I).width) (h := (layout false I).height)
      ((layout false I).quotaTemplates.take 6) =
      frameCells I ∪ readRegion .east (layout false I).probeRequests ∪
        readRegion .west ((layout false I).dividerNeighbors.map fun row => (row, (layout false I).rackX)) := by
  have hframe : readRegion (w := (layout false I).width) (h := (layout false I).height) .south
      [(0, (layout false I).height), ((layout false I).width - 1, (layout false I).height)] ∪
      readRegion .west [(0, (layout false I).width), ((layout false I).height - 1, (layout false I).width)] =
      frameCells I := by
    have hh : allRegions (w := (layout false I).width) (h := (layout false I).height)
        ((layout false I).quotaTemplates.take 3) = frameCells I := by
      ext p
      simpa only [frameCells, Finset.mem_filter, Finset.mem_univ, true_and, Boundary] using frame_region I p
    have hstages : (layout false I).quotaTemplates.take 3 =
        [.read .south [(0, (layout false I).height), ((layout false I).width - 1, (layout false I).height)],
          .read .west [(0, (layout false I).width), ((layout false I).height - 1, (layout false I).width)],
          .read .north []] := rfl
    rw [hstages] at hh
    simpa only [allRegions, Template.region,
      show readRegion (w := (layout false I).width) (h := (layout false I).height) .north [] = ∅ from rfl,
      Finset.union_empty] using hh
  rw [(layout false I).quotaPrefix_region, hframe]

private theorem NeighborWitness.after_eq {I : Instance}
    {final : PushFS.State (layout false I).width (layout false I).height}
    {G : Finset (Cell (layout false I).width (layout false I).height)}
    (W : NeighborWitness I final.boxesᶜ G)
    (hsupport : Supported .east (layout false I).rackX final)
    (hrack : line .south (layout false I).rackX final.boxes =
      line .south (layout false I).rackX (puzzle false I).initial.boxes) :
    W.after = final.boxesᶜ \ allRegions ((layout false I).quotaTemplates.take 6) := by
  have hcapacity : ∀ {row : ℕ}, row ∈ (layout false I).dividerNeighbors →
      ∀ p ∈ W.probe.after, p.2.val = row → 0 < p.1.val ∧ p.1.val < (layout false I).rackX := by
    intro row hrow p hp hy
    exact W.probe.neighbor_capacity hsupport hrack hrow p hp hy
  have hag : ∀ p ∈ readRegion .west ((layout false I).dividerNeighbors.map
      fun row => (row, (layout false I).rackX)), p ∈ W.probe.after ↔ p ∈ neighborStart I := by
    intro p hp
    obtain ⟨request, hr, hy, hx⟩ := (mem_readRegion _ _ p).mp hp
    obtain ⟨row, hrow, he⟩ := List.mem_map.mp hr
    cases he
    change p.2.val = row at hy
    change p.1.val < (layout false I).rackX at hx
    rw [neighborStart_prefix I p (hy ▸ hrow) hx]
    constructor
    · intro hp
      exact (hcapacity hrow p hp hy).1
    · intro hp
      exact sixth_neighbor_full I hrow W.run (hcapacity hrow) p hy hp hx
  have hround := emit_rounds_agree [.read .west ((layout false I).dividerNeighbors.map
      fun row => (row, (layout false I).rackX))] W.probe.after (neighborStart I) (by
    intro p hp
    exact hag p (by simpa only [allRegions, Template.region, Finset.union_empty] using hp))
  have hquotas : (emitReads .west ((layout false I).dividerNeighbors.map
      fun row => (row, (layout false I).rackX)) W.probe.after).quotas = neighborQuotas I := by
    injection hround with hhead
    exact Round.read.inj hhead |>.2
  have he := emitReads_eval .west ((layout false I).dividerNeighbors.map
    fun row => (row, (layout false I).rackX)) W.probe.after
  rw [hquotas] at he
  have hafter := Option.some.inj (W.run.eval.symm.trans he)
  rw [hafter, emitReads_remaining, W.probe.after_eq hsupport hrack, prefix_region]
  ext p
  simp only [Finset.mem_sdiff, Finset.mem_union, not_or, and_assoc]

private theorem NeighborWitness.private_prefix_holes {I : Instance}
    {final : PushFS.State (layout false I).width (layout false I).height}
    {G : Finset (Cell (layout false I).width (layout false I).height)}
    (W : NeighborWitness I final.boxesᶜ G)
    (hframe : ∀ p, Boundary p → p ∈ final.boxesᶜ)
    (hsupport : Supported .east (layout false I).rackX final)
    (hrack : line .south (layout false I).rackX final.boxes =
      line .south (layout false I).rackX (puzzle false I).initial.boxes)
    (p : Cell (layout false I).width (layout false I).height)
    (hx : p.1.val < (layout false I).rackX - 1)
    (hp : p ∈ allRegions ((layout false I).quotaTemplates.take 6)) :
    p ∈ final.boxesᶜ ∧ p ∈ (layout false I).referenceHoles := by
  rw [prefix_region] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · rcases Finset.mem_union.mp hp with hp | hp
    · have hb : Boundary p := (Finset.mem_filter.mp hp).2
      exact ⟨hframe p hb, reference_boundary I p hb⟩
    · obtain ⟨request, hr, _, hpos⟩ := (mem_readRegion _ _ p).mp hp
      simp only [Layout.probeRequests, List.mem_append, List.mem_map] at hr
      rcases hr with ⟨row, _, rfl⟩ | ⟨row, _, rfl⟩ <;>
        simp only [prefixRank] at hpos <;> unfold Layout.width at hpos <;> omega
  · obtain ⟨request, hr, hy, hpos⟩ := (mem_readRegion _ _ p).mp hp
    obtain ⟨row, hrow, he⟩ := List.mem_map.mp hr
    cases he
    change p.2.val = row at hy
    change p.1.val < (layout false I).rackX at hpos
    have hreference : p ∈ (layout false I).referenceHoles := Finset.mem_compl.mpr
      (fun hb => neighbor_prefix_goal_empty false I hpos (hy ▸ hrow)
        (((layout false I).mem_raster _ _).mp hb))
    by_cases hpx : p.1.val = 0
    · exact ⟨hframe p (Or.inl hpx), hreference⟩
    · have hbefore := sixth_neighbor_full I hrow W.run
        (W.probe.neighbor_capacity hsupport hrack hrow) p hy (by omega) hpos
      exact ⟨(W.probe.run.subset.trans Finset.sdiff_subset) hbefore, hreference⟩

private theorem column_card_of_remainder {w h x : ℕ} (E F R : Finset (Cell w h))
    (hrest : ((E \ R).filter fun p => p.1.val = x).card =
      ((F \ R).filter fun p => p.1.val = x).card)
    (hag : ∀ p ∈ R, p.1.val = x → (p ∈ E ↔ p ∈ F)) :
    (E.filter fun p => p.1.val = x).card = (F.filter fun p => p.1.val = x).card := by
  let left := E.filter fun p => p.1.val = x
  let right := F.filter fun p => p.1.val = x
  have hdel : left.filter (fun p => p ∈ R) = right.filter fun p => p ∈ R := by
    ext p
    simp only [left, right, Finset.mem_filter]
    by_cases hr : p ∈ R
    · by_cases hx : p.1.val = x
      · simp only [hr, hx, and_true]
        exact hag p hr hx
      · simp only [hx, and_false, false_and]
    · simp only [hr, and_false]
  have hl : left.filter (fun p => p ∉ R) = (E \ R).filter fun p => p.1.val = x := by
    ext p
    simp only [left, Finset.mem_filter, Finset.mem_sdiff]
    exact ⟨fun ⟨⟨hp, hx⟩, hr⟩ => ⟨⟨hp, hr⟩, hx⟩, fun ⟨⟨hp, hr⟩, hx⟩ => ⟨⟨hp, hx⟩, hr⟩⟩
  have hr : right.filter (fun p => p ∉ R) = (F \ R).filter fun p => p.1.val = x := by
    ext p
    simp only [right, Finset.mem_filter, Finset.mem_sdiff]
    exact ⟨fun ⟨⟨hp, hx⟩, hr⟩ => ⟨⟨hp, hr⟩, hx⟩, fun ⟨⟨hp, hr⟩, hx⟩ => ⟨⟨hp, hx⟩, hr⟩⟩
  have hleft := Finset.card_filter_add_card_filter_not (s := left) (fun p => p ∈ R)
  have hright := Finset.card_filter_add_card_filter_not (s := right) (fun p => p ∈ R)
  rw [hdel, hl] at hleft
  rw [hr] at hright
  change left.card = right.card
  omega

private theorem column_compl_card {w h x : ℕ} (boxes : Finset (Cell w h)) :
    (boxes.filter fun p => p.1.val = x).card +
      (boxesᶜ.filter fun p => p.1.val = x).card =
      (Finset.univ.filter fun p : Cell w h => p.1.val = x).card := by
  have hh := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun p : Cell w h => p.1.val = x) (fun p => p ∈ boxes)
  have hb : ((Finset.univ.filter fun p : Cell w h => p.1.val = x).filter fun p => p ∈ boxes) =
      boxes.filter fun p => p.1.val = x := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_comm]
  have he : ((Finset.univ.filter fun p : Cell w h => p.1.val = x).filter fun p => p ∉ boxes) =
      boxesᶜ.filter fun p => p.1.val = x := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl, and_comm]
  rwa [hb, he] at hh

theorem NeighborWitness.private_columns {I : Instance}
    {final : PushFS.State (layout false I).width (layout false I).height}
    {G : Finset (Cell (layout false I).width (layout false I).height)}
    (W : NeighborWitness I final.boxesᶜ G)
    (hframe : ∀ p, Boundary p → p ∈ final.boxesᶜ)
    (hsupport : Supported .east (layout false I).rackX final)
    (hrack : line .south (layout false I).rackX final.boxes =
      line .south (layout false I).rackX (puzzle false I).initial.boxes)
    (hG : G = ∅) : PrivateColumnInventory false I final.boxes := by
  constructor
  intro x hx
  have hxw : x < (layout false I).width := by unfold Layout.width; omega
  have hlast := W.finish
  rw [readerRounds_final] at hlast
  simp only [instructions, List.flatMap_cons, List.flatMap_nil, Round.instructions, List.append_nil] at hlast
  have hread := hlast.parallel_read .north (finalQuotas I) x
  have hcard := hread.card
  rw [final_quotaAt I ⟨x, hxw⟩] at hcard
  simp only [hG, Finset.filter_empty, Finset.card_empty, Nat.zero_add] at hcard
  have hrest : ((final.boxesᶜ \ allRegions ((layout false I).quotaTemplates.take 6)).filter
      fun p => p.1.val = x).card =
      (((layout false I).referenceHoles \ allRegions ((layout false I).quotaTemplates.take 6)).filter
        fun p => p.1.val = x).card := by
    rw [← W.after_eq hsupport hrack]
    have hc : ((finalStart I).filter fun p => p.1.val = x).card =
        (W.after.filter fun p => p.1.val = x).card := by
      convert hcard using 1
      apply congrArg Finset.card
      apply Finset.filter_congr
      intro p _
      rfl
    rw [finalStart, emit_remaining] at hc
    exact hc.symm
  have hholes := column_card_of_remainder final.boxesᶜ (layout false I).referenceHoles
    (allRegions ((layout false I).quotaTemplates.take 6)) hrest (by
      intro p hp hpx
      have hh := W.private_prefix_holes hframe hsupport hrack p (by omega) hp
      exact iff_of_true hh.1 hh.2)
  have htotal := column_compl_card (x := x) final.boxes
  have href := column_compl_card (x := x) ((layout false I).raster (layout false I).goalsRaw)
  have hboxes : columnCount final.boxes x =
      columnCount ((layout false I).raster (layout false I).goalsRaw) x := by
    unfold Layout.referenceHoles at hholes
    unfold columnCount
    omega
  rw [hboxes]
  apply congrArg Finset.card
  ext p
  simp only [Finset.mem_filter, Layout.mem_raster]
  by_cases hp : p.1.val = x
  · simp only [hp, and_true]
    constructor
    · intro hgoal
      have hbox : p ∈ (puzzle false I).board.goals := ((layout false I).mem_raster _ _).mpr
        (by simpa only [hp] using hgoal)
      simpa only [hp] using (TerminalInventory.goals false I).private_pin p hbox (by omega)
    · exact fun hpin => Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hpin))
  · simp only [hp, and_false]

end PushPuzzle.PushPush.Doors.Source
