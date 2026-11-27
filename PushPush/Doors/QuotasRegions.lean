/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.Quotas
public import PushPush.Doors.ProtectedRows
public import PushPush.Doors.MachineState

/-! The first six exact coordinate fronts leave every door register slot untouched. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Layout

open PushFS (Cell Direction)
open Push.AcceptanceProgram

theorem quotaPrefix_region (L : Layout) :
    allRegions (w := L.width) (h := L.height) (L.quotaTemplates.take 6) =
      readRegion .south [(0, L.height), (L.width - 1, L.height)] ∪
        readRegion .west [(0, L.width), (L.height - 1, L.width)] ∪
        readRegion .east L.probeRequests ∪
        readRegion .west (L.dividerNeighbors.map fun y => (y, L.rackX)) := by
  simp only [quotaTemplates, List.take_succ_cons, List.take_zero, allRegions,
    Template.region, readRegion, Finset.union_empty, Finset.empty_union, Finset.union_assoc]

private theorem working_not_probe (L : Layout) (p : Cell L.width L.height)
    (hx : p.1.val = L.rackX - 1) : p ∉ readRegion .east L.probeRequests := by
  intro hp
  obtain ⟨⟨row, span⟩, hr, _, hs⟩ := (mem_readRegion _ _ p).mp hp
  simp only [probeRequests, List.mem_append, List.mem_map] at hr
  rcases hr with ⟨y, _, he⟩ | ⟨y, _, he⟩
  · have he := congrArg Prod.snd he
    dsimp at he
    simp only [prefixRank] at hs
    unfold width rackX at hx he hs
    omega
  · have he := congrArg Prod.snd he
    dsimp at he
    simp only [prefixRank] at hs
    unfold width rackX at hx he hs
    omega

end Layout

namespace Source

open PushFS (Cell Direction)
open Push.AcceptanceProgram

theorem register_not_quotaPrefix (I : Instance) (i : Fin I.doors.length) (value : Register)
    (p : Cell (layout false I).width (layout false I).height)
    (hx : p.1.val = (layout false I).rackX - 1)
    (hy : p.2.val = doorBase i.val + value.row + (layout false I).shift) :
    p ∉ allRegions ((layout false I).quotaTemplates.take 6) := by
  have hrow := Register.row_bounds value
  have hbase := door_row_before I i.isLt (by omega : value.row < 90)
  have hpos := (layout false I).translated_bounds
    (doorRow_fit false I i.isLt (by omega : value.row < 90))
  have hborderSouth : p ∉ readRegion .south [(0, (layout false I).height),
      ((layout false I).width - 1, (layout false I).height)] := by
    intro hp
    obtain ⟨⟨row, span⟩, hr, hl, _⟩ := (mem_readRegion _ _ p).mp hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with he | he <;> cases he <;> simp only [Direction.lane] at hl <;>
      unfold Layout.width Layout.rackX at hx hl <;> omega
  have hborderWest : p ∉ readRegion .west [(0, (layout false I).width),
      ((layout false I).height - 1, (layout false I).width)] := by
    intro hp
    obtain ⟨⟨row, span⟩, hr, hl, _⟩ := (mem_readRegion _ _ p).mp hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with he | he <;> cases he <;> simp only [Direction.lane] at hl <;> omega
  have hneighbors : p ∉ readRegion .west ((layout false I).dividerNeighbors.map
      fun y => (y, (layout false I).rackX)) := by
    intro hp
    obtain ⟨⟨row, span⟩, hr, hl, _⟩ := (mem_readRegion _ _ p).mp hp
    obtain ⟨y, hy', he⟩ := List.mem_map.mp hr
    obtain ⟨g, hg, hy'⟩ := List.mem_flatMap.mp hy'
    have he := congrArg Prod.fst he
    simp only [Direction.lane] at hl
    dsimp at he
    have hgap := door_row_divider_gap false I i.isLt (by omega : 2 ≤ value.row)
      (by omega : value.row + 2 ≤ 90) hg
    have hshift := Layout.shift_ge (layout false I)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy'
    rcases hy' with hy' | hy' <;> omega
  intro hp
  rw [(layout false I).quotaPrefix_region] at hp
  rcases Finset.mem_union.mp hp with hp | hp
  · rcases Finset.mem_union.mp hp with hp | hp
    · rcases Finset.mem_union.mp hp with hp | hp
      · exact hborderSouth hp
      · exact hborderWest hp
    · exact (layout false I).working_not_probe p hx hp
  · exact hneighbors hp

end Source
end PushPuzzle.PushPush.Doors
