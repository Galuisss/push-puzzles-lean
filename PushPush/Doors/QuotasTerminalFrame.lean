/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.QuotasTerminalNeighbors
public import PushPush.Doors.ReaderSoundness

/-! Rack, marker and forbidden-neighbour readouts assemble the exact protected terminal frame. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell Direction Adjacent)

theorem restoredFrame_of_probes {storage : Bool} {I : Instance}
    {final : PushFS.State (layout storage I).width (layout storage I).height}
    (hactual : Reachable (puzzle storage I).initial final) (hinterior : Interior final)
    (hrack : ∀ p : Cell (layout storage I).width (layout storage I).height,
      (p.1.val, p.2.val) ∈ (layout storage I).rack → p ∈ final.boxes)
    (hmarker : ∀ p : Cell (layout storage I).width (layout storage I).height,
      p.1.val = (layout storage I).rackX - 1 → p.2.val ∈ (layout storage I).markerRows → p ∈ final.boxes)
    (hneighbor : ∀ p : Cell (layout storage I).width (layout storage I).height,
      p.1.val = (layout storage I).rackX - 1 → p.2.val ∈ (layout storage I).dividerNeighbors → p ∉ final.boxes) :
    RestoredFrame storage I final := by
  refine ⟨hinterior, ?_, ?_, ?_⟩
  · have hsub : line .south (layout storage I).rackX (puzzle storage I).initial.boxes ⊆
        line .south (layout storage I).rackX final.boxes := by
      intro z hz
      obtain ⟨p, hp, hx, he⟩ := mem_line.mp hz
      apply mem_line.mpr
      refine ⟨p, ?_, hx, he⟩
      apply hrack p
      have hp := ((layout storage I).mem_raster _ _).mp hp
      change (p.1.val, p.2.val) ∈ (layout storage I).initialRaw at hp
      change p.1.val = (layout storage I).rackX at hx
      rw [hx] at hp ⊢
      exact ((layout storage I).initialRaw_rack_iff _).mp hp
    exact (Finset.eq_of_subset_of_card_le hsub
      (hactual.rack_card_le (initial_supported storage I) hinterior)).symm
  · intro g hg p hx hy
    constructor
    · apply hmarker p hx
      apply List.mem_map.mpr
      exact ⟨g, List.mem_append_left _ (List.mem_append_left _ hg), hy.symm⟩
    · intro q hq hqb
      have hqx : q.1.val = (layout storage I).rackX - 1 := by
        rcases hq with hq | hq <;> exact (congrArg Fin.val hq.1).trans hx
      apply hneighbor q hqx ?_ hqb
      apply List.mem_flatMap.mpr
      refine ⟨g, hg, ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rcases hq with hq | hq
      · apply Or.inl
        have ha := hq.2
        omega
      · apply Or.inr
        have ha := hq.2
        omega
  · intro y hy p hx hpy
    apply hmarker p hx
    apply List.mem_map.mpr
    exact ⟨y, List.mem_append_left _ (List.mem_append_right _ hy), hpy.symm⟩

end PushPuzzle.PushPush.Doors.Source
