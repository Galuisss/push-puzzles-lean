/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.PartnerCutsRepair
public import PushS.CombCore
public import PushS.PortWalkBudget
import all PushS.PortWalkBudget
import all PushS.PortSignalLocality

/-! Nonempty actual contour sources contain a core gate, and every partner repair retains one. -/

public section
namespace PushPuzzle.Push.Partner

open PushS

private theorem ear_gate_exists {l : PortLayout} (cut : ℕ) (ab : ℕ × ℕ)
    (gate : ∃ kind first, LowerGroup.gate kind first ∈ l.lowerGroups) :
    ∃ kind first, LowerGroup.gate kind first ∈ (ear l cut ab).lowerGroups := by
  obtain ⟨kind, first, hg⟩ := gate
  exact ⟨kind, shift cut first, mapGroup_mem_ear hg⟩

private theorem bufferAt_gate_exists (s : BufferState) (position : ℕ)
    (gate : ∃ kind first, LowerGroup.gate kind first ∈ s.layout.lowerGroups) :
    ∃ kind first, LowerGroup.gate kind first ∈ (s.bufferAt position).layout.lowerGroups := by
  unfold BufferState.bufferAt
  split_ifs
  · exact ear_gate_exists _ _ gate
  · exact ear_gate_exists _ _ gate
  · exact gate
  · exact gate

private theorem bufferScan_gate_exists (positions : List ℕ) (s : BufferState)
    (gate : ∃ kind first, LowerGroup.gate kind first ∈ s.layout.lowerGroups) :
    ∃ kind first, LowerGroup.gate kind first ∈ (s.scan positions).layout.lowerGroups := by
  induction positions generalizing s with
  | nil => exact gate
  | cons first rest ih => exact ih (s.bufferAt first) (bufferAt_gate_exists s first gate)

private theorem cutAt_gate_exists (s : BufferState) (cut : ℕ)
    (gate : ∃ kind first, LowerGroup.gate kind first ∈ s.layout.lowerGroups) :
    ∃ kind first, LowerGroup.gate kind first ∈ (Cuts.cutAt s cut).layout.lowerGroups := by
  unfold Cuts.cutAt
  split_ifs
  · obtain ⟨kind, first, hg⟩ := gate
    exact ⟨kind, Cuts.shift cut (Cuts.active s.layout cut).length first,
      List.mem_append_left _ (List.mem_map.mpr ⟨.gate kind first, hg, rfl⟩)⟩
  · exact gate

private theorem cutScan_gate_exists (positions : List ℕ) (s : BufferState)
    (gate : ∃ kind first, LowerGroup.gate kind first ∈ s.layout.lowerGroups) :
    ∃ kind first, LowerGroup.gate kind first ∈ (Cuts.scan s positions).layout.lowerGroups := by
  induction positions generalizing s with
  | nil => exact gate
  | cons cut rest ih => exact ih (Cuts.cutAt s cut) (cutAt_gate_exists s cut gate)

/-- The complete actual partner repair retains every source's nonempty gate inventory. -/
theorem Cuts.repair_gate_exists (l : PortLayout)
    (gate : ∃ kind first, LowerGroup.gate kind first ∈ l.lowerGroups) :
    ∃ kind first, LowerGroup.gate kind first ∈ (repair l).layout.lowerGroups := by
  exact cutScan_gate_exists _ _ (bufferScan_gate_exists _ (BufferState.start l) gate)

/-- A nonempty actual native contour contains the lower triple of one of its original core blocks. -/
theorem compile_gate_exists_of_portCount_pos (width : ℕ) (input : Comb.Input)
    (nonempty : 0 < (Comb.compile width input).portCount) :
    ∃ kind first, LowerGroup.gate kind first ∈ (Comb.compile width input).lowerGroups := by
  let blocks := (Comb.vertexOrder width input.drawing).map fun sv => Comb.vertexBlock width input sv.2
  have hp : 0 < (blocks.flatMap Comb.Block.order).length := nonempty
  obtain ⟨token, htoken⟩ := List.exists_mem_of_ne_nil _ (List.ne_nil_of_length_pos hp)
  obtain ⟨b, hb, _⟩ := List.mem_flatMap.mp htoken
  obtain ⟨sv, hsv, rfl⟩ := List.mem_map.mp hb
  obtain ⟨left, middle, right, _, hg⟩ := Comb.vertexBlock_core_group width input sv.2
  have hglobal : Comb.TokenGroup.gate (Comb.vertexBlock width input sv.2).core.kind left middle right ∈
      (Comb.cut width input).lower :=
    List.mem_flatMap.mpr ⟨_, List.mem_map.mpr ⟨sv, hsv, rfl⟩, hg⟩
  exact ⟨_, (Comb.cut width input).rank left, List.mem_map.mpr ⟨_, hglobal, rfl⟩⟩

/-- One actual lower gate gives a nonempty actual list of middle-axis coordinates. -/
theorem gateCenterCoordinates_ne_nil {l : PortLayout}
    (gate : ∃ kind first, LowerGroup.gate kind first ∈ l.lowerGroups) : l.gateCenterCoordinates ≠ [] := by
  obtain ⟨kind, first, hg⟩ := gate
  intro empty
  have hm : first + 1 ∈ l.gateCenterCoordinates := by
    simpa only [PortLayout.gateCenterCoordinates] using PortLayout.center_of_gate l hg
  rw [empty] at hm
  exact List.not_mem_nil hm

end PushPuzzle.Push.Partner
