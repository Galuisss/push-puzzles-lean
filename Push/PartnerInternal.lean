/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.PartnerPaths
public import Push.PartnerInventory

/-! A finite descending scan buffers actual upper pairs inside lower gate triples. -/

@[expose] public section
namespace PushPuzzle.Push.Partner

open PushS

/-- The evolving layout and the current positions of every original port. -/
structure BufferState where
  layout : PortLayout
  ports : List ℕ

namespace BufferState

def start (l : PortLayout) : BufferState := ⟨l, List.range l.portCount⟩

def port (s : BufferState) (i : ℕ) : ℕ := s.ports.getD i 0

private theorem start_port (l : PortLayout) {i : ℕ} (hi : i < l.portCount) :
    (start l).port i = i := by
  simp only [start, port]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_range] using hi)]
  exact List.getElem_range _

def insertEar (s : BufferState) (cut : ℕ) (ab : ℕ × ℕ) : BufferState :=
  ⟨ear s.layout cut ab, s.ports.map (shift cut)⟩

private theorem insertEar_port (s : BufferState) (cut : ℕ) (ab : ℕ × ℕ) {i : ℕ}
    (hi : i < s.ports.length) : (s.insertEar cut ab).port i = shift cut (s.port i) := by
  simp only [insertEar, port]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map] using hi),
    List.getD_eq_getElem _ _ hi, List.getElem_map]

private theorem insertEar_connected_iff (s : BufferState) (cut : ℕ) (ab : ℕ × ℕ)
    (hab : ab ∈ s.layout.upperPairs) {i j : ℕ} (hi : i < s.ports.length) (hj : j < s.ports.length) :
    WireConnected (s.insertEar cut ab).layout (s.insertEar cut ab |>.port i)
      (s.insertEar cut ab |>.port j) ↔ WireConnected s.layout (s.port i) (s.port j) := by
  rw [insertEar_port _ _ _ hi, insertEar_port _ _ _ hj]
  exact ear_connected_iff hab _ _

/-- Test whether a lower gate starts at the current numerical port. -/
def gateTest (l : PortLayout) (first : ℕ) : Bool :=
  l.lowerGroups.any (fun g => match g with
    | .gate _ a => decide (a = first)
    | .wire .. => false)

/-- The current source triple is inspected before choosing its left or reflected right ear. -/
def bufferAt (s : BufferState) (first : ℕ) : BufferState :=
  if gateTest s.layout first then
    if (first, first + 1) ∈ s.layout.upperPairs then
      s.insertEar first (first, first + 1)
    else if (first + 1, first + 2) ∈ s.layout.upperPairs then
      s.insertEar (first + 3) (first + 1, first + 2)
    else s
  else s

private theorem bufferAt_length (s : BufferState) (first : ℕ) :
    (s.bufferAt first).ports.length = s.ports.length := by
  unfold bufferAt
  split_ifs <;> simp only [insertEar, List.length_map]

private theorem bufferAt_count (s : BufferState) (first : ℕ) :
    (s.bufferAt first).layout.portCount ≤ s.layout.portCount + 2 := by
  unfold bufferAt
  split_ifs <;> (try dsimp only [insertEar, ear]) <;> omega

private theorem bufferAt_connected_iff (s : BufferState) (first : ℕ) {i j : ℕ}
    (hi : i < s.ports.length) (hj : j < s.ports.length) :
    WireConnected (s.bufferAt first).layout ((s.bufferAt first).port i)
      ((s.bufferAt first).port j) ↔ WireConnected s.layout (s.port i) (s.port j) := by
  unfold bufferAt
  split_ifs with hg hl hr
  · exact s.insertEar_connected_iff _ _ hl hi hj
  · exact s.insertEar_connected_iff _ _ hr hi hj
  all_goals rfl

private theorem gate_of_any {s : BufferState} {first : ℕ}
    (hg : s.layout.lowerGroups.any (fun g => match g with
      | .gate _ a => decide (a = first)
      | .wire .. => false) = true) :
    ∃ kind, LowerGroup.gate kind first ∈ s.layout.lowerGroups := by
  obtain ⟨g, hmem, he⟩ := List.any_eq_true.mp hg
  cases g with
  | wire a b => cases he
  | gate kind a =>
    have ha : a = first := of_decide_eq_true he
    exact ⟨kind, ha ▸ hmem⟩

/-- Each inspected actual gate preserves the complete finite partition on both pages. -/
theorem bufferAt_inventory (s : BufferState) (first : ℕ) (hs : PortInventory s.layout) :
    PortInventory (s.bufferAt first).layout := by
  unfold bufferAt
  split_ifs with hg hl hr
  · obtain ⟨kind, hgate⟩ := gate_of_any hg
    have hc := inventory_gate_bound hs hgate
    exact ear_inventory hs first _ (by omega) (inventory_gate_boundary_safe hs hgate).1 hl
  · obtain ⟨kind, hgate⟩ := gate_of_any hg
    exact ear_inventory hs (first + 3) _ (inventory_gate_bound hs hgate)
      (inventory_gate_boundary_safe hs hgate).2 hr
  all_goals exact hs

/-- Perform a prescribed finite sequence of gate inspections. -/
def scan (s : BufferState) (positions : List ℕ) : BufferState := positions.foldl bufferAt s

theorem scan_length (s : BufferState) (positions : List ℕ) :
    (s.scan positions).ports.length = s.ports.length := by
  induction positions generalizing s with
  | nil => rfl
  | cons first rest ih =>
    exact (ih (s.bufferAt first)).trans (s.bufferAt_length first)

private theorem scan_count (s : BufferState) (positions : List ℕ) :
    (s.scan positions).layout.portCount ≤ s.layout.portCount + 2 * positions.length := by
  induction positions generalizing s with
  | nil => simp only [scan, List.foldl_nil, List.length_nil, Nat.mul_zero, Nat.add_zero, le_refl]
  | cons first rest ih =>
    have h := ih (s.bufferAt first)
    have hc := s.bufferAt_count first
    change (s.bufferAt first |>.scan rest).layout.portCount ≤ _
    simp only [List.length_cons]
    omega

/-- The finite scan preserves all original port-pair connectivity on its literal emitted layout. -/
private theorem scan_connected_iff (s : BufferState) (positions : List ℕ) {i j : ℕ}
    (hi : i < s.ports.length) (hj : j < s.ports.length) :
    WireConnected (s.scan positions).layout ((s.scan positions).port i)
      ((s.scan positions).port j) ↔ WireConnected s.layout (s.port i) (s.port j) := by
  induction positions generalizing s with
  | nil => rfl
  | cons first rest ih =>
    have hi' : i < (s.bufferAt first).ports.length := by rwa [bufferAt_length]
    have hj' : j < (s.bufferAt first).ports.length := by rwa [bufferAt_length]
    exact (ih (s.bufferAt first) hi' hj').trans (s.bufferAt_connected_iff first hi hj)

end BufferState

/-- Inspect original gate locations from right to left, so later insertions preserve earlier locations. -/
def bufferInternal (l : PortLayout) : BufferState :=
  (BufferState.start l).scan (List.range l.portCount).reverse

theorem bufferInternal_length (l : PortLayout) : (bufferInternal l).ports.length = l.portCount := by
  rw [bufferInternal, BufferState.scan_length]
  exact List.length_range

/-- The total ear stage uses at most two fresh ports per original inspected position. -/
theorem bufferInternal_count (l : PortLayout) : (bufferInternal l).layout.portCount ≤ 3 * l.portCount := by
  have h := (BufferState.start l).scan_count (List.range l.portCount).reverse
  simp only [List.length_reverse, List.length_range, BufferState.start] at h
  change (bufferInternal l).layout.portCount ≤ _ at h
  omega

/-- Every pair of original incidence names keeps exactly the same WIRE connectivity. -/
theorem bufferInternal_connected_iff (l : PortLayout) {i j : ℕ}
    (hi : i < l.portCount) (hj : j < l.portCount) :
    WireConnected (bufferInternal l).layout ((bufferInternal l).port i) ((bufferInternal l).port j) ↔
      WireConnected l i j := by
  have hi' : i < (BufferState.start l).ports.length := by simpa only [BufferState.start, List.length_range] using hi
  have hj' : j < (BufferState.start l).ports.length := by simpa only [BufferState.start, List.length_range] using hj
  have h := (BufferState.start l).scan_connected_iff (List.range l.portCount).reverse hi' hj'
  rw [BufferState.start_port l hi, BufferState.start_port l hj] at h
  exact h

end PushPuzzle.Push.Partner
