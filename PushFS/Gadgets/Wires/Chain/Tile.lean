/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Straight
public import PushFS.Gadgets.Wires.Parity
public import PushFS.Gadgets.Wires.Interface
public import PushFS.Gadgets.Wires.Chain.Spans
public import PushFS.Gadgets.Wires.Chain.CoveredPlacement

/-! The exact finite physical interface used in arbitrary-length 40/59 chains. -/

@[expose] public section

namespace PushPuzzle.PushFS.Gadgets.Wires.Chain.Tile


set_option maxRecDepth 65536
set_option maxHeartbeats 0

def width (kind : Bool) : ℕ := if kind then 64 else 45
def count (kind : Bool) : ℕ := if kind then 26 else 18
abbrev C (kind : Bool) := Cell (width kind) 21
abbrev span := Spans.span

theorem width_eq (kind : Bool) : width kind = span kind + 5 := by cases kind <;> rfl

def walls : (kind : Bool) → Finset (C kind)
  | false => Straight.template.walls
  | true => Parity.template.walls

def reserved : (kind : Bool) → Finset (C kind)
  | false => Straight.template.reservedCells
  | true => Parity.template.reservedCells

def neighbors : (kind : Bool) → Finset (C kind)
  | false => Straight.neighbors
  | true => Parity.neighbors

def position : (kind : Bool) → Bool → Fin (count kind) → C kind
  | false => Straight.template.position
  | true => Parity.template.position

def hub : (kind : Bool) → C kind
  | false => Straight.hub
  | true => Parity.hub

def corner : (kind : Bool) → Fin 4 → C kind
  | false => Straight.corner
  | true => Parity.corner

def boxes (kind phase : Bool) : Finset (C kind) := Finset.univ.image (position kind phase)
def state (kind phase : Bool) : State (width kind) 21 := ⟨hub kind, boxes kind phase⟩

@[simp] theorem boxes_false (a : Bool) : boxes false a = Straight.template.boxes a := rfl
@[simp] theorem boxes_true (a : Bool) : boxes true a = Parity.template.boxes a := rfl
@[simp] theorem state_false (a : Bool) : state false a = Straight.template.state a := rfl
@[simp] theorem state_true (a : Bool) : state true a = Parity.template.state a := rfl

theorem position_injective (kind phase : Bool) : Function.Injective (position kind phase) := by
  cases kind
  · exact Straight.checked.injective phase
  · exact Parity.checked.injective phase

theorem position_bounds (kind phase : Bool) (i : Fin (count kind)) :
    (position kind phase i).2.val = 10 ∧ 2 ≤ (position kind phase i).1.val ∧
      (position kind phase i).1.val ≤ span kind + 1 := by
  have h : ∀ k p, ∀ i : Fin (count k), (position k p i).2.val = 10 ∧
      2 ≤ (position k p i).1.val ∧ (position k p i).1.val ≤ span k + 1 := by decide +kernel
  exact h kind phase i

theorem left_high (kind : Bool) (i : Fin (count kind))
    (hi : (position kind true i).1.val ≤ 4) : (position kind true i).1.val = 3 := by
  have h : ∀ k, ∀ i : Fin (count k), (position k true i).1.val ≤ 4 → (position k true i).1.val = 3 := by decide +kernel
  exact h kind i hi

theorem right_low (kind : Bool) (i : Fin (count kind))
    (hi : span kind ≤ (position kind false i).1.val) : (position kind false i).1.val = span kind := by
  have h : ∀ k, ∀ i : Fin (count k), span k ≤ (position k false i).1.val →
      (position k false i).1.val = span k := by decide +kernel
  exact h kind i hi

theorem boxes_floor (kind phase : Bool) : Disjoint (boxes kind phase) (walls kind) := by
  cases kind
  · exact Straight.checked.boxes_floor phase
  · exact Parity.checked.boxes_floor phase

private theorem boxes_reserved (kind phase : Bool) : boxes kind phase ⊆ reserved kind := by
  cases kind
  · exact Straight.checked.boxes_reserved phase
  · exact Parity.checked.boxes_reserved phase

theorem wall_rows (kind : Bool) (p : C kind) (hp : p ∈ walls kind) :
    p.2.val = 8 ∨ p.2.val = 9 ∨ p.2.val = 11 ∨ p.2.val = 12 := by
  have h : ∀ k, ∀ p : C k, p ∈ walls k →
      p.2.val = 8 ∨ p.2.val = 9 ∨ p.2.val = 11 ∨ p.2.val = 12 := by decide +kernel
  exact h kind p hp

/-- The five-column overlap has exactly the same lower guard wall at either end. -/
theorem collar_walls (kind : Bool) (p : C kind)
    (hp : p.1.val < 5 ∨ span kind ≤ p.1.val) :
    p ∈ walls kind ↔ p.2.val = 11 ∨ p.2.val = 12 := by
  have h : ∀ k, ∀ p : C k, p.1.val < 5 ∨ span k ≤ p.1.val →
      (p ∈ walls k ↔ p.2.val = 11 ∨ p.2.val = 12) := by decide +kernel
  exact h kind p hp

theorem mem_neighbors (kind : Bool) (p : C kind) :
    p ∈ neighbors kind ↔ p.2.val = 10 ∧ (p.1.val = 0 ∨ p.1.val = span kind + 3) := by
  have h : ∀ k, ∀ p : C k, p ∈ neighbors k ↔
      p.2.val = 10 ∧ (p.1.val = 0 ∨ p.1.val = span k + 3) := by decide +kernel
  exact h kind p

theorem mem_reserved (kind : Bool) (p : C kind) :
    p ∈ reserved kind ↔ p.2.val = 10 ∧ p.1.val ≠ 9 ∧ p.1.val ≠ 10 ∧ p.1.val ≠ 29 ∧ p.1.val ≠ 30 := by
  have h : ∀ k, ∀ p : C k, p ∈ reserved k ↔
      p.2.val = 10 ∧ p.1.val ≠ 9 ∧ p.1.val ≠ 10 ∧ p.1.val ≠ 29 ∧ p.1.val ≠ 30 := by decide +kernel
  exact h kind p

@[simp] theorem hub_x (kind : Bool) : (hub kind).1.val = 20 := by cases kind <;> rfl
@[simp] theorem hub_y (kind : Bool) : (hub kind).2.val = 3 := by cases kind <;> rfl


def template : (kind : Bool) → Template (width kind) 21 (count kind)
  | false => Straight.template
  | true => Parity.template

theorem checked (kind : Bool) : (template kind).Checked := by
  cases kind
  · exact Straight.checked
  · exact Parity.checked

@[simp] theorem template_position (kind phase : Bool) : (template kind).position phase = position kind phase := by
  cases kind <;> rfl
@[simp] theorem template_state (kind phase : Bool) : (template kind).state phase = state kind phase := by
  cases kind <;> rfl
@[simp] theorem template_walls (kind : Bool) : (template kind).walls = walls kind := by cases kind <;> rfl
@[simp] theorem template_neighbors (kind : Bool) : (template kind).neighbors = neighbors kind := by cases kind <;> rfl
@[simp] theorem template_reserved (kind : Bool) : (template kind).reservedCells = reserved kind := by cases kind <;> rfl
@[simp] theorem template_hub (kind : Bool) : (template kind).hub = hub kind := by cases kind <;> rfl
@[simp] theorem template_corner (kind : Bool) : (template kind).corner = corner kind := by cases kind <;> rfl
@[simp] theorem template_boxes (kind phase : Bool) : (template kind).boxes phase = boxes kind phase := by cases kind <;> rfl

theorem transition_placed {W H : ℕ} (kind a b : Bool) (fixed : Finset (C kind))
    (hf : fixed ⊆ neighbors kind) (e : GridEmbedding (width kind) 21 W H)
    {B : Board W H} {external : Finset (Cell W H)}
    (hwalls : ∀ p, e.cells p ∈ B.walls ↔ p ∈ walls kind)
    (hinside : ∀ p, e.cells p ∈ external → p ∈ fixed)
    (hfixed : ∀ p ∈ fixed, e.cells p ∈ external)
    (hfree : Disjoint external B.walls) :
    Reachable B (some 1) ((state kind a).place e external) ((state kind b).place e external) := by
  apply e.reachable_withFixed (sourceBoard := (template kind).board ∅) (by simpa [GridEmbedding.WallsAgree, Template.board] using hwalls) hinside hfixed hfree
  simpa using (checked kind).transition a b ∅ fixed (by simpa using hf)

/-- Both real corner walks survive arbitrary mixed collar boxes on reserved rails. -/
theorem corners_placed {W H : ℕ} (kind a : Bool) (i : Fin 4) (fixed : Finset (C kind))
    (hf : fixed ⊆ reserved kind) (hfw : Disjoint fixed (walls kind))
    (e : GridEmbedding (width kind) 21 W H) {B : Board W H} {external : Finset (Cell W H)}
    (hwalls : ∀ p, e.cells p ∈ B.walls ↔ p ∈ walls kind)
    (hinside : ∀ p, e.cells p ∈ external → p ∈ fixed)
    (hfixed : ∀ p ∈ fixed, e.cells p ∈ external)
    (hfree : Disjoint external B.walls) :
    Reachable B (some 1) ((state kind a).place e external)
      ((⟨corner kind i, boxes kind a⟩ : State (width kind) 21).place e external) ∧
    Reachable B (some 1) ((⟨corner kind i, boxes kind a⟩ : State (width kind) 21).place e external)
      ((state kind a).place e external) := by
  have ha : boxes kind a ∪ fixed ⊆ (template kind).reservedCells :=
    Finset.union_subset (by simpa using boxes_reserved kind a) (by simpa using hf)
  have haw : Disjoint (boxes kind a ∪ fixed) (template kind).walls := by
    simpa using Finset.disjoint_union_left.mpr ⟨boxes_floor kind a, hfw⟩
  have hfwd := (checked kind).corner_reachable i ∅ (boxes kind a ∪ fixed) ha haw
  have hbwd := (checked kind).corner_to_hub i ∅ (boxes kind a ∪ fixed) ha haw
  constructor
  · apply e.reachable_withFixed (sourceBoard := (template kind).board ∅) (by simpa [GridEmbedding.WallsAgree, Template.board] using hwalls) hinside hfixed hfree
    simpa [Gates.withFixed, state] using hfwd
  · apply e.reachable_withFixed (sourceBoard := (template kind).board ∅) (by simpa [GridEmbedding.WallsAgree, Template.board] using hwalls) hinside hfixed hfree
    simpa [Gates.withFixed, state] using hbwd

theorem position_component_placed {W H : ℕ} (kind a b : Bool) (i : Fin (count kind))
    (e : GridEmbedding (width kind) 21 W H) {B : Board W H}
    (hwalls : ∀ p, e.cells p ∈ B.walls ↔ p ∈ walls kind) :
    SameComponent B (e.cells (position kind a i)) (e.cells (position kind b i)) := by
  simpa using (checked kind).position_component_placed a b i e (by simpa [GridEmbedding.WallsAgree, Template.board] using hwalls)

end PushPuzzle.PushFS.Gadgets.Wires.Chain.Tile
