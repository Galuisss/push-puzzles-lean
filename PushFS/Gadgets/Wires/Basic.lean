/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Gates.Framing
public import PushFS.Gadgets.Gates.StaticSlots

/-!
# Finite wire templates with complete physical slots and executable certificates

A template gives all walls, both positions of every box, the exact player hub,
two full phase-change programs, and four actual corner walks. Concrete finite
templates supply kernel-checked certificates for each of these programs.
-/

@[expose] public section

namespace PushPuzzle.PushFS.Gadgets.Wires


open Gates (withFixed)

/-- The exact data of one finite two-phase wire tile. -/
structure Template (w h count : ℕ) where
  /-- The exact player hub used at both ends of every phase change. -/
  hub : Cell w h
  /-- Four exterior walking anchors, in NW/NE/SW/SE order. -/
  corner : Fin 4 → Cell w h
  /-- Complete fixed-wall predicate. -/
  wall : Cell w h → Bool
  /-- All possible buffer positions, excluding traversable flip crossings. -/
  reserved : Cell w h → Bool
  /-- Actual neighboring box positions permitted during propagation. -/
  neighbors : Finset (Cell w h)
  /-- The false-phase position of each physical identity. -/
  zero : Fin count → Cell w h
  /-- The true-phase position of each physical identity. -/
  one : Fin count → Cell w h
  /-- Every walk and push in the false-to-true phase change. -/
  forward : List Direction
  /-- Every walk and push in the true-to-false phase change. -/
  backward : List Direction
  /-- Complete hub-to-corner walking programs. -/
  walks : Fin 4 → List Direction

namespace Template

variable {w h count : ℕ}

/-- Position of one fixed identity in the selected canonical phase. -/
def position (T : Template w h count) (phase : Bool) (i : Fin count) : Cell w h :=
  if phase then T.one i else T.zero i

/-- Every canonical physical box, without labels in the actual game state. -/
def boxes (T : Template w h count) (phase : Bool) : Finset (Cell w h) :=
  Finset.univ.image (T.position phase)

/-- Full exact canonical state. -/
def state (T : Template w h count) (phase : Bool) : State w h := ⟨T.hub, T.boxes phase⟩

/-- Complete fixed walls. -/
def walls (T : Template w h count) : Finset (Cell w h) := Finset.univ.filter fun p => T.wall p

/-- Conservative rail obstacles used by the walking programs. -/
def reservedCells (T : Template w h count) : Finset (Cell w h) :=
  Finset.univ.filter fun p => T.reserved p

/-- The actual tile board, with an independently chosen exact goal set. -/
def board (T : Template w h count) (goals : Finset (Cell w h)) : Board w h := ⟨T.walls, goals⟩

/-- The propagation checker reserves the real neighboring box positions as obstacles. -/
def guardTest (T : Template w h count) (p : Cell w h) : Bool :=
  T.wall p || decide (p ∈ T.neighbors)

/-- The walking checker reserves every potential rail box position. -/
def walkTest (T : Template w h count) (p : Cell w h) : Bool := T.wall p || T.reserved p

/-- A straight static slot path; every concrete slot is horizontal or vertical. -/
def slotDirections (p q : Cell w h) : List Direction :=
  if p.1.val < q.1.val then List.replicate (q.1.val - p.1.val) .east
  else if q.1.val < p.1.val then List.replicate (p.1.val - q.1.val) .west
  else if p.2.val < q.2.val then List.replicate (q.2.val - p.2.val) .south
  else List.replicate (p.2.val - q.2.val) .north

/-- Finite executable certificates for all physical slots and both complete phase changes. -/
structure Checked (T : Template w h count) : Prop where
  /-- Every box has a distinct position in either phase. -/
  injective : ∀ phase, Function.Injective (T.position phase)
  /-- All canonical box positions lie in the reserved rail set. -/
  slots_reserved : ∀ phase i, T.reserved (T.position phase i) = true
  /-- Every neighboring box position is a reserved rail cell. -/
  neighbors_reserved : ∀ p ∈ T.neighbors, T.reserved p = true
  /-- Neighbor positions lie on actual floor. -/
  neighbors_floor : ∀ p ∈ T.neighbors, T.wall p = false
  /-- Every physical slot is statically reachable in both directions. -/
  static_paths : ∀ i,
    Gates.staticRun T.wall (T.zero i) (slotDirections (T.zero i) (T.one i)) = some (T.one i) ∧
    Gates.staticRun T.wall (T.one i) (slotDirections (T.one i) (T.zero i)) = some (T.zero i)
  /-- The complete forward program, with the real neighbor collar reserved. -/
  forward_checked : Execution.valid T.guardTest (T.state false) = true ∧
    Execution.check T.guardTest (T.state false) (T.state true) T.forward = true
  /-- The complete backward program, with the real neighbor collar reserved. -/
  backward_checked : Execution.valid T.guardTest (T.state true) = true ∧
    Execution.check T.guardTest (T.state true) (T.state false) T.backward = true
  /-- All four walks avoid every reserved rail position. -/
  walks_checked : ∀ i, Execution.valid T.walkTest ⟨T.hub, ∅⟩ = true ∧
    Execution.check T.walkTest ⟨T.hub, ∅⟩ ⟨T.corner i, ∅⟩ (T.walks i) = true

@[simp] theorem mem_walls (T : Template w h count) (p : Cell w h) :
    p ∈ T.walls ↔ T.wall p = true := by simp [walls]

@[simp] theorem mem_reserved (T : Template w h count) (p : Cell w h) :
    p ∈ T.reservedCells ↔ T.reserved p = true := by simp [reservedCells]

theorem wall_correct (T : Template w h count) (goals : Finset (Cell w h)) (p : Cell w h) :
    T.wall p = true ↔ p ∈ (T.board goals).walls := (T.mem_walls p).symm

private theorem same_walls {B C : Board w h} {s t : State w h}
    (hw : B.walls = C.walls) (hr : Reachable B (some 1) s t) : Reachable C (some 1) s t := by
  have hstep : ∀ s t, Step B (some 1) s t → Step C (some 1) s t := by
    rintro s t ⟨d, hd⟩
    have hm := Move.single_iff.mp hd
    exact ⟨d, Move.single_iff.mpr (by simpa only [SingleMoveView, State.Valid, hw] using hm)⟩
  exact hr.lift id hstep

variable {T : Template w h count}

theorem Checked.state_valid_guard (hc : T.Checked) (phase : Bool) :
    (T.state phase).Valid (⟨T.walls ∪ T.neighbors, ∅⟩ : Board w h) := by
  have hw : ∀ p, T.guardTest p = true ↔ p ∈ T.walls ∪ T.neighbors := by simp [guardTest]
  apply (Execution.valid_correct hw _).mp
  cases phase
  · exact hc.forward_checked.1
  · exact hc.backward_checked.1

theorem Checked.boxes_floor (hc : T.Checked) (phase : Bool) : Disjoint (T.boxes phase) T.walls :=
  (hc.state_valid_guard phase).2.1.mono_right Finset.subset_union_left

theorem Checked.boxes_reserved (hc : T.Checked) (phase : Bool) : T.boxes phase ⊆ T.reservedCells := by
  intro p hp
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  exact (T.mem_reserved _).mpr (hc.slots_reserved phase i)

private theorem Checked.neighbors_disjoint (hc : T.Checked) : Disjoint T.neighbors T.walls := by
  apply Finset.disjoint_left.mpr
  intro p hp hw
  exact Bool.noConfusion ((hc.neighbors_floor p hp).symm.trans ((T.mem_walls p).mp hw))

theorem Checked.boxes_card (hc : T.Checked) (phase : Bool) : (T.boxes phase).card = count := by
  rw [boxes, Finset.card_image_of_injective _ (hc.injective phase), Finset.card_univ, Fintype.card_fin]

/-- Propagate either phase change while all actual collar neighbors stay fixed. -/
theorem Checked.transition (hc : T.Checked) (a b : Bool) (goals fixed : Finset (Cell w h))
    (hf : fixed ⊆ T.neighbors) :
    Reachable (T.board goals) (some 1) (withFixed fixed (T.state a)) (withFixed fixed (T.state b)) := by
  have hw : ∀ p, T.guardTest p = true ↔ p ∈ T.walls ∪ T.neighbors := by simp [guardTest]
  have run {s t : State w h} {ds : List Direction}
      (hchecked : Execution.valid T.guardTest s = true ∧ Execution.check T.guardTest s t ds = true) :
      Reachable (T.board goals) (some 1) (withFixed fixed s) (withFixed fixed t) := by
    have hr := Execution.sound (B := ⟨T.walls ∪ T.neighbors, ∅⟩) hw hchecked.1 hchecked.2
    have hr' : Reachable (⟨T.walls ∪ T.neighbors, goals⟩ : Board w h) (some 1) s t :=
      same_walls (B := ⟨T.walls ∪ T.neighbors, ∅⟩) rfl hr
    exact Gates.reachable_withFixed hf (hc.neighbors_disjoint.mono_left hf) hr'
  cases a <;> cases b
  · exact .refl
  · exact run hc.forward_checked
  · exact run hc.backward_checked
  · exact .refl

private theorem empty_symm {B : Board w h} {p q : Cell w h}
    (hr : Reachable B (some 1) ⟨p, ∅⟩ ⟨q, ∅⟩) : Reachable B (some 1) ⟨q, ∅⟩ ⟨p, ∅⟩ := by
  have aux : ∀ {s t : State w h}, Reachable B (some 1) s t → s.boxes = ∅ →
      Reachable B (some 1) t s := by
    intro s t hr
    induction hr with
    | refl => intro _; exact .refl
    | @tail u v hr hs ih =>
      intro he
      have hu : u.boxes = ∅ := Finset.card_eq_zero.mp (by rw [Reachable.card_boxes hr, he]; rfl)
      have hv : v.boxes = ∅ := Finset.card_eq_zero.mp (by rw [Step.card_boxes hs, hu]; rfl)
      obtain ⟨d, hd⟩ := hs
      have hm := Move.single_iff.mp hd
      have hback : Move B (some 1) d.opposite v u :=
        .walk hd.valid_target hm.2.1.reverse hd.valid_source.1 (by simp [hv]) (hu.trans hv.symm)
      exact (Relation.ReflTransGen.single ⟨d.opposite, hback⟩).trans (ih he)
  exact aux hr rfl

private theorem Checked.empty_walk (hc : T.Checked) (i : Fin 4) :
    Reachable (⟨T.walls ∪ T.reservedCells, ∅⟩ : Board w h) (some 1) ⟨T.hub, ∅⟩ ⟨T.corner i, ∅⟩ := by
  have hw : ∀ p, T.walkTest p = true ↔ p ∈ T.walls ∪ T.reservedCells := by simp [walkTest]
  exact Execution.sound hw (hc.walks_checked i).1 (hc.walks_checked i).2

/-- Walk to an exterior corner with any actual rail inventory, including mixed phases. -/
theorem Checked.corner_reachable (hc : T.Checked) (i : Fin 4) (goals actual : Finset (Cell w h))
    (ha : actual ⊆ T.reservedCells) (hw : Disjoint actual T.walls) :
    Reachable (T.board goals) (some 1) ⟨T.hub, actual⟩ ⟨T.corner i, actual⟩ := by
  have hr : Reachable (⟨T.walls ∪ T.reservedCells, goals⟩ : Board w h)
      (some 1) ⟨T.hub, ∅⟩ ⟨T.corner i, ∅⟩ := same_walls (B := ⟨T.walls ∪ T.reservedCells, ∅⟩) rfl (hc.empty_walk i)
  simpa only [withFixed, Finset.empty_union] using Gates.reachable_withFixed (B := T.board goals) ha hw hr

/-- Return from an exterior corner with the same actual rail inventory. -/
theorem Checked.corner_to_hub (hc : T.Checked) (i : Fin 4) (goals actual : Finset (Cell w h))
    (ha : actual ⊆ T.reservedCells) (hw : Disjoint actual T.walls) :
    Reachable (T.board goals) (some 1) ⟨T.corner i, actual⟩ ⟨T.hub, actual⟩ := by
  have hr : Reachable (⟨T.walls ∪ T.reservedCells, goals⟩ : Board w h)
      (some 1) ⟨T.corner i, ∅⟩ ⟨T.hub, ∅⟩ := same_walls (B := ⟨T.walls ∪ T.reservedCells, ∅⟩) rfl (empty_symm (hc.empty_walk i))
  simpa only [withFixed, Finset.empty_union] using Gates.reachable_withFixed (B := T.board goals) ha hw hr

theorem Checked.position_component (hc : T.Checked) (a b : Bool) (goals : Finset (Cell w h))
    (i : Fin count) : SameComponent (T.board goals) (T.position a i) (T.position b i) := by
  have hf := Gates.staticRun_sound (T.wall_correct goals) (hc.static_paths i).1
  have hb := Gates.staticRun_sound (T.wall_correct goals) (hc.static_paths i).2
  cases a <;> cases b
  · exact ⟨.refl, .refl⟩
  · exact ⟨hf, hb⟩
  · exact ⟨hb, hf⟩
  · exact ⟨.refl, .refl⟩

end Template
end PushPuzzle.PushFS.Gadgets.Wires
