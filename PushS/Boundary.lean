/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushFS.Run

/-! A box on an outer edge can move along that edge but cannot leave it. -/

@[expose] public section
namespace PushPuzzle.PushS.Boundary

open PushFS

variable {w h : ℕ}

/-- The edge facing the specified direction. -/
def edge (d : Direction) : Finset (Cell w h) :=
  match d with
  | .north => Finset.univ.filter fun p => p.2.val = 0
  | .east => Finset.univ.filter fun p => p.1.val + 1 = w
  | .south => Finset.univ.filter fun p => p.2.val + 1 = h
  | .west => Finset.univ.filter fun p => p.1.val = 0

/-- The four outer edges of the rectangle. -/
def frame : Finset (Cell w h) :=
  edge .north ∪ edge .east ∪ edge .south ∪ edge .west

theorem mem_frame (p : Cell w h) : p ∈ frame ↔ ∃ d, p ∈ edge d := by
  simp only [frame, Finset.mem_union]
  constructor
  · rintro (((hn | he) | hs) | hw)
    · exact ⟨.north, hn⟩
    · exact ⟨.east, he⟩
    · exact ⟨.south, hs⟩
    · exact ⟨.west, hw⟩
  · rintro ⟨d, hd⟩
    cases d <;> tauto

variable {B : Board w h} {cap : Option ℕ} {d : Direction} {s t : State w h}

/-- If a push consumes an edge box, its new endpoint is on the same edge. -/
theorem run_last_mem_edge {n : ℕ} (r : Run B d s n) (e : Direction)
    (hn : 0 < n) (he : r.cell 1 ∈ edge e) :
    r.cell ⟨n + 1, by omega⟩ ∈ edge e := by
  have hp := r.position 1
  have hz := r.position ⟨n + 1, by omega⟩
  have lp := r.lane 1
  have lz := r.lane ⟨n + 1, by omega⟩
  have hx := s.player.1.isLt
  have hy := s.player.2.isLt
  have hzx := (r.cell ⟨n + 1, by omega⟩).1.isLt
  have hzy := (r.cell ⟨n + 1, by omega⟩).2.isLt
  cases e <;> cases d <;>
    simp only [edge, Finset.mem_filter, Finset.mem_univ, true_and,
      Direction.position, Direction.lane, Fin.val_one] at * <;> omega

/-- Each occupied outer edge remains occupied after a legal move. -/
private theorem move_has_edge_box (hm : Move B cap d s t) (e : Direction)
    (hs : ∃ p ∈ s.boxes, p ∈ edge e) : ∃ p ∈ t.boxes, p ∈ edge e := by
  obtain ⟨p, hp, he⟩ := hs
  cases hm with
  | walk _ _ _ _ hb => exact ⟨p, hb ▸ hp, he⟩
  | push _ hn _ r _ hb =>
    by_cases hpf : p = r.cell 1
    · subst p
      exact ⟨_, hb ▸ Finset.mem_insert_self _ _, run_last_mem_edge r e hn he⟩
    · exact ⟨p, hb ▸ Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hpf, hp⟩), he⟩

/-- Every occupied outer edge stays occupied along any finite play. -/
private theorem reachable_has_edge_box (hr : Reachable B cap s t) (e : Direction)
    (hs : ∃ p ∈ s.boxes, p ∈ edge e) : ∃ p ∈ t.boxes, p ∈ edge e := by
  induction hr with
  | refl => exact hs
  | tail _ hm ih => exact move_has_edge_box hm.choose_spec e ih

/-- An empty final edge was empty throughout every prefix ending there. -/
theorem reachable_edge_empty (hr : Reachable B cap s t) (e : Direction)
    (ht : Disjoint t.boxes (edge e)) : Disjoint s.boxes (edge e) := by
  apply Finset.disjoint_left.mpr
  intro p hp he
  obtain ⟨q, hq, hqe⟩ := reachable_has_edge_box hr e ⟨p, hp, he⟩
  exact Finset.disjoint_left.mp ht hq hqe

/-- If the final outer frame is empty, it is empty at the start of every suffix. -/
theorem reachable_frame_empty (hr : Reachable B cap s t)
    (ht : Disjoint t.boxes frame) : Disjoint s.boxes frame := by
  apply Finset.disjoint_left.mpr
  intro p hp hf
  obtain ⟨e, he⟩ := (mem_frame p).mp hf
  obtain ⟨q, hq, hqe⟩ := reachable_has_edge_box hr e ⟨p, hp, he⟩
  exact Finset.disjoint_left.mp ht hq ((mem_frame q).mpr ⟨e, hqe⟩)

end PushPuzzle.PushS.Boundary
