/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.HoleState

/-! Coordinate construction of a complete push to the first hole on a straight line. -/

public section

namespace PushPuzzle.PushS.HoleState


open PushFS

variable {w h : ℕ}

private def ray (d : Direction) (a b : Cell w h) (n : ℕ)
    (hl : d.lane b = d.lane a) (hg : d.position b = d.position a + n + 1)
    (i : Fin (n + 2)) : Cell w h :=
  match d with
  | .north => (a.1, ⟨a.2.val - i.val, by
      have := a.2.isLt; dsimp [Direction.position] at hg; omega⟩)
  | .east => (⟨a.1.val + i.val, by
      have := b.1.isLt; dsimp [Direction.position] at hg; omega⟩, a.2)
  | .south => (a.1, ⟨a.2.val + i.val, by
      have := b.2.isLt; dsimp [Direction.position] at hg; omega⟩)
  | .west => (⟨a.1.val - i.val, by
      have := a.1.isLt; dsimp [Direction.position] at hg; omega⟩, a.2)

private theorem ray_coordinates (d : Direction) (a b : Cell w h) (n : ℕ)
    (hl : d.lane b = d.lane a) (hg : d.position b = d.position a + n + 1)
    (i : Fin (n + 2)) :
    d.lane (ray d a b n hl hg i) = d.lane a ∧
      d.position (ray d a b n hl hg i) = d.position a + i.val := by
  cases d <;> dsimp only [Direction.position] at hg <;>
    simp only [ray, Direction.lane, Direction.position, Fin.val_mk, true_and] <;> omega

private theorem state_ext (s t : HoleState w h) (hp : s.player = t.player)
    (he : s.empty = t.empty) : s = t := by
  cases s; cases t; simp_all

/-- Occupancy of the open segment and its first empty endpoint construct a genuine push.
The target replaces that endpoint hole by the adjacent box cell. -/
theorem move_to_first_hole (s t : HoleState w h) (d : Direction) (b : Cell w h)
    (n : ℕ) (hn : 0 < n) (hl : d.lane b = d.lane s.player)
    (hg : d.position b = d.position s.player + n + 1)
    (ho : ∀ q, d.lane q = d.lane s.player →
      d.position s.player < d.position q → d.position q < d.position b → q ∉ s.empty)
    (hb : b ∈ s.empty) (ht : Adjacent d s.player t.player)
    (he : t.empty = insert t.player (s.empty.erase b))
    (B : Board w h) (hB : B.walls = ∅) : Move B none d s.toState t.toState := by
  let r : s.Push d := {
    length := n
    positive := hn
    cell := ray d s.player b n hl hg
    start := d.cell_ext (ray_coordinates d s.player b n hl hg 0).1
      (by simpa using (ray_coordinates d s.player b n hl hg 0).2)
    adjacent := fun i => (adjacent_iff_coordinates d _ _).mpr ⟨by
      rw [(ray_coordinates d s.player b n hl hg _).1,
        (ray_coordinates d s.player b n hl hg _).1], by
      rw [(ray_coordinates d s.player b n hl hg _).2,
        (ray_coordinates d s.player b n hl hg _).2]; simp; omega⟩
    occupied := fun i => ho _ (ray_coordinates d s.player b n hl hg _).1 (by
      rw [(ray_coordinates d s.player b n hl hg _).2]; simp) (by
      rw [(ray_coordinates d s.player b n hl hg _).2, hg]; simp_all; omega)
    destination := by
      have heq : ray d s.player b n hl hg ⟨n + 1, by omega⟩ = b :=
        d.cell_ext ((ray_coordinates d s.player b n hl hg _).1.trans hl.symm)
          (by rw [(ray_coordinates d s.player b n hl hg _).2, hg]; simp_all; omega)
      rw [heq]; exact hb }
  have hp : r.cell 1 = t.player :=
    d.cell_ext ((ray_coordinates d s.player b n hl hg 1).1.trans ht.lane.symm)
      (by change d.position (ray d s.player b n hl hg 1) = _
          rw [(ray_coordinates d s.player b n hl hg 1).2, ht.position]; simp)
  have hb' : r.cell ⟨r.length + 1, by omega⟩ = b :=
    d.cell_ext ((ray_coordinates d s.player b n hl hg _).1.trans hl.symm)
      (by change d.position (ray d s.player b n hl hg _) = _
          rw [(ray_coordinates d s.player b n hl hg _).2, hg]; simp [r]; omega)
  have heq : r.target = t := by
    have he' : r.target.empty = t.empty := by
      change insert (r.cell 1) (s.empty.erase _) = t.empty
      rw [hp, hb']; exact he.symm
    exact state_ext _ _ hp he'
  exact heq ▸ r.move B hB none trivial

end PushPuzzle.PushS.HoleState
