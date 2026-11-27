/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushFS.Run

/-! Full blocks wider than the finite push limit are permanently frozen. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteFreeze

open PushFS

variable {w h k : ℕ} {W : Finset (Cell w h)}

/-- Every occupied point lies in a full interval longer than the push limit on each axis. -/
def Thick (k : ℕ) (W : Finset (Cell w h)) : Prop :=
  ∀ (d : Direction) p, p ∈ W → ∃ a b : ℤ,
    a ≤ d.position p ∧ d.position p ≤ b ∧ (k : ℤ) < b - a + 1 ∧
    ∀ q, d.lane q = d.lane p → a ≤ d.position q → d.position q ≤ b → q ∈ W

/-- Each point is covered by a completely filled square of the given side length. -/
def SquareCovered (side : ℕ) (W : Finset (Cell w h)) : Prop :=
  ∀ p, p ∈ W → ∃ x y : ℕ,
    x ≤ p.1.val ∧ p.1.val < x + side ∧ y ≤ p.2.val ∧ p.2.val < y + side ∧
    ∀ q : Cell w h, x ≤ q.1.val → q.1.val < x + side →
      y ≤ q.2.val → q.2.val < y + side → q ∈ W

/-- Filled square covers provide the directional thickness used by the first-motion argument. -/
theorem thick_of_squareCovered {side : ℕ} (hside : k < side)
    (hW : SquareCovered side W) : Thick k W := by
  intro d p hp
  obtain ⟨x, y, hx, hx', hy, hy', hfull⟩ := hW p hp
  cases d with
  | north =>
    refine ⟨-(y : ℤ) - side + 1, -(y : ℤ), ?_, ?_, ?_, ?_⟩
    · simp only [Direction.position]; omega
    · simp only [Direction.position]; omega
    · omega
    · intro q hl ha hb
      simp only [Direction.lane, Direction.position] at hl ha hb
      apply hfull q <;> omega
  | east =>
    refine ⟨(x : ℤ), (x : ℤ) + side - 1, ?_, ?_, ?_, ?_⟩
    · simp only [Direction.position]; omega
    · simp only [Direction.position]; omega
    · omega
    · intro q hl ha hb
      simp only [Direction.lane, Direction.position] at hl ha hb
      apply hfull q <;> omega
  | south =>
    refine ⟨(y : ℤ), (y : ℤ) + side - 1, ?_, ?_, ?_, ?_⟩
    · simp only [Direction.position]; omega
    · simp only [Direction.position]; omega
    · omega
    · intro q hl ha hb
      simp only [Direction.lane, Direction.position] at hl ha hb
      apply hfull q <;> omega
  | west =>
    refine ⟨-(x : ℤ) - side + 1, -(x : ℤ), ?_, ?_, ?_, ?_⟩
    · simp only [Direction.position]; omega
    · simp only [Direction.position]; omega
    · omega
    · intro q hl ha hb
      simp only [Direction.lane, Direction.position] at hl ha hb
      apply hfull q <;> omega

/-- A legal bounded run avoids every cell of a full thick region. -/
theorem run_avoids (hW : Thick k W) {B : Board w h} {d : Direction}
    {s : State w h} {n : ℕ} (hs : s.Valid B) (hfull : W ⊆ s.boxes)
    (run : Run B d s n) (hn : n ≤ k) (i : Fin (n + 2)) : run.cell i ∉ W := by
  intro hi
  obtain ⟨a, b, ha, hb, hwidth, hinterval⟩ := hW d (run.cell i) hi
  have hstart : run.cell 0 ∉ W := fun h => hs.2.2 (run.start ▸ hfull h)
  have hend : run.cell ⟨n + 1, by omega⟩ ∉ W := fun h => run.empty (hfull h)
  have hpos := run.position i
  have hpos0 : d.position (run.cell 0) = d.position s.player := by
    simpa only [Fin.val_zero, Int.natCast_zero, Int.add_zero] using run.position 0
  have hposEnd : d.position (run.cell ⟨n + 1, by omega⟩) =
      d.position s.player + (n + 1 : ℕ) := run.position _
  have hiBound := i.isLt
  have hl0 : d.lane (run.cell 0) = d.lane (run.cell i) :=
    (run.lane 0).trans (run.lane i).symm
  have hlEnd : d.lane (run.cell ⟨n + 1, by omega⟩) = d.lane (run.cell i) :=
    (run.lane _).trans (run.lane i).symm
  have ha' : d.position (run.cell 0) < a := by
    by_contra hh
    exact hstart (hinterval _ hl0 (by omega) (by omega))
  have hb' : b < d.position (run.cell ⟨n + 1, by omega⟩) := by
    by_contra hh
    exact hend (hinterval _ hlEnd (by omega) (by omega))
  omega

/-- No move dislodges any box of the full thick region. -/
private theorem move_full (hW : Thick k W) {B : Board w h} {d : Direction}
    {s t : State w h} (hm : Move B (some k) d s t) (hfull : W ⊆ s.boxes) :
    W ⊆ t.boxes := by
  cases hm with
  | walk _ _ _ _ hb => simpa only [hb] using hfull
  | push hv _ hn run _ hb =>
    have ha := run_avoids hW hv hfull run hn 1
    intro p hp
    rw [hb]
    exact Finset.mem_insert_of_mem
      (Finset.mem_erase.mpr ⟨fun he => ha (he ▸ hp), hfull hp⟩)

/-- A filled thick region remains full throughout every bounded trajectory. -/
theorem reachable_full (hW : Thick k W) {B : Board w h} {s t : State w h}
    (hr : Reachable B (some k) s t) (hfull : W ⊆ s.boxes) : W ⊆ t.boxes := by
  induction hr with
  | refl => exact hfull
  | tail _ hm ih => exact move_full hW hm.choose_spec ih

end PushPuzzle.PushS.FiniteFreeze
