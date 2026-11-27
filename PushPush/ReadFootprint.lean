/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.ReadRun

/-! Exact hole footprints of committed source-column reads. -/

@[expose] public section
namespace PushPuzzle.PushPush.Reader

open PushFS (Cell State Direction)

variable {w h n k : ℕ} {s : State w h}

/-- The source-column cells traversed by `q` northward player steps. -/
def northTrail (s : State w h) (q : ℕ) : Finset (Cell w h) :=
  Finset.univ.filter fun p => p.1 = s.player.1 ∧
    s.player.2.val - q ≤ p.2.val ∧ p.2.val < s.player.2.val

@[simp] theorem northTrail_zero (s : State w h) : northTrail s 0 = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have := (Finset.mem_filter.mp hp).2
  omega

private theorem slide_trail (r : Slide .north s n k) : r.trail = northTrail s k := by
  ext p
  constructor
  · intro hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    have hx := r.lane ⟨i.val + 1, by omega⟩
    have hy := r.position ⟨i.val + 1, by omega⟩
    change -((r.cell ⟨i.val + 1, by omega⟩).2.val : ℤ) =
      -(s.player.2.val : ℤ) + (i.val + 1 : ℕ) at hy
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, Fin.ext hx, ?_⟩
    constructor <;> omega
  · intro hp
    obtain ⟨_, hx, hlo, hhi⟩ := Finset.mem_filter.mp hp
    let i : Fin k := ⟨s.player.2.val - p.2.val - 1, by omega⟩
    refine Finset.mem_image.mpr ⟨i, Finset.mem_univ _, ?_⟩
    apply Direction.north.cell_ext
    · exact (r.lane _).trans (congrArg Fin.val hx.symm)
    · rw [r.position]
      change -(s.player.2.val : ℤ) + (i.val + 1 : ℕ) = -(p.2.val : ℤ)
      dsimp only [i]
      omega

theorem northTrail_append (s u : State w h) (a b : ℕ)
    (hx : u.player.1 = s.player.1) (hy : u.player.2.val + a = s.player.2.val) :
    northTrail s a ∪ northTrail u b = northTrail s (a + b) := by
  ext p
  simp only [northTrail, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, hx]
  by_cases hp : p.1 = s.player.1 <;> simp [hp]
  omega

theorem NorthRun.target_holes {cutoff : ℕ} (R : NorthRun s cutoff)
    (hspace : cutoff + (northData s cutoff).card < s.player.2.val)
    (hgap : ∀ q : Cell w h, q.1 = s.player.1 → cutoff ≤ q.2.val →
      q.2.val < s.player.2.val → q ∈ s.boxes) (hv : s.player ∉ s.boxes) :
    (R.target hspace hgap).boxesᶜ =
      (s.boxesᶜ \ (R.toSlide hspace hgap).gap) ∪ northTrail s R.length := by
  rw [show (R.target hspace hgap).boxes = (R.toSlide hspace hgap).boxes from rfl,
    (R.toSlide hspace hgap).holes_eq hv (R.length_le_train hspace hgap), slide_trail]

/-- Successive reads delete disjoint source runs while retaining earlier trailing holes. -/
theorem erase_source_runs {α : Type} [DecidableEq α] (S D G T : Finset α)
    (hGD : G ⊆ D) (hTD : Disjoint T D) :
    ((S \ G) ∪ T) \ (D \ G) = (S \ D) ∪ T := by
  ext p
  have hg : p ∈ G → p ∈ D := fun hp => hGD hp
  have ht : p ∈ T → p ∉ D := fun hp hd => Finset.disjoint_left.mp hTD hp hd
  simp only [Finset.mem_sdiff, Finset.mem_union]
  tauto

end PushPuzzle.PushPush.Reader
