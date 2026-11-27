/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.Holes

/-! The corner of two solid northeast regions cannot be reopened after it is filled. -/

public section
namespace PushPuzzle.Push.SealedDoor

open PushFS PushS

variable {w h cut height : ℕ} {B : Board w h} {cap : Option ℕ}
  {d : Direction} {s t : State w h}

/-- Solid source-side regions exclude every complete run that could reopen the door. -/
theorem move_full (door : Cell w h) (hx : door.1.val = cut) (hy : door.2.val + 1 = height)
    (heast : ∀ q : Cell w h, cut < q.1.val → q.2.val < height → q ∈ s.boxes)
    (hnorth : ∀ q : Cell w h, cut ≤ q.1.val → q.2.val + 1 < height → q ∈ s.boxes)
    (hm : Move B cap d s t) (hs : door ∈ s.boxes) : door ∈ t.boxes := by
  by_contra ht
  have he : t.player = door := by
    by_contra he
    exact (mem_holes _).mp
      (hole_source_of_ne_player hm (Ne.symm he) ((mem_holes _).mpr ht)) hs
  have htx : t.player.1.val = cut := (congrArg (fun q => q.1.val) he).trans hx
  have hty : t.player.2.val + 1 = height := by rw [he]; exact hy
  cases hm with
  | walk _ _ _ hempty _ => exact hempty (he ▸ hs)
  | @push n hv hn _ run hp hb =>
    have hp1 := run.position 1
    have hpl := run.position ⟨n + 1, by omega⟩
    have hl1 := run.lane 1
    have hll := run.lane ⟨n + 1, by omega⟩
    rw [← hp] at hp1 hl1
    simp only [Fin.val_one] at hp1 hpl
    cases d with
    | north =>
      simp only [Direction.position, Direction.lane] at hp1 hpl hl1 hll
      exact run.empty (hnorth _ (by omega) (by omega))
    | east =>
      simp only [Direction.position, Direction.lane] at hp1 hpl hl1 hll
      exact run.empty (heast _ (by omega) (by omega))
    | south =>
      simp only [Direction.position, Direction.lane] at hp1 hpl hl1 hll
      exact hv.2.2 (hnorth _ (by omega) (by omega))
    | west =>
      simp only [Direction.position, Direction.lane] at hp1 hpl hl1 hll
      exact hv.2.2 (heast _ (by omega) (by omega))

end PushPuzzle.Push.SealedDoor
