/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.UnitExpansion
public import Push.CornerDockTrace
import all Push.CornerDockReverse

/-! Maximum-slide source prefixes of the southwest docking extension. -/

@[expose] public section
namespace PushPuzzle.PushPush.CornerDock

open PushFS (Cell State Direction Adjacent)

variable (r : Push.CornerDock.Input)
variable {s t : State r.outputWidth r.outputHeight} {d : Direction} {n k : ℕ}

/-- Maximum-game steps whose actual player remains in the original source. -/
def SourceStep (s t : State r.outputWidth r.outputHeight) : Prop := Step s t ∧ r.SourceInside t

/-- The full slide's final leading cell was an original hole. -/
theorem slide_last_empty (slide : Slide d s n k) (hk : 0 < k) :
    slide.cell ⟨n + k, by omega⟩ ∉ s.boxes := by
  have he : (⟨n + (k - 1) + 1, by omega⟩ : Fin (n + k + 1)) =
      ⟨n + k, by omega⟩ := Fin.ext (by change n + (k - 1) + 1 = n + k; omega)
  exact he ▸ slide.clear ⟨k - 1, by omega⟩

/-- No outside dock hole apart from the entry is aligned with an inside source player. -/
private theorem slide_last_inside_or_entry (slide : Slide d s n k) (hk : 0 < k)
    (hpre : Relation.ReflTransGen r.SourceStep r.compile.initial s)
    (hs : r.SourceInside s) :
    (2 ≤ (slide.cell ⟨n + k, by omega⟩).1.val ∧
      (slide.cell ⟨n + k, by omega⟩).2.val < r.height) ∨
      slide.cell ⟨n + k, by omega⟩ = r.entry := by
  classical
  by_cases hi : 2 ≤ (slide.cell ⟨n + k, by omega⟩).1.val ∧
      (slide.cell ⟨n + k, by omega⟩).2.val < r.height
  · exact Or.inl hi
  · right
    have hhole := (PushS.mem_holes _).mpr (slide_last_empty r slide hk)
    have haux := r.outside_hole_source hpre _ hi hhole
    rcases Finset.mem_insert.mp haux with he | hw
    · exact he
    · have hw := (Finset.mem_filter.mp hw).2
      have hp := slide.position ⟨n + k, by omega⟩
      have hl := slide.lane ⟨n + k, by omega⟩
      have hsx := hs.1
      have hsy := hs.2
      cases d <;> simp only [Direction.position, Direction.lane] at hp hl <;> omega

/-- Artificial follow-the-run player positions stay inside the dock's original source. -/
theorem slide_players_inside (slide : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hpre : Relation.ReflTransGen r.SourceStep r.compile.initial s)
    (hs : r.SourceInside s) (i : Fin (k + 1)) : r.SourceInside (slide.stage i) := by
  have hlast := slide_last_inside_or_entry r slide hk hpre hs
  have hip := slide.position ⟨i.val, by omega⟩
  have hil := slide.lane ⟨i.val, by omega⟩
  have hep := slide.position ⟨n + k, by omega⟩
  have hel := slide.lane ⟨n + k, by omega⟩
  have hsx := hs.1
  have hsy := hs.2
  change 2 ≤ (slide.cell ⟨i.val, by omega⟩).1.val ∧
    (slide.cell ⟨i.val, by omega⟩).2.val < r.height
  rcases hlast with hlast | he
  · cases d <;> simp only [Direction.position, Direction.lane] at hip hil hep hel <;> omega
  · rw [he] at hep hel
    have hentryX : r.entry.1.val = 1 := rfl
    have hentryY : r.entry.2.val < r.height := r.goalY.isLt
    cases d <;> simp only [Direction.position, Direction.lane] at hip hil hep hel <;> omega

/-- One inside maximum action has an inside ordinary expansion. -/
theorem source_step_expansion
    (hpre : Relation.ReflTransGen r.SourceStep r.compile.initial s)
    (hm : SourceStep r s t) : Relation.ReflTransGen r.SourceStep s t := by
  obtain ⟨⟨d, hmove⟩, htInside⟩ := hm
  cases hmove with
  | walk hv ha he hb =>
    exact Relation.ReflTransGen.single ⟨⟨d, .walk
      ⟨Finset.notMem_empty _, Finset.disjoint_empty_right _, hv⟩ ha (Finset.notMem_empty _) he hb⟩,
      htInside⟩
  | push hv hn hk slide hp hb =>
    have hs := r.sourceInside_prefix hpre
    have hpath := slide.unit_expansion_player_prefix hn hk hv r.compile.board.goals
      (fun p => 2 ≤ p.1.val ∧ p.2.val < r.height) (slide_players_inside r slide hn hk hpre hs)
    have he : (⟨slide.cell ⟨1, by omega⟩, slide.boxes⟩ : State _ _) = _ := State.ext hp.symm hb.symm
    exact he ▸ hpath

/-- Every inside maximum action expands to a complete ordinary inside-source trace. -/
theorem source_prefix_expansion {s : State r.outputWidth r.outputHeight}
    (hr : Relation.ReflTransGen (SourceStep r) r.compile.initial s) :
    Relation.ReflTransGen r.SourceStep r.compile.initial s := by
  induction hr with
  | refl => exact .refl
  | tail _ hm ih => exact ih.trans (source_step_expansion r ih hm)

/-- Keeping the dock entry empty forces the complete maximum ray to remain in the source. -/
theorem slide_inside (slide : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hpre : Relation.ReflTransGen r.SourceStep r.compile.initial s) (hs : r.SourceInside s)
    (hb : t.boxes = slide.boxes) (he : r.entry ∉ t.boxes) :
    ∀ i, 2 ≤ (slide.cell i).1.val ∧ (slide.cell i).2.val < r.height := by
  have hlast := slide_last_inside_or_entry r slide hk hpre hs
  have hlastInside : 2 ≤ (slide.cell ⟨n + k, by omega⟩).1.val ∧
      (slide.cell ⟨n + k, by omega⟩).2.val < r.height := by
    rcases hlast with hi | hentry
    · exact hi
    · apply False.elim
      apply he
      rw [hb, ← hentry]
      apply Finset.mem_union_right
      refine Finset.mem_image.mpr ⟨⟨n - 1, by omega⟩, Finset.mem_univ _, ?_⟩
      congr 1
      apply Fin.ext
      change k + (n - 1) + 1 = n + k
      omega
  intro i
  have hip := slide.position i
  have hil := slide.lane i
  have hep := slide.position ⟨n + k, by omega⟩
  have hel := slide.lane ⟨n + k, by omega⟩
  have hsx := hs.1
  have hsy := hs.2
  cases d <;> simp only [Direction.position, Direction.lane] at hip hil hep hel <;> omega

end PushPuzzle.PushPush.CornerDock
