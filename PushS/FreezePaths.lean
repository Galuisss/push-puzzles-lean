/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Closure

/-! Finite straight paths ending at a known blocker certify freezing rays. -/

public section

namespace PushPuzzle.PushS.Freeze


open PushFS

/-- A finite straight path through full cells or earlier blockers reaches a known blocker. -/
theorem Ray.of_path {w h n : ℕ} {S G : Finset (Cell w h)} {d : Direction}
    (cell : Fin (n + 2) → Cell w h)
    (ha : ∀ i : Fin (n + 1), Adjacent d (cell i.castSucc) (cell i.succ))
    (hm : ∀ i : Fin n, cell ⟨i.val + 1, by omega⟩ ∈ S ∨ cell ⟨i.val + 1, by omega⟩ ∈ G)
    (he : cell ⟨n + 1, by omega⟩ ∈ G) : Ray S G d (cell 0) := by
  induction n with
  | zero => exact .hit (ha 0) he
  | succ n ih =>
    rcases hm 0 with hfull | hblock
    · refine .extend (ha 0) hfull ?_
      apply ih (fun i => cell i.succ)
      · intro i
        exact ha i.succ
      · intro i
        exact hm i.succ
      · exact he
    · exact .hit (ha 0) hblock

/-- A horizontal interval of full cells ending at a blocker gives an eastward ray. -/
theorem Ray.east_of_interval {w h : ℕ} {S G : Finset (Cell w h)} {q g : Cell w h}
    (hy : q.2 = g.2) (hx : q.1.val < g.1.val) (hg : g ∈ G)
    (hm : ∀ r : Cell w h, r.2 = q.2 → q.1.val < r.1.val → r.1.val < g.1.val → r ∈ S ∨ r ∈ G) :
    Ray S G .east q := by
  let n := g.1.val - q.1.val - 1
  let path : Fin (n + 2) → Cell w h := fun i =>
    (⟨q.1.val + i.val, by have := i.isLt; have := g.1.isLt; dsimp only [n] at *; omega⟩, q.2)
  have hstart : path 0 = q := Prod.ext (Fin.ext (by simp [path])) rfl
  rw [← hstart]
  apply Ray.of_path path
  · intro i
    exact ⟨by simp only [path, Fin.val_succ, Fin.val_castSucc]; omega, rfl⟩
  · intro i
    apply hm (path ⟨i.val + 1, by omega⟩) rfl
    · dsimp only [path]; omega
    · have := i.isLt; dsimp only [path, n] at *; omega
  · convert hg using 1
    apply Prod.ext
    · apply Fin.ext
      change q.1.val + (n + 1) = g.1.val
      dsimp only [n]; omega
    · exact hy

/-- A horizontal interval of full cells ending at a blocker gives a westward ray. -/
theorem Ray.west_of_interval {w h : ℕ} {S G : Finset (Cell w h)} {q g : Cell w h}
    (hy : q.2 = g.2) (hx : g.1.val < q.1.val) (hg : g ∈ G)
    (hm : ∀ r : Cell w h, r.2 = q.2 → g.1.val < r.1.val → r.1.val < q.1.val → r ∈ S ∨ r ∈ G) :
    Ray S G .west q := by
  let n := q.1.val - g.1.val - 1
  let path : Fin (n + 2) → Cell w h := fun i =>
    (⟨q.1.val - i.val, by have := q.1.isLt; omega⟩, q.2)
  have hstart : path 0 = q := Prod.ext (Fin.ext (by simp [path])) rfl
  rw [← hstart]
  apply Ray.of_path path
  · intro i
    refine ⟨?_, rfl⟩
    have := i.isLt
    dsimp only [path, n] at *
    simp only [Fin.val_succ, Fin.val_castSucc]
    omega
  · intro i
    apply hm (path ⟨i.val + 1, by omega⟩) rfl
    · have := i.isLt; dsimp only [path, n] at *; omega
    · have := i.isLt; dsimp only [path, n] at *; omega
  · convert hg using 1
    apply Prod.ext
    · apply Fin.ext
      change q.1.val - (n + 1) = g.1.val
      dsimp only [n]; omega
    · exact hy

/-- Enlarging the full region preserves every certified finite ray. -/
theorem Ray.mono_full {w h : ℕ} {S T G : Finset (Cell w h)} {d : Direction} {p : Cell w h}
    (hST : S ⊆ T) (hr : Ray S G d p) : Ray T G d p := by
  induction hr with
  | hit ha hg => exact .hit ha hg
  | extend ha hs _ ih => exact .extend ha (hST hs) ih

/-- A finite union of regions anchored to the same blockers is anchored to those blockers. -/
theorem Anchored.biUnion {w h : ℕ} {α : Type} (s : Finset α)
    (f : α → Finset (Cell w h)) {G : Finset (Cell w h)}
    (hs : ∀ i ∈ s, Anchored (f i) G) : Anchored (s.biUnion f) G := by
  intro d p hp
  obtain ⟨i, hi, hpi⟩ := Finset.mem_biUnion.mp hp
  have hsub : f i ⊆ s.biUnion f := fun q hq => Finset.mem_biUnion.mpr ⟨i, hi, hq⟩
  exact (hs i hi d p hpi).imp (fun hr => hr.mono_full hsub) (fun hr => hr.mono_full hsub)

/-- Enlarging the known blocker set preserves every certified finite ray. -/
theorem Ray.mono_blockers {w h : ℕ} {S G H : Finset (Cell w h)} {d : Direction} {p : Cell w h}
    (hGH : G ⊆ H) (hr : Ray S G d p) : Ray S H d p := by
  induction hr with
  | hit ha hg => exact .hit ha (hGH hg)
  | extend ha hs _ ih => exact .extend ha hs ih

/-- An anchored full region remains anchored after adding more established blockers. -/
theorem Anchored.mono_blockers {w h : ℕ} {S G H : Finset (Cell w h)}
    (ha : Anchored S G) (hGH : G ⊆ H) : Anchored S H := by
  intro d p hp
  exact (ha d p hp).elim (fun h => Or.inl (h.mono_blockers hGH))
    (fun h => Or.inr (h.mono_blockers hGH))

/-- A concrete closure remains valid after adding more initial geometric blockers. -/
theorem Closure.enlarge_blockers {w h : ℕ} {s : State w h} {G R H : Finset (Cell w h)}
    (hc : Closure s G R) (hGH : G ⊆ H) : Closure s H (H ∪ R) := by
  induction hc with
  | refl => simpa only [Finset.union_eq_left.mpr hGH] using (Closure.refl H : Closure s H H)
  | add previous hfull hanchor ih =>
    have ha := hanchor.mono_blockers (fun _ h => Finset.mem_union_right H h)
    simpa only [Finset.union_assoc] using Closure.add ih hfull ha

/-- Adjoining the same established blockers to both ends preserves a closure. -/
theorem Closure.adjoin_blockers {w h : ℕ} {s : State w h} {G R : Finset (Cell w h)}
    (hc : Closure s G R) (H : Finset (Cell w h)) : Closure s (G ∪ H) (R ∪ H) := by
  have hsub : G ⊆ R := by
    induction hc with
    | refl => exact Finset.Subset.refl _
    | add _ _ _ ih => exact Finset.Subset.trans ih Finset.subset_union_left
  have heq : ((G ∪ H) ∪ R : Finset (Cell w h)) = R ∪ H := by
    rw [Finset.union_right_comm, Finset.union_eq_right.mpr hsub]
  exact heq ▸ hc.enlarge_blockers Finset.subset_union_left

end PushPuzzle.PushS.Freeze
