/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushFS.Isometry
public import PushFS.StaticPlacement

/-! A complete neighboring collar is invariant under actual grid isometries. -/

@[expose] public section
namespace PushPuzzle.PushFS

private theorem Interior.of_neighbor_exists {W H : ℕ} {p : Cell W H}
    (hp : ∀ d, ∃ q, Adjacent d p q) : Interior p := by
  obtain ⟨n,hn⟩ := hp .north
  obtain ⟨e,he⟩ := hp .east
  obtain ⟨s,hs⟩ := hp .south
  obtain ⟨w,hw⟩ := hp .west
  have hex := e.1.isLt
  have hsy := s.2.isLt
  simp only [Adjacent] at hn he hs hw
  unfold Interior
  omega

theorem GridIsometry.interior {w h W H : ℕ} (e : GridIsometry w h W H)
    {p : Cell w h} (hp : Interior p) : Interior (e.cells p) := by
  apply Interior.of_neighbor_exists
  intro d
  obtain ⟨q,hq⟩ := hp.neighbor_exists (e.directions.symm d)
  refine ⟨e.cells q,?_⟩
  simpa only [Equiv.apply_symm_apply] using (e.adjacent _ _ _).mpr hq

end PushPuzzle.PushFS
