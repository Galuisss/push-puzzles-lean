/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessCentralSamples
import all Push.AcceptanceSoundnessCentralGeometry
import all PushS.PortInstance
import all PushS.PortSegments

/-! Actual acceptance permanently protects the four new marker rows and permits filling them. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

/-- The actual added flank, far-guard, and independent sample markers, excluding the old central cut. -/
def newCentralMarkers (l : PortLayout) (p : Scales.Parameters) : Finset (Cell (p.W + 1) (p.H + 1)) :=
  (l.centralMarkers p).filter fun q => q.2.val ≠ p.D

theorem newCentralMarkers_subset (l : PortLayout) (p : Scales.Parameters) :
    newCentralMarkers l p ⊆ l.centralMarkers p := Finset.filter_subset _ _

/-- Acceptance of the literal program forces every newly added marker to be a final hole. -/
theorem newCentralMarkers_terminal (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {B : Board (p.W + 1) (p.H + 1)} {cap : Option ℕ} {s t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable B cap s t) (hp : s.player ∈ Boundary.frame) (hs : PushS.holes s = targetHoles l p initial)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    newCentralMarkers l p ⊆ PushS.holes t := by
  intro q hq
  obtain ⟨hq, hcut⟩ := Finset.mem_filter.mp hq
  rcases central_sources l p hq with h | h | h | ⟨h, _⟩ | ⟨h, _⟩
  · exact (hcut h).elim
  · apply flank_markers_terminal l p hl hM haxes initial target hr hp hs ha
    exact Finset.mem_filter.mpr ⟨hq, Finset.mem_insert.mpr (Or.inl h)⟩
  · apply flank_markers_terminal l p hl hM haxes initial target hr hp hs ha
    exact Finset.mem_filter.mpr ⟨hq, Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h))⟩
  · exact guard_markers_terminal l p hl hM haxes initial target hr hp hs ha (Finset.mem_filter.mpr ⟨hq, h⟩)
  · exact sample_markers_terminal l p hl hM haxes initial target hr hp hs ha (Finset.mem_filter.mpr ⟨hq, h⟩)

/-- Every newly added marker stays empty and excludes the player on every actual successful prefix. -/
theorem newCentralMarkers_excluded_at (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {B : Board (p.W + 1) (p.H + 1)} {cap : Option ℕ} {s u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable B cap s u) (hut : Reachable B cap u t) (hp : s.player ∈ Boundary.frame)
    (hs : PushS.holes s = targetHoles l p initial)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    Blocked.Excluded (newCentralMarkers l p) u := by
  apply Distant.excluded_at hsu hut hp (program_frame_empty l p target ha)
  · intro q hq
    exact l.centralMarkers_far p hl haxes (l.canonical initial) s hs q (newCentralMarkers_subset l p hq)
  · exact newCentralMarkers_terminal l p hl hM haxes initial target (hsu.trans hut) hp hs ha

private theorem canonical_initial_frame (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool) :
    (l.canonicalInstance p hl hM haxes initial target).initial.player ∈ Boundary.frame :=
  l.physicalInstance_initial_frame p hl hM haxes (l.canonical initial) (l.canonical target)

private theorem canonical_initial_holes (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool) :
    PushS.holes (l.canonicalInstance p hl hM haxes initial target).initial = targetHoles l p initial :=
  l.physicalInstance_initial_holes p hl hM haxes (l.canonical initial) (l.canonical target)

/-- Filling the new marker holes preserves every segment of the actual accepted physical play. -/
theorem canonical_newCentralMarkers_fill_between (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (huv : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u v)
    (hvt : Reachable (l.canonicalInstance p hl hM haxes initial target).board none v t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (Blocked.fill u (newCentralMarkers l p)) (Blocked.fill v (newCentralMarkers l p)) := by
  apply Blocked.reachable_fill_of_invariant (fun {_ _} h => h) huv
    (fun _ hux hxv => newCentralMarkers_excluded_at l p hl hM haxes initial target
      (hsu.trans hux) (hxv.trans hvt) (canonical_initial_frame l p hl hM haxes initial target)
      (canonical_initial_holes l p hl hM haxes initial target) ha)
  rw [(l.canonicalInstance p hl hM haxes initial target).walls_empty]
  exact Finset.disjoint_empty_right _

/-- The new acceptance markers can be projected back to ordinary boxes along the whole real play. -/
theorem canonical_newCentralMarkers_fill (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (Blocked.fill (l.canonicalInstance p hl hM haxes initial target).initial (newCentralMarkers l p))
      (Blocked.fill t (newCentralMarkers l p)) :=
  canonical_newCentralMarkers_fill_between l p hl hM haxes initial target .refl hr .refl ha

end PushPuzzle.Push.AcceptanceSoundness
