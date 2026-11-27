/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessFrame
public import PushS.PortAxisFixed
public import PushS.PortHoleBudget
public import PushS.PortCentralStrip
import all PushS.PortCentralStrip
import all PushS.Scales

/-! The actual accepted trajectory keeps every principal-axis central crossing occupied and unvisited. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushFS.Reduction PushS PushS.PortLayout AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include haxes in
private theorem main_central_margins {i : ℕ} (hi : i < l.portCount) : p.D ≤ p.x i ∧ p.x i + p.D ≤ p.W := by
  have hp := hi.trans_le haxes
  constructor
  · simpa only [Scales.Parameters.x, Nat.one_mul] using Nat.mul_le_mul_right p.D (show 1 ≤ i + 1 by omega)
  · have h := Nat.mul_le_mul_right p.D (show i + 1 + 1 ≤ p.axes + 1 by omega)
    simpa only [Scales.Parameters.x, Scales.Parameters.W, Nat.add_mul, Nat.one_mul] using h

private theorem main_central_far {i : ℕ} (hi : i < l.portCount) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = p.x i) (hy : p.D ≤ q.2.val + 4 ∧ q.2.val ≤ p.D + 4) : Distant.Far (I).initial q := by
  have margins := main_central_margins l p haxes hi
  have initialHoles : (holes (I).initial : Finset (Cell (p.W + 1) (p.H + 1))) =
      SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p (l.canonical initial)) :=
    l.physicalInstance_initial_holes p hl hM haxes (l.canonical initial) (l.canonical target)
  exact l.far_of_central_margins p hl haxes (l.canonical initial) (I).initial initialHoles q
    (by omega) (by omega) hy.1 hy.2

private theorem main_central_initial_full {i : ℕ} (hi : i < l.portCount) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = p.x i) (hy : p.D ≤ q.2.val + 4 ∧ q.2.val ≤ p.D + 4) : q ∈ (I).initial.boxes := by
  have margins := main_central_margins l p haxes hi
  have hD := readDepth_add_lt_D p 1
  have hH : p.H = 2 * p.D := rfl
  have hlast := last_depth_margin p
  have hframe : q ∉ Boundary.frame := by
    simp only [Boundary.frame, Boundary.edge, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hmarker : q ∉ l.centralMarkers p := by
    intro marker
    have fixed := (Finset.mem_sdiff.mp (Finset.mem_filter.mp marker).1).1
    obtain ⟨s, hs, contains⟩ := (SegmentRecipe.mem_holes _ q).mp fixed
    have point : (q.1.val, q.2.val) ∈ SegmentRecipe.pointHoles (l.fixedSegments p) :=
      (SegmentRecipe.mem_pointHoles _ _).mpr ⟨s, hs, contains⟩
    have location := l.fixedSegments_on_main_axis p hl hM haxes hi point hx
    omega
  exact l.physicalInstance_central_strip_full p hl hM haxes (l.canonical initial) (l.canonical target)
    hframe hmarker (by omega) (by omega)

/-- Every actual principal-axis crossing in the central band stays occupied on accepted source play. -/
theorem canonical_main_central_occupied {i : ℕ} (hi : i < l.portCount) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = p.x i) (hy : p.D ≤ q.2.val + 4 ∧ q.2.val ≤ p.D + 4)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t)) : q ∈ u.boxes :=
  Distant.box_at hsu hut (l.physicalInstance_initial_frame p hl hM haxes (l.canonical initial) (l.canonical target))
    (program_frame_empty l p target accepted) (main_central_far l p hl hM haxes initial target hi hx hy)
    (main_central_initial_full l p hl hM haxes initial target hi hx hy)

/-- No actual accepted prefix player visits any principal-axis central crossing. -/
theorem canonical_main_central_unvisited {i : ℕ} (hi : i < l.portCount) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = p.x i) (hy : p.D ≤ q.2.val + 4 ∧ q.2.val ≤ p.D + 4)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t)) : u.player ≠ q :=
  Distant.player_ne hsu (l.physicalInstance_initial_frame p hl hM haxes (l.canonical initial) (l.canonical target))
    (canonical_frame_empty_at l p hl hM haxes initial target hut accepted)
    (main_central_far l p hl hM haxes initial target hi hx hy)

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
