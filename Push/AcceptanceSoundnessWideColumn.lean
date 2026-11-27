/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessPageFreeze
public import PushS.PortWideFreeze
import all PushS.PortWideFreeze
import all PushS.PortSignalLocality
import all PushS.PortSegments
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceProgram

/-! A far wide-separator column cannot acquire a new endpoint hole anywhere in its interior. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

theorem canonical_filled_frame_empty (l : PortLayout) (p : Scales.Parameters) (target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    Disjoint (Blocked.fill t (l.centralMarkers p)).boxes Boundary.frame := by
  apply Finset.disjoint_left.mpr
  intro q hq hf
  rcases Finset.mem_union.mp hq with hb | hc
  · exact Finset.disjoint_left.mp (program_frame_empty l p target ha) hb hf
  · exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hc).1).2 hf

private theorem wide_column_far_exits (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {g q : Cell (p.W + 1) (p.H + 1)} (hg : g ∈ l.wideSeparatorHoles p) (hx : q.1 = g.1) :
    ∀ a ∈ Support.frameExits (l.streetColumnSet p) (l.workingRowSet p),
      (PushS.holes (Blocked.fill (l.canonicalInstance p hl hM haxes initial target).initial
        (l.centralMarkers p)) \ Boundary.frame).card < distance a q := by
  have hb : (PushS.holes (Blocked.fill (l.canonicalInstance p hl hM haxes initial target).initial
      (l.centralMarkers p)) \ (Boundary.frame : Finset (Cell (p.W + 1) (p.H + 1)))).card ≤ 2 * p.b p.levels :=
    filled_interior_budget l p hl haxes (l.canonical initial) _
      (canonical_initial_holes l p hl hM haxes initial target)
  have hgaps := l.wideSeparatorHoles_street_gap p hl hg
  have hleft := hgaps (⟨0, by omega⟩ : Fin (p.W + 1)) (by
    change 0 ∈ streetColumns l (coordinates p)
    simp [streetColumns])
  have hright := hgaps (⟨p.W, by omega⟩ : Fin (p.W + 1)) (by
    change p.W ∈ streetColumns l (coordinates p)
    simp [streetColumns, coordinates])
  have hqx := q.1.isLt
  rw [← hx] at hleft hright
  have hfar : ∀ a ∈ Support.frameExits (l.streetColumnSet p) (l.workingRowSet p),
      2 * p.b p.levels + 2 < distance a q := by
    apply Support.frameExits_far_of_column_gap
    · simp only [Nat.dist] at hleft
      omega
    · simp only [Nat.dist] at hright
      omega
    · intro x hstreet
      have hd := hgaps x hstreet
      rw [← hx] at hd
      exact Nat.dist_comm _ _ ▸ hd
  intro a ha
  exact (hb.trans (by omega)).trans_lt (hfar a ha)

/-- Any accepted endpoint hole on a wide separator's column was already a source hole in that same physical cell. -/
private theorem canonical_wide_column_hole_source (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {g q : Cell (p.W + 1) (p.H + 1)} (hg : g ∈ l.wideSeparatorHoles p) (hx : q.1 = g.1)
    (hq : q ∈ PushS.holes t) (hf : q ∉ Boundary.frame) :
    q ∈ PushS.holes (l.canonicalInstance p hl hM haxes initial target).initial := by
  by_cases hc : q ∈ l.centralMarkers p
  · exact (congrArg (fun E : Finset (Cell (p.W + 1) (p.H + 1)) => q ∈ E)
      (canonical_initial_holes l p hl hM haxes initial target)).mpr (l.centralMarkers_subset_encoded p _ hc)
  · have hpath := canonical_central_fill_between l p hl hM haxes initial target .refl hr .refl ha
    have hsupp := canonical_central_filled_supported_at l p hl hM haxes initial target hr .refl ha
    have hfilled : q ∈ PushS.holes (Blocked.fill t (l.centralMarkers p)) := by
      exact (PushS.mem_holes _).mpr (fun hb => (Finset.mem_union.mp hb).elim ((PushS.mem_holes _).mp hq) hc)
    have hsource := Support.hole_at_of_frame_exits (l.streetColumnSet_separated p)
      (l.workingRowSet_separated p) .refl hpath
      (canonical_initial_frame l p hl hM haxes initial target) (canonical_filled_frame_empty l p target ha)
      hsupp hf (wide_column_far_exits l p hl hM haxes initial target hg hx) hfilled
    exact (PushS.mem_holes _).mpr (fun hb => (PushS.mem_holes _).mp hsource (Finset.mem_union_left _ hb))

/-- The complete accepted stock on a wide separator column is contained in its canonical fixed target stock. -/
theorem canonical_wide_column_target_stock (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {g q : Cell (p.W + 1) (p.H + 1)} (hg : g ∈ l.wideSeparatorHoles p) (hx : q.1 = g.1)
    (hq : q ∈ PushS.holes t) (hf : q ∉ Boundary.frame) : q ∈ targetHoles l p target := by
  have hsource := canonical_wide_column_hole_source l p hl hM haxes initial target hr ha hg hx hq hf
  have henc : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p (l.canonical initial)) :=
    (congrArg (fun E : Finset (Cell (p.W + 1) (p.H + 1)) => q ∈ E)
      (canonical_initial_holes l p hl hM haxes initial target)).mp hsource
  obtain ⟨seg, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp henc
  rcases List.mem_append.mp hs with hfixed | hsignal
  · exact (SegmentRecipe.mem_holes _ q).mpr ⟨seg, List.mem_append_left _ hfixed, hc⟩
  · have hpoint := (SegmentRecipe.mem_pointHoles _ (q.1.val, q.2.val)).mpr ⟨seg, hsignal, hc⟩
    obtain ⟨i, hi, hnear⟩ := l.signalSegments_near_axis p hl (l.canonical initial) hpoint
    have hstreet : (⟨p.x i, by have := x_add_readLength_lt_W p (hi.trans_le haxes) 0; omega⟩ : Fin (p.W + 1)) ∈
        l.streetColumnSet p := by
      change p.x i ∈ streetColumns l (coordinates p)
      exact axis_in_streetColumns l p hi
    have hgap := l.wideSeparatorHoles_street_gap p hl hg _ hstreet
    rw [← hx] at hgap
    change 2 * p.b p.levels + 2 < Nat.dist q.1.val (p.x i) at hgap
    change Nat.dist q.1.val (p.x i) ≤ 12 at hnear
    have hb : 10 ≤ p.b p.levels := by
      have hm := Nat.mul_le_mul_right (p.Y p.levels + p.L p.levels + 10)
        (show 1 ≤ 8 * (p.axes + 1) by omega)
      simp only [Nat.one_mul] at hm
      unfold Scales.Parameters.b
      omega
    exact False.elim (by omega)

end PushPuzzle.Push.AcceptanceSoundness
