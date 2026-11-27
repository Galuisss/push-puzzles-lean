/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortEndpointLocality
import all PushS.PortEndpointLocality
import all PushS.PortCoreCrossing
import all PushS.PortSignalLocality

/-! Every local hole has an actual original port axis as its owner. -/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS

/-- Away from the frame and permanent markers, an actual hole stays within one last branch
length plus twelve of an actual port axis. -/
theorem encodedSegments_hole_axis_locality (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (state : SignalState)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state))
    (hf : q ∉ Boundary.frame) :
    q ∈ l.centralMarkers p ∨ q ∈ l.wideSeparatorHoles p ∨
      ∃ i < l.portCount, Nat.dist q.1.val (p.x i) ≤ p.L p.levels + 12 := by
  rcases encoded_sources l p hl hM state hq hf with hc | hw | ⟨e, he, hq⟩ | ⟨kind, first, hg, hq⟩
  · exact Or.inl hc
  · exact Or.inr (Or.inl hw)
  · exact Or.inr (Or.inr ⟨e.port, l.endpoints_port_lt hl he, endpoint_source_near l p state e hq⟩)
  · right; right
    refine ⟨first + 1, gate_middle_lt l hl hg, ?_⟩
    have hs : p.x (first + 1) - 2 ≤ q.1.val ∧ q.1.val ≤ p.x (first + 1) + 12 := by
      rcases hq with hq | ⟨internal, hq⟩
      · exact gate_fixed_span p _ hq
      · exact gate_signal_span p state kind first internal hq
    simp only [Nat.dist]
    omega

/-- Cells far from every original axis are full unless they are an actual permanent marker. -/
theorem encodedSegments_far_from_axes_full (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (state : SignalState)
    (s : State (p.W + 1) (p.H + 1))
    (hs : PushS.holes s = SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state))
    {q : Cell (p.W + 1) (p.H + 1)} (hf : q ∉ Boundary.frame) (hc : q ∉ l.centralMarkers p)
    (hw : q ∉ l.wideSeparatorHoles p)
    (hx : ∀ i < l.portCount, p.L p.levels + 12 < Nat.dist q.1.val (p.x i)) : q ∈ s.boxes := by
  by_contra hbox
  have hh : q ∈ PushS.holes s := (mem_holes _).mpr hbox
  rw [hs] at hh
  rcases l.encodedSegments_hole_axis_locality p hl hM state hh hf with hc' | hw' | ⟨i, hi, hnear⟩
  · exact hc hc'
  · exact hw hw'
  · have hfar := hx i hi
    omega

end PushPuzzle.PushS.PortLayout
