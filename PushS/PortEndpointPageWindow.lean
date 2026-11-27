/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.PortEndpointLocality
import all PushS.PortEndpointLocality
import all PushS.PortEndpointWide
import all PushS.PortEndpointCrossing
import all PushS.PortCoreCrossing
import all PushS.PortFixedSeparation
import all PushS.PortCentralStrip
import all PushS.PortWideGeometry
import all PushS.PortSegments

/-! Exact endpoint hole identification throughout its physical page and the global last-level radius. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

/-- The interior of an endpoint's physical page within the global last branch radius. -/
@[expose] def endpointPageWindow (p : Scales.Parameters) (e : Endpoint) :
    Set (Cell (p.W + 1) (p.H + 1)) :=
  {q | (if e.side = .upper then 0 < q.2.val ∧ q.2.val + 32 < p.D
      else p.D + 32 < q.2.val ∧ q.2.val < p.H) ∧
    Nat.dist q.1.val (p.x e.port) ≤ p.L p.levels + 16}

/-- Actual selected working rows and the global horizontal margin lie inside the page window. -/
theorem endpointPageWindow_of_workingDepth (l : PortLayout) (p : Scales.Parameters) (e : Endpoint)
    {v : ℕ} (hv : v ∈ l.workingDepthCoordinates p) (q : Cell (p.W + 1) (p.H + 1))
    (hy : q.2.val = if e.side = .upper then v else p.H - v)
    (hx : Nat.dist q.1.val (p.x e.port) ≤ p.L p.levels + 16) : q ∈ endpointPageWindow p e := by
  have hpos := workingDepth_positive l p hv
  have hmax := workingRows_le_last l p hv
  have hD := last_depth_margin p
  have hH : p.H = 2 * p.D := rfl
  refine ⟨?_, hx⟩
  cases hs : e.side <;> simp only [hs, reduceCtorEq, ite_true, ite_false] at hy ⊢ <;> omega

private theorem page_window_not_central (l : PortLayout) (p : Scales.Parameters) (e : Endpoint)
    {q : Cell (p.W + 1) (p.H + 1)} (hw : q ∈ endpointPageWindow p e) : q ∉ l.centralMarkers p := by
  intro hc
  have hy := (Finset.mem_filter.mp hc).2
  have hpage := hw.1
  split at hpage <;> omega

private theorem page_window_not_frame (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (ha : l.portCount ≤ p.axes) (e : Endpoint) (he : e ∈ l.endpoints)
    {q : Cell (p.W + 1) (p.H + 1)} (hw : q ∈ endpointPageWindow p e) : q ∉ Boundary.frame := by
  have hx0 := readLength_add_lt_x p e.port p.levels
  have hxW := x_add_readLength_lt_W p ((l.endpoints_port_lt hl he).trans_le ha) p.levels
  rw [readLength_eq p p.levels_pos le_rfl] at hx0 hxW
  have hx := hw.2
  simp only [Nat.dist] at hx
  have hy := hw.1
  have hH : p.H = 2 * p.D := rfl
  intro hf
  obtain ⟨d, hd⟩ := (Boundary.mem_frame q).mp hf
  cases d <;> simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and] at hd
  all_goals split at hy <;> omega

private theorem page_window_not_wide (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (ha : l.portCount ≤ p.axes) (e : Endpoint) (he : e ∈ l.endpoints)
    {q : Cell (p.W + 1) (p.H + 1)} (hw : q ∈ endpointPageWindow p e) : q ∉ l.wideSeparatorHoles p := by
  have hi := l.endpoints_port_lt hl he
  have hm := x_add_readLength_lt_W p (show e.port < p.axes by omega) 0
  let col : Fin (p.W + 1) := ⟨p.x e.port, by omega⟩
  have hc : col ∈ l.streetColumnSet p := axis_in_streetColumns l p hi
  intro hwide
  have hfar := l.wideSeparatorHoles_street_gap p hl hwide col hc
  have hb := local_radius_budget p p.levels
  rw [readLength_eq p p.levels_pos le_rfl] at hb
  have hnear := hw.2
  change 2 * p.b p.levels + 2 < Nat.dist q.1.val (p.x e.port) at hfar
  omega

private theorem page_window_axis_eq (p : Scales.Parameters) (e : Endpoint)
    {q : Cell (p.W + 1) (p.H + 1)} (hw : q ∈ endpointPageWindow p e) (i : ℕ)
    (hi : Nat.dist q.1.val (p.x i) ≤ p.L p.levels + 12) : i = e.port := by
  apply nearby_axis_eq p hw.2
  simp only [Nat.dist] at hi
  omega

private theorem page_window_owner (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (state : SignalState) (e f : Endpoint) (he : e ∈ l.endpoints) (hf : f ∈ l.endpoints)
    {q : Cell (p.W + 1) (p.H + 1)} (hw : q ∈ endpointPageWindow p e)
    (hq : (q.1.val, q.2.val) ∈ pointHoles (endpointFixedSegments l (coordinates p) f) ∨
      (q.1.val, q.2.val) ∈ pointHoles (endpointSegments (coordinates p) state f)) : f = e := by
  have hport := page_window_axis_eq p e hw f.port (endpoint_source_near l p state f hq)
  have hside : f.side = e.side := by
    by_contra hne
    have hp := hw.1
    have hfpage := hq.elim (fixed_endpoint_page l p f) (signal_endpoint_page p state f)
    cases hes : e.side <;> cases hfs : f.side <;>
      simp_all only [reduceCtorEq, ite_true, ite_false] <;> omega
  exact l.endpoints_key_injective hl hf he hside hport

private theorem page_window_not_gate (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (state : SignalState) (e : Endpoint) (he : e ∈ l.endpoints)
    {kind : Shuttle.Kind} {first : ℕ} (hg : .gate kind first ∈ l.lowerGroups)
    {q : Cell (p.W + 1) (p.H + 1)} (hw : q ∈ endpointPageWindow p e)
    (hq : (q.1.val, q.2.val) ∈ pointHoles (gateFixedSegments (coordinates p) (first + 1)) ∨
      ∃ internal, (q.1.val, q.2.val) ∈ pointHoles (gateSegments (coordinates p) state kind first internal)) : False := by
  have hspan : p.x (first + 1) - 2 ≤ q.1.val ∧ q.1.val ≤ p.x (first + 1) + 12 := by
    rcases hq with h | ⟨internal, h⟩
    · exact gate_fixed_span p _ h
    · exact gate_signal_span p state kind first internal h
  have hpage : p.D + 32 < q.2.val := by
    rcases hq with h | ⟨internal, h⟩
    · exact gate_fixed_page p _ h
    · exact gate_signal_page p state kind first internal h
  have hport : first + 1 = e.port := page_window_axis_eq p e hw (first + 1) (by
    simp only [Nat.dist]
    omega)
  cases hs : e.side with
  | upper => have hp := hw.1; simp only [hs, ite_true] at hp; omega
  | lower => exact l.endpoints_lower_ne_gate_middle hl hg he hs hport.symm

/-- Throughout its actual page window, the complete emitter has exactly this endpoint's
original fixed and signal holes. -/
theorem encodedSegments_endpointPageWindow (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) (e : Endpoint) (he : e ∈ l.endpoints)
    (q : Cell (p.W + 1) (p.H + 1)) (hw : q ∈ endpointPageWindow p e) :
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) ↔
      q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1)
        (endpointFixedSegments l (coordinates p) e ++ endpointSegments (coordinates p) state e) := by
  constructor
  · intro hq
    rcases encoded_sources l p hl hM state hq (page_window_not_frame l p hl ha e he hw) with
      hc | hw' | hsource
    · exact False.elim (page_window_not_central l p e hw hc)
    · exact False.elim (page_window_not_wide l p hl ha e he hw hw')
    · rcases hsource with ⟨f, hf, hsource⟩ | ⟨kind, first, hg, hsource⟩
      · have hfe := page_window_owner l p hl state e f he hf hw hsource
        subst f
        apply (SegmentRecipe.mem_holes _ q).mpr
        apply (mem_pointHoles _ _).mp
        simpa only [pointHoles_append, Finset.mem_union] using hsource
      · exact False.elim (page_window_not_gate l p hl state e he hg hw hsource)
  · exact fun hq => endpoint_holes_subset_encoded l p hl hM state e he hq

end PushPuzzle.PushS.PortLayout
