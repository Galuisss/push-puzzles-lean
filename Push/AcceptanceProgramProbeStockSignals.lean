/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramProbeStockCells
public import PushS.PortFixedSeparation
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProbePartners
import all PushS.PortSegments
import all PushS.PortEndpointCounts
import all PushS.PortEndpointSeparation
import all PushS.PortCoreCrossing
import all PushS.PortWireGeometry
import all PushS.PortLayoutCoordinates

/-! On actual upper Y+2 probe rows, all signal holes are precisely their true principal-axis bits. -/

public section
namespace PushPuzzle.PushS.PortLayout

open PushFS PushFS.Reduction SegmentRecipe Push.AcceptanceProgram

private theorem probe_row_data (l : PortLayout) (p : Scales.Parameters) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q.2.val ∈ probeRows l p) :
    ∃ e ∈ l.endpoints, e.side = .upper ∧ q.2.val = p.Y e.level + 2 := by
  obtain ⟨e, he, hy⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
  obtain ⟨he, hs⟩ := List.mem_filter.mp he
  exact ⟨e, he, by simpa only [beq_iff_eq] using hs, hy.symm⟩

private theorem signal_probe_endpoint (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (state : SignalState)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q.2.val ∈ probeRows l p)
    (hsig : (q.1.val, q.2.val) ∈ pointHoles (l.signalSegments p state)) :
    ∃ e ∈ l.endpoints, e.side = .upper ∧ q.1.val = p.x e.port ∧
      q.2.val = p.Y e.level + 2 ∧ state.axes.getD e.port false = true := by
  obtain ⟨ref, href, _, hyref⟩ := probe_row_data l p hq
  obtain ⟨hr0, hrM⟩ := l.endpoints_level_bounds p hl hM href
  have hrD := readDepth_add_lt_D p ref.level
  rw [readDepth_eq p hr0 hrM] at hrD
  obtain ⟨s, hs, hc⟩ := (mem_pointHoles _ _).mp hsig
  rcases List.mem_append.mp hs with hs | hs
  · obtain ⟨e, he, hs⟩ := List.mem_flatMap.mp hs
    obtain ⟨hj, hjM⟩ := l.endpoints_level_bounds p hl hM he
    have hband := acceptanceEndpointSignalBand p state e ((mem_pointHoles _ _).mpr ⟨s, hs, hc⟩)
    rw [readDepth_eq p hj hjM] at hband
    cases hside : e.side with
    | lower =>
      have heD := readDepth_add_lt_D p e.level
      rw [readDepth_eq p hj hjM] at heD
      have hh : p.H = 2 * p.D := rfl
      simp only [hside, reduceCtorEq, ite_false] at hband
      omega
    | upper =>
      simp only [hside, ite_true] at hband
      have hlevel : e.level = ref.level := by
        rcases lt_trichotomy e.level ref.level with hlt | heq | hlt
        · have hg := depth_gap p hj hlt hrM
          rw [readDepth_eq p hj hjM, readDepth_eq p hr0 hrM] at hg
          omega
        · exact heq
        · have hg := depth_gap p hr0 hlt hjM
          rw [readDepth_eq p hr0 hrM, readDepth_eq p hj hjM] at hg
          omega
      have hy : q.2.val = p.Y e.level + 2 := hlevel ▸ hyref
      dsimp only [endpointSegments] at hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · have hc := vertical_coordinates hc
        have hcoord : (coordinates p).x = p.x := rfl
        have hdepth : (coordinates p).depth e.level = readDepth p e.level := rfl
        simp only [hside, onSide, ite_true, hcoord, hdepth, readDepth_eq p hj hjM] at hc
        refine ⟨e, he, hside, hc.1, hy, ?_⟩
        cases hb : state.axes.getD e.port false
        · simp only [hb, Bool.toNat_false, Nat.add_zero] at hc
          omega
        · rfl
      · have hc := horizontal_coordinates hc
        have hdepth : (coordinates p).depth e.level = readDepth p e.level := rfl
        simp only [hside, onSide, ite_true, hdepth, readDepth_eq p hj hjM] at hc
        omega
  · obtain ⟨g, _, hs⟩ := List.mem_flatMap.mp hs
    cases hk : g.gate with
    | none => simp only [tripleSignal, hk, Option.elim_none, List.not_mem_nil] at hs
    | some kind =>
      have hg := gate_signal_page p state kind g.left g.internal
        ((mem_pointHoles _ _).mpr ⟨s, by simpa only [tripleSignal, hk, Option.elim_some] using hs, hc⟩)
      omega

private theorem endpoint_probe_signal (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    {e : Endpoint} (he : e ∈ l.endpoints) (hs : e.side = .upper)
    (hj : 1 ≤ e.level) (hjm : e.level ≤ p.levels) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = p.x e.port) (hy : q.2.val = p.Y e.level + 2)
    (hb : state.axes.getD e.port false = true) :
    (q.1.val, q.2.val) ∈ pointHoles (l.signalSegments p state) := by
  have ha : (q.1.val, q.2.val) ∈ pointHoles ((endpointSegments (coordinates p) state e).take 1) := by
    rw [axis_mem]
    simp only [hs, onSide, ite_true, hb, Bool.toNat_true, readDepth_eq p hj hjm, hy]
    exact ⟨hx, by omega, by omega⟩
  obtain ⟨s, hseg, hc⟩ := (mem_pointHoles _ _).mp ha
  exact (mem_pointHoles _ _).mpr ⟨s, List.mem_append_left _
    (List.mem_flatMap.mpr ⟨e, he, List.mem_of_mem_take hseg⟩), hc⟩

end PushPuzzle.PushS.PortLayout

namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushFS.Reduction PushS PushS.PortLayout SegmentRecipe AcceptanceProbe

/-- The canonical signal bitmap on all actual upper probe rows is exactly the true-bit probe image. -/
theorem signal_probe_rows (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (target : List Bool)
    {q : Cell (p.W + 1) (p.H + 1)} :
    ((q.1.val, q.2.val) ∈ pointHoles (l.signalSegments p (l.canonical target)) ∧ q.2.val ∈ probeRows l p) ↔
      q ∈ probeSignalStock l p hl hM haxes target := by
  constructor
  · rintro ⟨hsignal, hrows⟩
    obtain ⟨e, he, hs, hx, hy, hb⟩ := l.signal_probe_endpoint p hl hM (l.canonical target) hrows hsignal
    let i : Fin l.portCount := ⟨e.port, l.endpoints_port_lt hl he⟩
    obtain ⟨he', hs', hp'⟩ := upperEndpoint_spec l hl i
    have heq : upperEndpoint l hl i = e := l.endpoints_key_injective hl he' he (hs'.trans hs.symm) hp'
    apply Finset.mem_map.mpr
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩, ?_⟩
    apply Prod.ext <;> apply Fin.ext
    · exact hx.symm
    · change p.Y (level l hl i) + 2 = q.2.val
      simpa only [level, heq] using hy.symm
  · intro hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hq
    have hi := (Finset.mem_filter.mp hi).2
    obtain ⟨he, hs, hp⟩ := upperEndpoint_spec l hl i
    have hb := probeLevel_bounds l p hl hM i
    refine ⟨l.endpoint_probe_signal p (l.canonical target) he hs hb.1 hb.2 ?_ rfl ?_,
      probeCell_mem_rows l p hl hM haxes i⟩
    · change p.x i.val = p.x (upperEndpoint l hl i).port
      rw [hp]
    · change target.getD (upperEndpoint l hl i).port false = true
      simpa only [hp] using hi

end PushPuzzle.Push.AcceptanceProgram
