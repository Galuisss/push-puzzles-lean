/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.EndpointAxisMacro
public import PushS.PortAxisClear
import all PushS.PortAxisClear
import all PushS.PortCoreCrossing
import all PushS.PortEndpointEnumeration
import all PushS.PortEndpointCrossing
import all PushS.PortSegments

/-! Ordinary shared-axis pushes on the complete actual marked board. -/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

private def axisRest (l : PortLayout) (p : Scales.Parameters) (state : SignalState) (i : ℕ) :
    List Segment :=
  l.fixedSegments p ++
    ((l.endpoints.filter fun e => decide (e.port ≠ i)).flatMap (endpointSegments (coordinates p) state) ++
      (placements l).flatMap (tripleSignal (coordinates p) state))

private theorem endpoint_set_other (p : Scales.Parameters) (state : SignalState)
    (e : Endpoint) (i : ℕ) (gain : Bool) (hne : e.port ≠ i) :
    endpointSegments (coordinates p) {state with axes := state.axes.set i gain} e =
      endpointSegments (coordinates p) state e := by
  simp only [endpointSegments, List.getD, List.getElem?_set_ne hne.symm]

private theorem core_set_other (p : Scales.Parameters) (state : SignalState)
    (g : Placement) (i : ℕ) (gain : Bool) (hne : g.left + 1 ≠ i) :
    tripleSignal (coordinates p) {state with axes := state.axes.set i gain} g =
      tripleSignal (coordinates p) state g := by
  cases hg : g.gate <;>
    simp only [tripleSignal, hg, Option.elim, gateSegments, List.getD,
      List.getElem?_set_ne hne.symm]

private theorem rest_set (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (state : SignalState) {e : Endpoint} (he : e ∈ l.endpoints) (hs : e.side = .lower)
    (gain : Bool) :
    axisRest l p {state with axes := state.axes.set e.port gain} e.port =
      axisRest l p state e.port := by
  unfold axisRest
  congr 2
  · apply List.flatMap_congr
    intro f hf
    have hne := of_decide_eq_true (List.mem_filter.mp hf).2
    exact endpoint_set_other p state f e.port gain hne
  · apply List.flatMap_congr
    intro g hg
    cases hgate : g.gate with
    | none => simp only [tripleSignal, hgate, Option.elim]
    | some kind =>
      have hraw := placement_gate_mem l hg hgate
      have hne := l.endpoints_lower_ne_gate_middle hl hraw he hs
      exact core_set_other p state g e.port gain hne.symm

private theorem endpoint_pair_at_port (l : PortLayout) (hl : l.pages.Valid) {e f g : Endpoint}
    (he : e ∈ l.endpoints) (hf : f ∈ l.endpoints) (hg : g ∈ l.endpoints)
    (heSide : e.side = .upper) (hfSide : f.side = .lower) (hport : f.port = e.port)
    (hgport : g.port = e.port) : g = e ∨ g = f := by
  cases hs : g.side with
  | upper => exact Or.inl (l.endpoints_key_injective hl hg he (hs.trans heSide.symm) hgport)
  | lower => exact Or.inr (l.endpoints_key_injective hl hg hf (hs.trans hfSide.symm)
      (hgport.trans hport.symm))

private theorem finite_mem (p : Scales.Parameters) (ss : List Segment)
    (q : Cell (p.W + 1) (p.H + 1)) :
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) ss ↔
      (q.1.val, q.2.val) ∈ pointHoles ss := by
  simp only [SegmentRecipe.mem_holes, mem_pointHoles]

private theorem full_split (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (state : SignalState) {e f : Endpoint} (he : e ∈ l.endpoints) (hf : f ∈ l.endpoints)
    (heSide : e.side = .upper) (hfSide : f.side = .lower) (hport : f.port = e.port) :
    SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) =
      SegmentRecipe.holes (p.W + 1) (p.H + 1) (axisRest l p state e.port) ∪
      SegmentRecipe.holes (p.W + 1) (p.H + 1)
        (endpointSegments (coordinates p) state e ++ endpointSegments (coordinates p) state f) := by
  ext q
  simp only [Finset.mem_union, finite_mem, encodedSegments, signalSegments, rawSignals,
    axisRest, pointHoles_append, Finset.mem_union]
  constructor
  · rintro (hfixed | hend | hcore)
    · exact Or.inl (Or.inl hfixed)
    · obtain ⟨s, hmem, hq⟩ := (mem_pointHoles _ _).mp hend
      obtain ⟨g, hg, hmem⟩ := List.mem_flatMap.mp hmem
      by_cases hp : g.port = e.port
      · rcases endpoint_pair_at_port l hl he hf hg heSide hfSide hport hp with rfl | rfl
        · exact Or.inr (Or.inl ((mem_pointHoles _ _).mpr ⟨s, hmem, hq⟩))
        · exact Or.inr (Or.inr ((mem_pointHoles _ _).mpr ⟨s, hmem, hq⟩))
      · exact Or.inl (Or.inr (Or.inl ((mem_pointHoles _ _).mpr
          ⟨s, List.mem_flatMap.mpr ⟨g, List.mem_filter.mpr ⟨hg, by simp [hp]⟩, hmem⟩, hq⟩)))
    · exact Or.inl (Or.inr (Or.inr hcore))
  · rintro ((hfixed | hend | hcore) | heq | hfq)
    · exact Or.inl hfixed
    · obtain ⟨s, hmem, hq⟩ := (mem_pointHoles _ _).mp hend
      obtain ⟨g, hg, hmem⟩ := List.mem_flatMap.mp hmem
      exact Or.inr (Or.inl ((mem_pointHoles _ _).mpr
        ⟨s, List.mem_flatMap.mpr ⟨g, (List.mem_filter.mp hg).1, hmem⟩, hq⟩))
    · exact Or.inr (Or.inr hcore)
    · obtain ⟨s, hmem, hq⟩ := (mem_pointHoles _ _).mp heq
      exact Or.inr (Or.inl ((mem_pointHoles _ _).mpr
        ⟨s, List.mem_flatMap.mpr ⟨e, he, hmem⟩, hq⟩))
    · obtain ⟨s, hmem, hq⟩ := (mem_pointHoles _ _).mp hfq
      exact Or.inr (Or.inl ((mem_pointHoles _ _).mpr
        ⟨s, List.mem_flatMap.mpr ⟨f, hf, hmem⟩, hq⟩))

private theorem rest_axis_clear (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (state : SignalState)
    {e : Endpoint} (he : e ∈ l.endpoints) (hs : e.side = .lower) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles (axisRest l p state e.port)) (hcol : q.1 = p.x e.port)
    (hlo : 0 < q.2) (hhi : q.2 < p.H) : False := by
  simp only [axisRest, pointHoles_append, Finset.mem_union] at hq
  rcases hq with hfixed | hend | hcore
  · have hb := l.fixedSegments_on_ordinary_axis p hl hM ha he hs hfixed hcol
    omega
  · obtain ⟨s, hmem, hq⟩ := (mem_pointHoles _ _).mp hend
    obtain ⟨g, hg, hmem⟩ := List.mem_flatMap.mp hmem
    have hne := of_decide_eq_true (List.mem_filter.mp hg).2
    have hb := signal_span p state g ((mem_pointHoles _ _).mpr ⟨s, hmem, hq⟩)
    exact off_axis_of_span p hne (r := 2)
      (by have := readDepth_readLength_margin p 0 0; omega) hb hcol
  · obtain ⟨s, hmem, hq⟩ := (mem_pointHoles _ _).mp hcore
    obtain ⟨g, hg, hmem⟩ := List.mem_flatMap.mp hmem
    cases hgate : g.gate with
    | none => simp only [tripleSignal, hgate, Option.elim, List.not_mem_nil] at hmem
    | some kind =>
      have hraw := placement_gate_mem l hg hgate
      have hne := l.endpoints_lower_ne_gate_middle hl hraw he hs
      have hm : q ∈ pointHoles (gateSegments (coordinates p) state kind g.left g.internal) :=
        (mem_pointHoles _ _).mpr ⟨s, by simpa only [tripleSignal, hgate, Option.elim] using hmem, hq⟩
      have hb := gate_signal_span p state kind g.left g.internal hm
      exact off_axis_of_span p hne.symm (r := 12)
        (by have := readDepth_readLength_margin p 0 0; omega) (by omega) hcol

/-- A genuine ordinary shared-axis flip on the complete marked physical board. All other
emitted holes are retained, and the destination is exactly the updated `encodedSegments`. -/
theorem encodedSegments_axis_step (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (state : SignalState)
    (e f : Endpoint) (he : e ∈ l.endpoints) (hf : f ∈ l.endpoints)
    (heSide : e.side = .upper) (hfSide : f.side = .lower) (hport : f.port = e.port)
    (hindex : e.port < state.axes.length) (gain : Bool)
    (hbefore : state.axes.getD e.port false = !gain)
    (s : HoleState (p.W + 1) (p.H + 1))
    (hempty : s.empty = SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state))
    (hp : (s.player.1.val, s.player.2.val) =
      (p.x e.port, if gain then readDepth p e.level + 1 else p.H - readDepth p f.level - 1))
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) :
    ∃ t : HoleState (p.W + 1) (p.H + 1), Step B none s.toState t.toState ∧
      t.empty = SegmentRecipe.holes (p.W + 1) (p.H + 1)
        (l.encodedSegments p {state with axes := state.axes.set e.port gain}) ∧
      (t.player.1.val, t.player.2.val) =
        (p.x e.port, if gain then readDepth p e.level + 2 else p.H - readDepth p f.level - 2) := by
  let ambient := SegmentRecipe.holes (p.W + 1) (p.H + 1) (axisRest l p state e.port)
  have hfree : Disjoint ambient (SegmentRecipe.holes (p.W + 1) (p.H + 1)
      [⟨(p.x e.port, readDepth p e.level + 2),
        (p.x e.port, p.H - readDepth p f.level - 2)⟩]) := by
    apply Finset.disjoint_left.mpr
    intro q hqA hq
    rw [SegmentRecipe.mem_holes] at hq
    obtain ⟨s, hs, hq⟩ := hq
    simp only [List.mem_singleton] at hs
    subst s
    have hv : q.1.val = p.x e.port ∧ readDepth p e.level + 2 ≤ q.2.val ∧
        q.2.val ≤ p.H - readDepth p f.level - 2 := by
      have hu := readDepth_add_lt_D p e.level
      have hl' := readDepth_add_lt_D p f.level
      have hH : p.H = 2 * p.D := rfl
      dsimp only [Segment.Contains] at hq
      omega
    have hpoint := (finite_mem p _ q).mp hqA
    rw [← hport] at hpoint
    exact rest_axis_clear l p hl hM ha state hf hfSide hpoint
      (by simpa only [hport] using hv.1) (by omega) (by have := q.2.isLt; omega)
  obtain ⟨hj, hm⟩ := l.endpoints_level_bounds p hl hM hf
  have hsplit := full_split l p hl state he hf heSide hfSide hport
  have hsource : s.empty = ambient ∪ SegmentRecipe.holes (p.W + 1) (p.H + 1)
      (endpointSegments (coordinates p) state e ++ endpointSegments (coordinates p) state f) :=
    hempty.trans hsplit
  obtain ⟨t, hstep, ht, hplayer⟩ := axis_step p state e f heSide hfSide hport hj hm
    (lt_of_lt_of_le (l.endpoints_port_lt hl he) ha) hindex gain hbefore
    ambient hfree s hsource hp B hB
  refine ⟨t, hstep, ?_, hplayer⟩
  rw [full_split l p hl _ he hf heSide hfSide hport]
  have hrest := rest_set l p hl state hf hfSide gain
  rw [hport] at hrest
  rw [hrest]
  exact ht

end PushPuzzle.PushS.PortLayout
