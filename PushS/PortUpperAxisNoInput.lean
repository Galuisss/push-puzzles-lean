/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortWireBarrier
public import PushS.PortAxisBlockers
public import PushS.PortDepthBands
public import PushS.PortColumnRadius
public import PushS.PortGatePublicWalk
import all PushS.PortWireIndexing
import all PushS.PortEndpointIndexing
import all PushS.PortOrdinaryAxis
import all PushS.PortEndpointReaderWalk
import all PushS.PortEndpointBranch
import all PushS.PortEndpointCounts
import all PushS.PortEndpointPageWindow
import all PushS.PortPublicWalkBudget
import all PushS.PortAxisClear
import all PushS.PortCentralStrip
import all PushS.PortSegments

/-! All horizontal box input at an actual upper main-axis working row is excluded. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

private theorem upper_endpoint_wire (l : PortLayout) {e : Endpoint}
    (he : e ∈ l.endpoints) (hs : e.side = .upper) :
    ∃ g ∈ placements l, g.gate = none ∧ (e = wireLeft g ∨ e = wireRight g) := by
  obtain ⟨g, hg, he⟩ := List.mem_flatMap.mp he
  have hside := endpoint_side_of_mem he
  have hw : g.gate = none := by
    cases hk : g.gate with
    | none => rfl
    | some kind =>
      have hgside := (placement_gate_shape l hg hk).1
      have hf : Side.upper = .lower := hs.symm.trans (hside.trans hgside)
      cases hf
  refine ⟨g, hg, hw, ?_⟩
  simpa only [hw, Option.isSome_none, Bool.false_eq_true, ite_false, Nat.add_zero,
    List.mem_cons, List.not_mem_nil, or_false, wireLeft, wireRight] using he

private theorem branch_subset_public (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (e : Endpoint) (he : e ∈ l.endpoints) :
    endpointLongBranch p e ⊆ l.allPublicWalkHoles p := by
  intro q hq
  apply Finset.mem_union_right
  apply (SegmentRecipe.mem_holes _ q).mpr
  refine ⟨_, ordinary_public_mem l p he ?_, (longBranch_contains_iff l p hl hM e he q).mpr hq⟩
  dsimp only [endpointFixedSegments]
  simp only [List.cons_append, List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil, or_false]
  exact Or.inr (Or.inr rfl)

private theorem endpoint_axis_deep_initial_full (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) (e : Endpoint) (he : e ∈ l.endpoints) {depth : ℕ}
    (hv : depth ∈ l.workingDepthCoordinates p) (hdeep : readDepth p e.level + 2 < depth)
    {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val = p.x e.port)
    (hy : q.2.val = if e.side = .upper then depth else p.H - depth) :
    q ∈ (l.physicalInstance p hl hM ha initial target).initial.boxes := by
  have hw := l.endpointPageWindow_of_workingDepth p e hv q hy (by rw [hx, Nat.dist_self]; omega)
  by_contra hbox
  have hh := (mem_holes q).mpr hbox
  have hinit : holes ((l.physicalInstance p hl hM ha initial target).initial : State (p.W + 1) (p.H + 1)) =
      SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p initial) :=
    l.physicalInstance_initial_holes p hl hM ha initial target
  have hh' : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p initial) := hinit ▸ hh
  rw [l.encodedSegments_endpointPageWindow p hl hM ha initial e he q hw] at hh'
  have hlocal := (finite_mem p _ q).mp hh'
  rw [pointHoles_append, Finset.mem_union] at hlocal
  rcases hlocal with hfixed | hsignal
  · exact own_fixed_off_axis l p hl hM he hfixed hx
  · rw [← List.take_append_drop 1 (endpointSegments (coordinates p) initial e), pointHoles_append,
      Finset.mem_union] at hsignal
    rcases hsignal with haxis | hhorizontal
    · have hax := (axis_mem p initial e _).mp haxis
      have hb := Bool.toNat_le (if e.side = .upper then initial.axes.getD e.port false else !(initial.axes.getD e.port false))
      have hdepth := (workingDepth_positive l p hv).2
      have hY := readDepth_add_lt_H p e.level
      cases hs : e.side <;> simp only [hs, reduceCtorEq, ite_true, ite_false, onSide,
        show (coordinates p).H = p.H from rfl] at hax hb hy <;> omega
    · exact horizontal_near_off_axis p initial e hhorizontal hx

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)

local notation "I" => l.physicalInstance p hl hM ha initial target

/-- A successful horizontal push cannot fill an actual upper main-axis cell on a selected row. -/
theorem physicalInstance_upper_axis_no_horizontal_input (e : Endpoint) (he : e ∈ l.endpoints)
    (hsuSide : e.side = .upper) {u v t : State (p.W + 1) (p.H + 1)} {d : Direction} {n depth : ℕ}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals)
    (run : Run (I).board d u n) (hn : 0 < n) (hp : v.player = run.cell 1)
    (hb : v.boxes = insert (run.cell ⟨n + 1, by omega⟩) (u.boxes.erase (run.cell 1)))
    (hd : d = .east ∨ d = .west) (hv : depth ∈ l.workingDepthCoordinates p)
    (hx : (run.cell ⟨n + 1, by omega⟩).1.val = p.x e.port)
    (hy : (run.cell ⟨n + 1, by omega⟩).2.val = depth) : False := by
  let q : Cell (p.W + 1) (p.H + 1) := run.cell ⟨n, by omega⟩
  let z : Cell (p.W + 1) (p.H + 1) := run.cell ⟨n + 1, by omega⟩
  change z.1.val = _ at hx
  change z.2.val = depth at hy
  have hadj := run.adjacent ⟨n, by omega⟩
  change Adjacent d q z at hadj
  have hqy : q.2.val = depth := by rcases hd with rfl | rfl <;> exact (congrArg Fin.val hadj.2).symm.trans hy
  have hqx : q.1.val = (if e.inward then p.x e.port - 1 else p.x e.port + 1) ∨
      q.1.val = (if e.inward then p.x e.port + 1 else p.x e.port - 1) := by
    rcases hd with rfl | rfl <;> cases hi : e.inward <;>
      simp only [Adjacent] at hadj <;> simp only [Bool.false_eq_true, ite_true, ite_false] <;> omega
  have havoid := l.physicalInstance_ordinary_reader_step_avoiding p hl hM ha initial target e he hsu hm hvt ht
  rcases l.workingDepthCoordinates_bands p (l.endpoints_level_bounds p hl hM he).1
      (l.endpoints_level_bounds p hl hM he).2 hv with hshallow | hbranch | ⟨heM, hdeep⟩
  · by_cases hown : depth = readDepth p e.level
    · obtain ⟨g, hg, hw, rfl | rfl⟩ := upper_endpoint_wire l he hsuSide
      all_goals
        have hgs : g.side = .upper := hsuSide
        have hgy : (run.cell ⟨n + 1, by omega⟩).2.val =
            (if g.side = .upper then readDepth p g.level else p.H - readDepth p g.level) := by
          change z.2.val = _
          simp only [hgs, ite_true]
          exact hy.trans hown
        apply l.physicalInstance_wire_axis_destination_impossible p hl hM ha initial target hg hw hsu hm hvt ht run hn hp hb hd hgy
        first | exact Or.inl hx | exact Or.inr hx
    · rcases hqx with hout | hin
      · exact havoid.2 d n run hn hp hb ⟨n, by omega⟩
          (l.endpointOrdinaryBlockers_front_mem p hl hM ha e he hv hshallow hout (by simpa only [hsuSide, ite_true] using hqy))
      · have hreader := l.physicalInstance_ordinaryReaders_empty p hl hM ha initial target e he hsu
          ((Relation.ReflTransGen.single hm).trans hvt) ht
        have hshort : q ∈ l.endpointShortBranches p e := (mem_endpointShortBranches l p e q).mpr
          ⟨hin, depth, hv, by omega, by simpa only [hsuSide, ite_true] using hqy⟩
        exact (mem_holes q).mp (hreader (Finset.mem_union_right _ (Finset.mem_union_right _ hshort)))
          (run.occupied_at ⟨n, by omega⟩ hn le_rfl)
  · rcases hqx with hout | hin
    · have hqbranch : q ∈ endpointLongBranch p e := by
        apply (mem_endpointLongBranch p e q).mpr
        refine ⟨by simpa only [hsuSide, ite_true, hbranch] using hqy, ?_⟩
        have hlen := readLength_ge p (l.endpoints_level_bounds p hl hM he).1 (l.endpoints_level_bounds p hl hM he).2
        have hx0 := readLength_add_lt_x p e.port e.level
        cases hi : e.inward <;> simp only [hi, Bool.false_eq_true, ite_true, ite_false, EndpointStreet.column_f] at hout ⊢ <;> omega
      have hpublic := l.physicalInstance_allPublicWalk_empty p hl hM ha initial target hsu
        ((Relation.ReflTransGen.single hm).trans hvt) ht
      exact (mem_holes q).mp (hpublic (branch_subset_public l p hl hM e he hqbranch))
        (run.occupied_at ⟨n, by omega⟩ hn le_rfl)
    · exact havoid.2 d n run hn hp hb ⟨n, by omega⟩
        (l.endpointOrdinaryBlockers_branch_mem p hl hM ha e he hin
          (by simpa only [hsuSide, ite_true, hbranch] using hqy))
  · have hmax := workingRows_le_last l p hv
    have hband : z ∈ axisDeepBand p e.side e.port e.level := by
      refine ⟨?_, ?_⟩
      · rw [hx, Nat.dist_self]
        omega
      · simp only [hsuSide, ite_true]
        omega
    have hgap := readDepth_interlevel_margin p (l.endpoints_level_bounds p hl hM he).1 heM
    have hfull := endpoint_axis_deep_initial_full l p hl hM ha initial target e he hv (by omega) hx
      (by simpa only [hsuSide, ite_true] using hy)
    exact run.empty (l.physicalInstance_endpoint_deep_occupied p hl hM ha initial target e he heM hband hfull hsu
      ((Relation.ReflTransGen.single hm).trans hvt) ht)

end Solution
end PushPuzzle.PushS.PortLayout
