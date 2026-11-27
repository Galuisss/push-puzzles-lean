/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortPublicExits
public import PushS.PortGatePublicWalk
import all PushS.PortGatePageWindow
import all PushS.PortGateMarkers
import all PushS.PortGatePublicWalk
import all PushS.PortEndpointWide
import all PushS.PortEndpointLocality
import all PushS.PortStreetSupport
import all PushS.PortBackground
import all PushS.PortSegments

/-! The actual two half-depth holes of every gate are protected by the final public-walk budget. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

/-- The emitted half-depth holes on each gate's middle axis and private column. -/
noncomputable def gateHalfMarkers (l : PortLayout) (p : Scales.Parameters) :
    Finset (Cell (p.W + 1) (p.H + 1)) := by
  classical
  exact Finset.univ.filter fun q => ∃ middle ∈ l.gateCenterCoordinates,
    (q.1.val = p.x middle ∨ q.1.val = p.x middle + 4) ∧
      q.2.val = p.H - readDepth p 1 / 2

private theorem half_marker_data (l : PortLayout) (p : Scales.Parameters)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.gateHalfMarkers p) :
    ∃ middle ∈ l.gateCenterCoordinates,
      (q.1.val = p.x middle ∨ q.1.val = p.x middle + 4) ∧
        q.2.val = p.H - readDepth p 1 / 2 := by
  classical
  simpa only [gateHalfMarkers, Finset.mem_filter, Finset.mem_univ, true_and] using hq

private theorem half_marker_window (p : Scales.Parameters) {middle : ℕ}
    {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = p.x middle ∨ q.1.val = p.x middle + 4)
    (hy : q.2.val = p.H - readDepth p 1 / 2) : q ∈ gatePageWindow p middle := by
  have hY := readDepth_ge p (show 1 ≤ 1 by omega) p.levels_pos
  have hD := readDepth_add_lt_D p 1
  have hH : p.H = 2 * p.D := rfl
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  simp only [Nat.dist]
  omega

/-- Every actual half-depth marker is a fixed hole of every physical signal encoding. -/
theorem gateHalfMarkers_subset_encoded (l : PortLayout) (p : Scales.Parameters) (state : SignalState) :
    l.gateHalfMarkers p ⊆ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) := by
  intro q hq
  obtain ⟨middle, hi, hx, hy⟩ := half_marker_data l p hq
  let s := point q.1.val (p.H - readDepth p 1 / 2)
  have hs : s ∈ gateFixedSegments (coordinates p) middle := by
    have hc : (coordinates p).x = p.x := rfl
    have hd : (coordinates p).depth 1 = readDepth p 1 := rfl
    simp only [gateFixedSegments, List.mem_append]
    left
    right
    simp only [List.mem_cons, List.not_mem_nil, or_false, gate_lower_coordinate, hd, hc]
    rcases hx with hx | hx
    · exact Or.inr (Or.inr (Or.inl (by simp only [s, hx])))
    · exact Or.inr (Or.inr (Or.inr (by simp only [s, hx])))
  apply (SegmentRecipe.mem_holes _ q).mpr
  refine ⟨s, List.mem_append_left _ (l.gateFixedSegments_mem_fixed p hi hs), ?_⟩
  simp only [s, point, segment, Segment.Contains, Nat.min_self, Nat.max_self, hy,
    le_refl, and_self, true_or]

private theorem half_marker_not_public (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) (state : SignalState)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.gateHalfMarkers p) : q ∉ l.allPublicWalkHoles p := by
  obtain ⟨middle, hi, hx, hy⟩ := half_marker_data l p hq
  have hwindow := half_marker_window p hx hy
  have hf := gate_window_not_frame l p hl ha hi hwindow
  intro hpub
  rcases Finset.mem_union.mp hpub with hframe | hw
  · exact hf hframe
  obtain ⟨s, hs, hcontains⟩ := (SegmentRecipe.mem_holes _ q).mp hw
  rcases List.mem_append.mp hs with hs | hs
  · obtain ⟨e, he, hs⟩ := List.mem_flatMap.mp hs
    exact gate_window_no_endpoint l p hl state hi hwindow e he (Or.inl
      ((mem_pointHoles _ _).mpr ⟨s, List.mem_of_mem_take hs, hcontains⟩))
  · obtain ⟨i, _, hs⟩ := List.mem_flatMap.mp hs
    have hp := ((mem_gatePublicWalk p i).mp (gatePublicSegments_subset_walk p i
      ((SegmentRecipe.mem_holes _ q).mpr ⟨s, hs, hcontains⟩))).resolve_left hf
    have hspan := gate_special_span p (gatePublicColumn_mem_special p hp.1)
    have heq : i = middle := nearby_axis_eq p hwindow.2 (by omega)
    rw [heq] at hp
    have hx0 := readLength_add_lt_x p middle 0
    simp only [gatePublicColumns, List.mem_cons, List.not_mem_nil, or_false] at hp
    omega

private def PublicStep (l : PortLayout) (p : Scales.Parameters)
    (B : Board (p.W + 1) (p.H + 1)) (s t : State (p.W + 1) (p.H + 1)) : Prop :=
  Radius.PreservingStep B none (l.allPublicWalkHoles p) s t ∧
    s.player ∈ Support.streets (l.streetColumnSet p) (l.workingRowSet p) ∧
    t.player ∈ Support.streets (l.streetColumnSet p) (l.workingRowSet p)

private theorem public_step_exit (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) {B : Board (p.W + 1) (p.H + 1)}
    {s t : State (p.W + 1) (p.H + 1)} (hm : PublicStep l p B s t)
    (hin : s.player ∈ l.allPublicWalkHoles p) (hout : t.player ∉ l.allPublicWalkHoles p) :
    s.player ∈ l.publicWalkExitSet p :=
  l.step_allPublicWalk_exit p hl hM hm.1.1 hm.2.1 hm.2.2 hin hout

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)

local notation "I" => l.physicalInstance p hl hM ha initial target

private theorem public_between {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (huv : Reachable (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals) :
    Relation.ReflTransGen (PublicStep l p (I).board) u v := by
  apply enrich_path huv
  intro a b hua hm hbv
  have hIa := hsu.trans hua
  have hIb := hIa.tail hm
  have hbt := hbv.trans hvt
  exact ⟨⟨hm, l.physicalInstance_allPublicWalk_empty p hl hM ha initial target hIb hbt ht⟩,
    l.physicalInstance_player_on_streets p hl hM ha initial target hIa ((Relation.ReflTransGen.single hm).trans hbt) ht,
    l.physicalInstance_player_on_streets p hl hM ha initial target hIb hbt ht⟩

/-- Both emitted half-depth holes of every gate remain empty and unvisited throughout every
successful actual trajectory. -/
theorem physicalInstance_gate_halfMarkers_excluded {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) : Blocked.Excluded (l.gateHalfMarkers p) u := by
  have hsu' := public_between l p hl hM ha initial target .refl hsu hut ht
  have hut' := public_between l p hl hM ha initial target hsu hut .refl ht
  have hPi := l.physicalInstance_allPublicWalk_empty p hl hM ha initial target .refl (hsu.trans hut) ht
  have hp : (I).initial.player ∈ l.allPublicWalkHoles p :=
    Finset.mem_union_left _ (l.physicalInstance_initial_frame p hl hM ha initial target)
  have hfar (q : Cell (p.W + 1) (p.H + 1)) (hq : q ∈ l.gateHalfMarkers p) :
      ∀ a ∈ l.publicWalkExitSet p, (holes (I).initial \ l.allPublicWalkHoles p).card < distance a q := by
    obtain ⟨middle, hi, hx, hy⟩ := half_marker_data l p hq
    have hb := l.encodedSegments_outside_allPublicWalk_card_le p hl hM ha initial
    rw [← l.physicalInstance_initial_holes p hl hM ha initial target] at hb
    exact fun a haE => hb.trans_lt (l.publicWalkExitSet_halfDepth_far p ha (gate_center_lt l hl hi)
      (by omega) hy a haE)
  constructor
  · intro q hq
    have hfinal : q ∈ holes t := by
      change q ∈ t.boxesᶜ
      rw [ht]
      change q ∈ (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p target))ᶜᶜ
      rw [compl_compl]
      exact l.gateHalfMarkers_subset_encoded p target hq
    exact Radius.distant_hole_at_from_exits (R := PublicStep l p (I).board)
      (fun {_ _} h => h.1) (fun {_ _} h hin hout => public_step_exit l p hl hM h hin hout)
      hsu' hut' hPi hp (half_marker_not_public l p hl ha initial hq) (hfar q hq) hfinal
  · intro hq
    exact Radius.player_ne_distant_from_exits (R := PublicStep l p (I).board)
      (fun {_ _} h => h.1) (fun {_ _} h hin hout => public_step_exit l p hl hM h hin hout)
      hsu' hPi hp (half_marker_not_public l p hl ha initial hq) (hfar u.player hq) rfl

end Solution
end PushPuzzle.PushS.PortLayout
