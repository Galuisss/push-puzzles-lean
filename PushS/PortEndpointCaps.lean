/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortEndpointLocality
public import PushS.PortInstance
import all PushS.PortSegments
import all PushS.PortEndpointSeparation

/-! Actual solid inward caps beside an ordinary endpoint's working row. -/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

/-- The r-column cell one depth beyond the work row and the inward part of the long-branch row,
restricted to the endpoint's actual local window. -/
@[expose] def endpointInwardCap (p : Scales.Parameters) (e : Endpoint) :
    Set (Cell (p.W + 1) (p.H + 1)) :=
  {q | q ∈ endpointWindow p e ∧
    ((q.1.val = (if e.inward then p.x e.port + 2 else p.x e.port - 2) ∧
      q.2.val = (if e.side = .upper then readDepth p e.level + 1
        else p.H - (readDepth p e.level + 1))) ∨
    (q.2.val = (if e.side = .upper then readDepth p e.level + 2
        else p.H - (readDepth p e.level + 2)) ∧
      (if e.inward then p.x e.port < q.1.val else q.1.val < p.x e.port)))}

private theorem cap_geometry (p : Scales.Parameters) (e : Endpoint)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ endpointInwardCap p e) :
    (if e.inward then (coordinates p).x e.port < q.1.val else q.1.val < (coordinates p).x e.port) ∧
      ∃ k, (k = 1 ∨ k = 2) ∧ q.2.val = onSide (coordinates p) e.side ((coordinates p).depth e.level + k) := by
  obtain ⟨_, hq⟩ := hq
  have hx := readLength_add_lt_x p e.port 0
  change readLength p 0 + 64 < p.x e.port at hx
  constructor
  · change if e.inward then p.x e.port < q.1.val else q.1.val < p.x e.port
    rcases hq with ⟨hc, _⟩ | ⟨_, hc⟩
    · cases hd : e.inward <;> simp only [hd, Bool.false_eq_true, ite_false, ite_true] at hc ⊢ <;> omega
    · exact hc
  · rcases hq with ⟨_, hy⟩ | ⟨hy, _⟩
    · exact ⟨1, Or.inl rfl, hy⟩
    · exact ⟨2, Or.inr rfl, hy⟩

private theorem own_fixed_cap_clear (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (e : Endpoint) (he : e ∈ l.endpoints)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hin : if e.inward then (coordinates p).x e.port < q.1.val else q.1.val < (coordinates p).x e.port)
    {k : ℕ} (hk : k = 1 ∨ k = 2)
    (hrow : q.2.val = onSide (coordinates p) e.side ((coordinates p).depth e.level + k))
    (hq : (q.1.val, q.2.val) ∈ pointHoles (endpointFixedSegments l (coordinates p) e)) : False := by
  let c := coordinates p
  obtain ⟨hj, hm⟩ := l.endpoints_level_bounds p hl hM he
  have hY : 16384 ≤ c.depth e.level := readDepth_ge p hj hm
  have hL : 16384 ≤ c.length e.level := readLength_ge p hj hm
  have hx : c.length e.level + 64 < c.x e.port := readLength_add_lt_x p e.port e.level
  have hy : c.depth e.level + 64 < c.H := readDepth_add_lt_H p e.level
  change (if e.inward then c.x e.port < q.1.val else q.1.val < c.x e.port) at hin
  change q.2.val = onSide c e.side (c.depth e.level + k) at hrow
  change (q.1.val, q.2.val) ∈ pointHoles (endpointFixedSegments l c e) at hq
  obtain ⟨s, hs, hq⟩ := (mem_pointHoles _ _).mp hq
  dsimp only [endpointFixedSegments] at hs
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hs
  rcases hs with rfl | rfl | rfl | hs | hs
  · have hp := (vertical_coordinates hq).1
    cases hd : e.inward <;> simp [auxiliary, outward, hd] at hp hin <;> omega
  · have hp := vertical_coordinates hq
    cases hd : e.side <;> simp [onSide, hd] at hp hrow <;> omega
  · have hp := horizontal_coordinates hq
    cases hd : e.inward <;> simp [auxiliary, inward, outward, hd] at hp hin <;> omega
  · obtain ⟨v, _, hs⟩ := List.mem_flatMap.mp hs
    rcases List.mem_append.mp hs with hs | hs
    · split at hs
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        subst s
        have hp := (point_coordinates hq).1
        cases hd : e.inward <;> simp [auxiliary, outward, hd] at hp hin <;> omega
      · cases hs
    · split at hs
      · rename_i hlt
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        subst s
        have hp := (point_coordinates hq).2
        cases hd : e.side <;> simp [onSide, hd] at hp hrow <;> omega
      · cases hs
  · split at hs
    · rename_i hnext
      have hsep := readDepth_interlevel_margin p hj hnext
      have hn : c.depth (e.level + 1) + 64 < c.H := readDepth_add_lt_H p (e.level + 1)
      change 2 * p.b e.level + 6 < (c.depth (e.level + 1) - c.depth e.level) / 2 - 2 at hsep
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · have hp := (point_coordinates hq).1
        cases hd : e.inward <;> simp [auxiliary, outward, hd] at hp hin <;> omega
      · have hp := (point_coordinates hq).2
        cases hd : e.side <;> simp [onSide, hd] at hp hrow <;> omega
    · cases hs

private theorem cap_source_not_hole (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels)
    (state : SignalState) (e : Endpoint) (he : e ∈ l.endpoints)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hin : if e.inward then (coordinates p).x e.port < q.1.val else q.1.val < (coordinates p).x e.port)
    {k : ℕ} (hk : k = 1 ∨ k = 2)
    (hrow : q.2.val = onSide (coordinates p) e.side ((coordinates p).depth e.level + k)) :
    q ∉ SegmentRecipe.holes (p.W + 1) (p.H + 1)
      (endpointFixedSegments l (coordinates p) e ++ endpointSegments (coordinates p) state e) := by
  intro hq
  obtain ⟨s, hs, hq⟩ := (SegmentRecipe.mem_holes _ q).mp hq
  rcases List.mem_append.mp hs with hs | hs
  · exact own_fixed_cap_clear l p hl hM e he hin hk hrow ((mem_pointHoles _ _).mpr ⟨s, hs, hq⟩)
  · have hy : (coordinates p).depth e.level + 64 < (coordinates p).H := readDepth_add_lt_H p e.level
    dsimp only [endpointSegments] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · have hp := (vertical_coordinates hq).1
      cases hd : e.inward <;> simp [hd] at hin <;> omega
    · have hp := (horizontal_coordinates hq).1
      cases hd : e.side <;> simp [onSide, hd] at hp hrow <;> omega

/-- The actual inward cap contains no emitted hole, for any physical signal bits. -/
theorem endpointInwardCap_not_hole (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) (e : Endpoint) (he : e ∈ l.endpoints)
    {q : Cell (p.W + 1) (p.H + 1)} (hc : q ∈ endpointInwardCap p e) :
    q ∉ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) := by
  rw [l.encodedSegments_endpointWindow p hl hM ha state e he q hc.1]
  obtain ⟨hin, k, hk, hrow⟩ := cap_geometry p e hc
  exact cap_source_not_hole l p hl hM state e he hin hk hrow

/-- Every inward-cap cell of an actual ordinary endpoint is initially occupied. -/
theorem physicalInstance_endpoint_cap_full (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) (e : Endpoint) (he : e ∈ l.endpoints)
    {q : Cell (p.W + 1) (p.H + 1)} (hc : q ∈ endpointInwardCap p e) :
    q ∈ (l.physicalInstance p hl hM ha initial target).initial.boxes := by
  by_contra hbox
  apply l.endpointInwardCap_not_hole p hl hM ha initial e he hc
  rw [← l.physicalInstance_initial_holes p hl hM ha initial target]
  exact (mem_holes _).mpr hbox

end PushPuzzle.PushS.PortLayout
