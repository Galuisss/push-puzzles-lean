/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramWireRowStockPaid
public import Push.AcceptanceProgramTrimStock
public import PushS.PortEndpointPageWindow
import all Push.AcceptanceProgramTrimStock
import all Push.AcceptanceProgramInterlevelStockGeometry
import all Push.AcceptanceSoundnessCentralGeometry
import all PushS.PortEndpointLocality
import all PushS.PortEndpointPageWindow
import all PushS.PortWireGeometry
import all PushS.PortCoreCrossing
import all PushS.PortHoleBudget
import all PushS.EndpointWalking
import all PushS.PortSegments

/-! The whole endpoint r trim sees only its literal outer corridor and its canonical work hole. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushFS.Reduction PushS PushS.PortLayout SegmentRecipe

private theorem r_column_near (p : Scales.Parameters) (e : Endpoint)
    {x : ℕ} (hx : x = EndpointStreet.r.column p e) : Nat.dist x (p.x e.port) ≤ 2 := by
  rw [hx, EndpointStreet.column_r]
  have hx0 := readLength_add_lt_x p e.port 0
  cases e.inward <;> simp only [Bool.false_eq_true, ite_true, ite_false, Nat.dist] <;> omega

private theorem rtrim_not_central (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (e : Endpoint) (he : e ∈ l.endpoints) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = EndpointStreet.r.column p e) (hy : pageDepth p e.side q < p.D - 2) :
    q ∉ l.centralMarkers p := by
  intro hc
  have hH : p.H = 2 * p.D := rfl
  have hD := p.outer_distance
  rcases PushPuzzle.Push.AcceptanceSoundness.central_sources l p hc with h | h | h | ⟨hyG, ss, hxG⟩ | ⟨hyS, i, hi, hxS⟩
  · cases hs : e.side <;> simp only [hs, pageDepth, ite_true, reduceCtorEq, ite_false] at hy <;> omega
  · cases hs : e.side <;> simp only [hs, pageDepth, ite_true, reduceCtorEq, ite_false] at hy <;> omega
  · cases hs : e.side <;> simp only [hs, pageDepth, ite_true, reduceCtorEq, ite_false] at hy <;> omega
  · have hfar := guard_axis_far l p ss hxG (l.endpoints_port_lt hl he)
    have hn := r_column_near p e hx
    omega
  · have hs : e.side = .lower := by
      cases hs : e.side
      · simp only [hs, pageDepth, ite_true] at hy
        omega
      · rfl
    obtain ⟨a, ha, hcol, _, _⟩ := endpoint_trim_column l p e he .r
    rw [hs] at ha
    apply l.acceptanceLowerColumn_not_sample p hl ha
    apply List.mem_toFinset.mpr
    apply List.mem_flatMap.mpr
    refine ⟨i, hi, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    exact hxS.elim (fun h => Or.inl (hcol.trans (hx.symm.trans h))) (fun h => Or.inr (hcol.trans (hx.symm.trans h)))

private theorem rtrim_target_window (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (target : List Bool)
    (e : Endpoint) (he : e ∈ l.endpoints) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ targetHoles l p target) (hf : q ∉ Boundary.frame)
    (hx : q.1.val = EndpointStreet.r.column p e) (hy : pageDepth p e.side q < trimDepth p e.level) :
    q ∈ endpointPageWindow p e := by
  obtain ⟨he0, heM⟩ := l.endpoints_level_bounds p hl hM he
  have htrim := trimDepth_lt_D p he0 heM
  have htrim' : trimDepth p e.level ≤ p.D - 2 := by
    unfold trimDepth
    split
    · have h0 := readDepth_add_lt_D p e.level
      have h1 := readDepth_add_lt_D p (e.level + 1)
      rw [readDepth_eq p he0 heM] at h0
      rw [readDepth_eq p (by omega) (by omega : e.level + 1 ≤ p.levels)] at h1
      omega
    · exact le_rfl
  have hnotC := rtrim_not_central l p hl e he hx (hy.trans_le htrim')
  have hnear := r_column_near p e hx
  have hwindow (other : Side) (hpage : if other = .upper then q.2.val + 32 < p.D else p.D + 32 < q.2.val) :
      q ∈ endpointPageWindow p e := by
    have hqH := q.2.isLt
    have hq0 : 0 < q.2.val := by
      by_contra hn
      apply hf
      apply (Boundary.mem_frame q).mpr
      exact ⟨.north, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩
    have hqLast : q.2.val < p.H := by
      by_contra hn
      apply hf
      apply (Boundary.mem_frame q).mpr
      exact ⟨.south, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩
    have hH : p.H = 2 * p.D := rfl
    refine ⟨?_, by omega⟩
    cases es : e.side <;> cases os : other <;>
      simp only [es, os, pageDepth, ite_true, reduceCtorEq, ite_false] at hy hpage ⊢ <;> omega
  rcases encoded_sources l p hl hM (l.canonical target) hq hf with hc | hw | hs
  · exact (hnotC hc).elim
  · have hfar := l.wideSeparatorHoles_street_gap p hl hw q.1
      (show q.1 ∈ l.streetColumnSet p from by
        obtain ⟨a, ha, hcol, _, _⟩ := endpoint_trim_column l p e he .r
        have haux := l.acceptancePageColumn_aux p hl hM haxes e.side ha
        change q.1.val ∈ l.streetColumnCoordinates p
        rw [hx, ← hcol]
        exact List.mem_toFinset.mp (Finset.mem_sdiff.mp haux).1)
    rw [Nat.dist_self] at hfar
    omega
  · rcases hs with ⟨f, _, hs⟩ | ⟨kind, first, _, hs⟩
    · exact hwindow f.side (hs.elim (fixed_endpoint_page l p f) (signal_endpoint_page p (l.canonical target) f))
    · apply hwindow .lower
      rcases hs with hs | ⟨internal, hs⟩
      · exact gate_fixed_page p (first + 1) hs
      · exact gate_signal_page p (l.canonical target) kind first internal hs

/-- An actual r-trim target hole is either in the outer corridor or exactly on its endpoint's work row. -/
theorem endpoint_r_trim_hole_depth (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (target : List Bool)
    (e : Endpoint) (he : e ∈ l.endpoints) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ targetHoles l p target) (hf : q ∉ Boundary.frame)
    (hx : q.1.val = EndpointStreet.r.column p e) (hy : pageDepth p e.side q < trimDepth p e.level) :
    pageDepth p e.side q ≤ p.Y e.level := by
  have hw := rtrim_target_window l p hl hM haxes target e he hq hf hx hy
  have hq := (l.encodedSegments_endpointPageWindow p hl hM haxes (l.canonical target) e he q hw).mp hq
  obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hq
  obtain ⟨he0, heM⟩ := l.endpoints_level_bounds p hl hM he
  have hL := readLength_ge p he0 heM
  have hX := readLength_add_lt_x p e.port e.level
  have hY := readDepth_ge p he0 heM
  have hH := readDepth_add_lt_H p e.level
  rw [readDepth_eq p he0 heM] at hY hH
  have hqH := q.2.isLt
  have hcoord : (coordinates p).depth e.level = p.Y e.level := readDepth_eq p he0 heM
  have hcX : (coordinates p).x = p.x := rfl
  have hcL : (coordinates p).length e.level = readLength p e.level := rfl
  have hcH : (coordinates p).H = p.H := rfl
  have hx' : q.1.val = inward (p.x e.port) e.inward 2 := hx
  rcases List.mem_append.mp hs with hs | hs
  · dsimp only [endpointFixedSegments] at hs
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hs
    rcases hs with rfl | rfl | rfl | hs | hs
    · have hc := vertical_coordinates hc
      cases hd : e.inward <;> simp only [auxiliary, outward, inward, hd, hcX, hcL, Bool.false_eq_true, ite_true, ite_false] at hc hx' <;> omega
    · have hc := vertical_coordinates hc
      cases es : e.side <;> simp only [es, onSide, hcH, hcoord, pageDepth, ite_true, reduceCtorEq, ite_false] at hc ⊢ <;> omega
    · have hc := horizontal_coordinates hc
      cases hd : e.inward <;> simp only [auxiliary, outward, inward, hd, hcX, hcL, Bool.false_eq_true, ite_true, ite_false] at hc hx' <;> omega
    · obtain ⟨v, _, hs⟩ := List.mem_flatMap.mp hs
      rcases List.mem_append.mp hs with hs | hs
      all_goals split at hs
      all_goals try { cases hs }
      all_goals simp only [List.mem_singleton] at hs
      all_goals subst s
      all_goals have hc := point_coordinates hc
      all_goals cases hd : e.inward <;> simp only [auxiliary, outward, inward, hd, hcX, hcL, Bool.false_eq_true, ite_true, ite_false] at hc hx' <;> omega
    · split at hs
      next hlev =>
        change e.level < p.levels at hlev
        have hn := readDepth_add_lt_H p (e.level + 1)
        rw [readDepth_eq p (by omega) (by omega : e.level + 1 ≤ p.levels)] at hn
        have hncoord : (coordinates p).depth (e.level + 1) = p.Y (e.level + 1) := readDepth_eq p (by omega) (by omega)
        rw [trimDepth, ite_eq_left hlev] at hy
        have hcNext : (coordinates p).depth (e.level + 1) = p.Y (e.level + 1) := hncoord
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        all_goals have hc := point_coordinates hc
        all_goals cases es : e.side <;> simp only [es, onSide, hcH, hcoord, hcNext, pageDepth, ite_true, reduceCtorEq, ite_false] at hc hy <;> omega
      next hlev => cases hs
  · simp only [endpointSegments, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · have hc := vertical_coordinates hc
      cases hd : e.inward <;> simp only [inward, hd, hcX, Bool.false_eq_true, ite_true, ite_false] at hc hx' <;> omega
    · have hc := horizontal_coordinates hc
      cases es : e.side <;> simp only [es, onSide, hcH, hcoord, pageDepth, ite_true, reduceCtorEq, ite_false] at hc ⊢ <;> omega

end PushPuzzle.Push.AcceptanceProgram
