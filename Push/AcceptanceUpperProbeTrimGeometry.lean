/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceUpperProbeColumnsGeometry
public import Push.AcceptanceSoundnessWireTrimStock
import all Push.AcceptanceUpperProbeColumnsGeometry
import all Push.AcceptanceProgramProbeStockSignals
import all Push.AcceptanceAxisTerminalReadoutGeometry
import all PushS.PortEndpointFStock
import all PushS.PortEndpointPageWindow
import all PushS.PortEndpointCounts
import all PushS.PortSegments

/-! Original upper probe holes on auxiliary columns belong to the exact f/r trim corridors. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushFS.Reduction PushS PushS.PortLayout SegmentRecipe AcceptanceProgram

private theorem street_probe_bound (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (target : List Bool)
    (e : Endpoint) (he : e ∈ l.endpoints) (hsu : e.side = .upper) (k : EndpointStreet)
    {q : Cell (p.W + 1) (p.H + 1)} (hrow : q.2.val ∈ probeRows l p)
    (hx : q.1.val = k.column p e) (hq : q ∈ targetHoles l p target) :
    q.2.val ≤ if k = .f then readDepth p e.level + 2 else readDepth p e.level - 1 := by
  obtain ⟨ref, href, _, hyref⟩ := probe_row_data l p hrow
  obtain ⟨hr0, hrM⟩ := l.endpoints_level_bounds p hl hM href
  obtain ⟨he0, heM⟩ := l.endpoints_level_bounds p hl hM he
  have rowPositive := p.Y_ge ref.level
  have ownMod := AcceptanceAxisReadout.Y_mod p e.level
  have refMod := AcceptanceAxisReadout.Y_mod p ref.level
  have margin := readDepth_add_lt_D p ref.level
  rw [readDepth_eq p hr0 hrM] at margin
  have window : q ∈ endpointPageWindow p e := by
    refine ⟨?_, le_trans (endpoint_street_radius p e k hx) (by omega)⟩
    simp only [hsu, ite_true]
    omega
  have raw := (l.encodedSegments_endpointPageWindow p hl hM haxes (l.canonical target) e he q window).mp hq
  obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp raw
  have hL := readLength_ge p he0 heM
  have hX := readLength_add_lt_x p e.port e.level
  have hcoord : (coordinates p).depth e.level = p.Y e.level := readDepth_eq p he0 heM
  have hcX : (coordinates p).x = p.x := rfl
  have hcL : (coordinates p).length e.level = readLength p e.level := rfl
  have hread := readDepth_eq p he0 heM
  rcases List.mem_append.mp hs with hs | hs
  · dsimp only [endpointFixedSegments] at hs
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hs
    rcases hs with rfl | rfl | rfl | hs | hs
    · have hc := vertical_coordinates hc
      cases k <;> cases hd : e.inward <;>
        simp only [EndpointStreet.column_f, EndpointStreet.column_r, auxiliary, outward, inward,
          hd, hcX, hcL, hcoord, hsu, onSide, ite_true, Bool.false_eq_true, ite_false, reduceCtorEq, hread] at hx hc ⊢ <;> omega
    · have hc := vertical_coordinates hc
      cases k <;> cases hd : e.inward <;>
        simp only [EndpointStreet.column_f, EndpointStreet.column_r, auxiliary, outward, inward,
          hd, hcX, hcL, hcoord, hsu, onSide, ite_true, Bool.false_eq_true, ite_false, reduceCtorEq, hread] at hx hc ⊢ <;> omega
    · have hc := horizontal_coordinates hc
      cases k <;> cases hd : e.inward <;>
        simp only [EndpointStreet.column_f, EndpointStreet.column_r, auxiliary, outward, inward,
          hd, hcX, hcL, hcoord, hsu, onSide, ite_true, Bool.false_eq_true, ite_false, reduceCtorEq, hread] at hx hc ⊢ <;> omega
    · obtain ⟨v, _, hs⟩ := List.mem_flatMap.mp hs
      rcases List.mem_append.mp hs with hs | hs
      all_goals split at hs
      all_goals try { cases hs }
      all_goals simp only [List.mem_singleton] at hs
      all_goals subst s
      all_goals have hc := point_coordinates hc
      all_goals cases k <;> cases hd : e.inward <;>
        simp only [EndpointStreet.column_f, EndpointStreet.column_r, auxiliary, outward, inward,
          hd, hcX, hcL, Bool.false_eq_true, ite_true, ite_false] at hc hx <;> omega
    · split at hs
      next levels =>
        have nextMod := AcceptanceAxisReadout.Y_mod p (e.level + 1)
        have nextCoord : (coordinates p).depth (e.level + 1) = p.Y (e.level + 1) :=
          readDepth_eq p (by omega) (by change e.level < p.levels at levels; omega)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        all_goals
          have hc := point_coordinates hc
          simp only [hsu, onSide, ite_true, hcoord, nextCoord] at hc
          omega
      next levels => cases hs
  · simp only [endpointSegments, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · have hc := vertical_coordinates hc
      cases k <;> cases hd : e.inward <;>
        simp only [EndpointStreet.column_f, EndpointStreet.column_r, hd, hcX, Bool.false_eq_true,
          ite_true, ite_false] at hc hx <;> omega
    · have hc := horizontal_coordinates hc
      simp only [hsu, onSide, ite_true, hcoord] at hc
      omega

/-- Every original probe hole on an upper f column lies in its full public f corridor. -/
theorem upper_probe_f_stock (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (target : List Bool)
    (e : Endpoint) (he : e ∈ l.endpoints) (hsu : e.side = .upper)
    {q : Cell (p.W + 1) (p.H + 1)} (hrow : q.2.val ∈ probeRows l p)
    (hx : q.1.val = EndpointStreet.f.column p e) (hq : q ∈ targetHoles l p target) : q ∈ endpointFWalk p e := by
  have bound := street_probe_bound l p hl hM haxes target e he hsu .f hrow hx hq
  apply (mem_endpointFWalk_iff p e q).mpr
  exact ⟨hx, by simpa only [hsu, ite_true] using bound⟩

/-- Every original probe hole on an upper r column lies strictly before its working row. -/
theorem upper_probe_r_stock (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (target : List Bool)
    (e : Endpoint) (he : e ∈ l.endpoints) (hsu : e.side = .upper)
    {q : Cell (p.W + 1) (p.H + 1)} (hrow : q.2.val ∈ probeRows l p)
    (hx : q.1.val = EndpointStreet.r.column p e) (hq : q ∈ targetHoles l p target) : q ∈ rTrimCorridor p e := by
  have bound := street_probe_bound l p hl hM haxes target e he hsu .r hrow hx hq
  obtain ⟨ref, _, _, hyref⟩ := probe_row_data l p hrow
  have positive := p.Y_ge ref.level
  obtain ⟨he0, heM⟩ := l.endpoints_level_bounds p hl hM he
  rw [readDepth_eq p he0 heM] at bound
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_univ _, hx, by simpa only [pageDepth, hsu, ite_true] using (show 1 ≤ q.2.val by omega),
    by simpa only [pageDepth, hsu, ite_true] using (show q.2.val < p.Y e.level by simp only [reduceCtorEq, ite_false] at bound; omega)⟩

end PushPuzzle.Push.AcceptanceSoundness
