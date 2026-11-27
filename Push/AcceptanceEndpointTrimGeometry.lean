/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceOrdinaryReaderClosure
public import Push.AcceptanceSoundnessTrimBarrier
import all PushS.PortOrdinaryBlockers
import all PushS.PortEndpointReaderFreeze
import all PushS.PortEndpointLevelReader
import all PushS.PortEndpointLevelRWall
import all PushS.PortEndpointRWall
import all PushS.PortGatePrivateEntry
import all PushS.PortCentralFreeze
import all PushS.PortBackground
import all PushS.PortSegments
import all PushS.PortLayoutCoordinates
import all Push.AcceptanceProgramTrimStock

/-! The actual receiving-column trim pays no cells beyond its own work row. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

private theorem r_short_guard (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (initial target : List Bool) (e : Endpoint) (he : e ∈ l.endpoints)
    {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val = EndpointStreet.r.column p e)
    {k : ℕ} (hk : k = 1 ∨ k = 2)
    (hy : q.2.val = if e.side = .upper then readDepth p e.level + k else p.H - (readDepth p e.level + k)) :
    q ∈ l.endpointOrdinaryBlockers p hl hM haxes e he ∧
      q ∈ (l.canonicalInstance p hl hM haxes initial target).initial.boxes := by
  classical
  have hD := readDepth_add_lt_D p e.level
  have hH : p.H = 2 * p.D := rfl
  have hc : q ∉ l.centralMarkers p := by
    intro hc
    have hb := (Finset.mem_filter.mp hc).2
    cases hs : e.side <;> simp only [hs, reduceCtorEq, ite_true, ite_false] at hy <;> omega
  have hrStreet := (auxiliary_columns l p he).2
  have hw : q ∉ l.wideSeparatorHoles p := by
    intro hw
    have hqStreet : q.1 ∈ l.streetColumnSet p := by
      change q.1.val ∈ streetColumns l (coordinates p)
      rw [hx, EndpointStreet.column_r]
      have hcx : (coordinates p).x = p.x := rfl
      simpa only [auxiliary, inward, hcx] using hrStreet
    have hfar := l.wideSeparatorHoles_street_gap p hl hw q.1 hqStreet
    simp only [Nat.dist_self] at hfar
    omega
  have hmargin := readLength_add_lt_x p e.port 0
  by_cases last : e.level = p.levels
  · let g := lastReaderSeparator l p hl haxes e he
    have forward := g.forward
    have hwall : q ∈ l.endpointRWall p e g := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, hc, hw, ?_⟩
      rcases hk with rfl | rfl
      · left
        refine ⟨?_, ?_⟩
        · simpa only [rColumn, EndpointStreet.column_r] using hx
        · have hd : readDepth p e.level = p.Y p.levels := by rw [last, readDepth_eq p p.levels_pos le_rfl]
          simpa only [hd] using hy
      · right
        refine ⟨Fin.ext ?_, ?_⟩
        · have hd : readDepth p e.level = p.Y p.levels := by rw [last, readDepth_eq p p.levels_pos le_rfl]
          rw [hy, g.row, hd]
        · rw [hx, EndpointStreet.column_r]
          cases hi : e.inward <;> simp only [hi, Bool.false_eq_true, ite_true, ite_false] at forward ⊢ <;> omega
    refine ⟨?_, l.endpointRWall_initial_full p hl hM haxes (l.canonical initial) (l.canonical target) e he g last hwall⟩
    simp only [endpointOrdinaryBlockers, ite_eq_left last, endpointReaderBlockers]
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hwall)
  · let g := levelReaderSeparator l p hl hM haxes e he
    have forward := g.forward
    have hwall : q ∈ l.levelRWall p e g := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, hc, hw, ?_⟩
      rcases hk with rfl | rfl
      · exact Or.inl ⟨hx, hy⟩
      · right
        refine ⟨Fin.ext (hy.trans g.row.symm), ?_⟩
        rw [hx, EndpointStreet.column_r]
        cases hi : e.inward <;> simp only [hi, Bool.false_eq_true, ite_true, ite_false] at forward ⊢ <;> omega
    refine ⟨?_, l.levelRWall_initial_full p hl hM haxes (l.canonical initial) (l.canonical target) e he g hwall⟩
    simp only [endpointOrdinaryBlockers, ite_eq_right last, endpointLevelReaderBlockers]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hwall))

/-- Every receiving-column cell strictly after its work row and before its retained marker stays occupied. -/
theorem canonical_r_trim_deep_occupied (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (initial target : List Bool) (hgate : l.gateCenterCoordinates ≠ []) (e : Endpoint) (he : e ∈ l.endpoints)
    {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val = EndpointStreet.r.column p e)
    (near : readDepth p e.level < pageDepth p e.side q) (far : pageDepth p e.side q < trimDepth p e.level)
    (central : q ∉ l.centralMarkers p) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t)) : q ∈ u.boxes := by
  classical
  have bounds := l.endpoints_level_bounds p hl hM he
  have hread := readDepth_eq p bounds.1 bounds.2
  have hD := readDepth_add_lt_D p e.level
  have hH : p.H = 2 * p.D := rfl
  have hqb := q.2.isLt
  by_cases short : pageDepth p e.side q ≤ readDepth p e.level + 2
  · let k := pageDepth p e.side q - readDepth p e.level
    have hk : k = 1 ∨ k = 2 := by dsimp only [k]; omega
    have hy : q.2.val = if e.side = .upper then readDepth p e.level + k else p.H - (readDepth p e.level + k) := by
      cases hs : e.side <;> simp only [pageDepth, hs, reduceCtorEq, ite_true, ite_false] at near short ⊢ <;>
        dsimp only [k, pageDepth] <;> simp only [hs, reduceCtorEq, ite_true, ite_false] <;> omega
    obtain ⟨guard, full⟩ := r_short_guard l p hl hM haxes initial target e he hx hk hy
    exact avoiding_box (canonical_ordinary_reader_avoiding_prefix l p hl hM haxes initial target hgate e he hsu hut accepted) guard full
  · by_cases last : e.level = p.levels
    · obtain ⟨a, hac, hcol, _, _⟩ := endpoint_trim_column l p e he .r
      have haux : q.1.val ∈ auxiliaries l p :=
        (hx.trans hcol.symm) ▸ l.acceptancePageColumn_aux p hl hM haxes e.side hac
      have hmain : q.1 ∉ l.mainColumnSet p := by
        intro hm
        have hn := (Finset.mem_sdiff.mp haux).2
        rcases (l.mainColumnSet_iff p q.1).mp hm with h0 | hW | ⟨i, hi, hxi⟩
        · exact hn (Finset.mem_union_right _ (by simp [h0]))
        · exact hn (Finset.mem_union_right _ (by simp [hW]))
        · exact hn (Finset.mem_union_left _ (List.mem_toFinset.mpr (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, hxi.symm⟩)))
      have hbox : q ∈ l.centralAuxiliaryBoxes p := by
        apply (mem_centralAuxiliaryBoxes l p q).mpr
        refine ⟨List.mem_toFinset.mp (Finset.mem_sdiff.mp haux).1, hmain, ?_, ?_, central⟩
        all_goals
          rw [last, trimDepth, ite_eq_right (by omega)] at far
          rw [last, readDepth_eq p p.levels_pos le_rfl] at short
          cases hs : e.side <;> simp only [pageDepth, hs, reduceCtorEq, ite_true, ite_false] at short far <;> omega
      exact canonical_central_auxiliary_full l p hl hM haxes initial target hsu hut accepted hbox
    · have hlevel : e.level < p.levels := by omega
      have hnext := readDepth_eq p (j := e.level + 1) (by omega) (by omega)
      have htail : q ∈ endpointTail p e .r := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, hx, pageDepth p e.side q, by omega, ?_, ?_⟩
        · simpa only [endpointMarkerDepth, trimDepth, ite_eq_left hlevel, hread, hnext] using far
        · cases e.side <;> simp only [pageDepth, reduceCtorEq, ite_true, ite_false]
          omega
      exact canonical_endpoint_tail_full_of_deeper l p hl hM haxes initial target hgate e he hlevel .r hsu hut accepted
        (fun _ hs ht => canonical_deeperWalk_empty l p hl hM haxes initial target hgate e.level hs ht accepted) htail

end PushPuzzle.Push.AcceptanceSoundness
