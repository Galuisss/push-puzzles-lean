/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.PortAxisBlockers
public import Push.AcceptanceProgramProbeStockSignals
import all PushS.PortAxisBlockers
import all PushS.PortOrdinaryBlockers
import all PushS.PortEndpointReaderFreeze
import all PushS.PortEndpointLevelReader
import all PushS.PortEndpointRWall
import all PushS.PortEndpointLevelRWall
import all PushS.PortStreetEnumeration
import all PushS.PortSegments
import all PushS.PortColumnRadius

/-! Endpoint ownership and the frozen receiving-column cells on upper probe rows. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout

private theorem upper_page_auxiliary (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) {x : Fin (p.W + 1)} (hx : x ∈ l.pageColumnSet p .upper)
    (hn : x ∉ l.mainColumnSet p) :
    ∃ e ∈ l.endpoints, e.side = .upper ∧ ∃ k : EndpointStreet, x.val = k.column p e := by
  change x.val ∈ pageColumns l (coordinates p) .upper at hx
  simp only [pageColumns, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, reduceCtorEq, ite_false, or_assoc] at hx
  rcases hx with h0 | hW | hx
  · exact (hn ((l.mainColumnSet_iff p x).mpr (Or.inl h0))).elim
  · exact (hn ((l.mainColumnSet_iff p x).mpr (Or.inr (Or.inl hW)))).elim
  · obtain ⟨e, he, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨he, hs⟩ := List.mem_filter.mp he
    have hs : e.side = .upper := of_decide_eq_true hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hf | hm | hr
    · exact ⟨e, he, hs, .f, hf⟩
    · exact (hn ((l.mainColumnSet_iff p x).mpr
        (Or.inr (Or.inr ⟨e.port, l.endpoints_port_lt hl he, hm⟩)))).elim
    · exact ⟨e, he, hs, .r, hr⟩

private theorem endpoint_street_radius (p : Scales.Parameters) (e : Endpoint)
    (k : EndpointStreet) {x : ℕ} (hx : x = k.column p e) :
    Nat.dist x (p.x e.port) ≤ p.L p.levels + 12 := by
  have hspan := endpoint_columns_span p e (x := x) (by
    cases k <;> simp [endpointColumns, EndpointStreet.column] at hx ⊢ <;> tauto)
  simp only [columnRadius, Nat.dist] at hspan ⊢
  omega

private theorem upper_probe_deep_band (p : Scales.Parameters) (e : Endpoint)
    (hs : e.side = .upper) (hj : 1 ≤ e.level) {j : ℕ} (hjm : j ≤ p.levels)
    (hlt : e.level < j) (k : EndpointStreet) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = k.column p e) (hy : q.2.val = readDepth p j + 2) :
    q ∈ axisDeepBand p e.side e.port e.level := by
  have hn := next_depth_le p hj hlt hjm
  have hg := readDepth_interlevel_margin p hj (by omega : e.level < p.levels)
  have hm := readDepth_le_last p j
  refine ⟨endpoint_street_radius p e k hx, ?_⟩
  simp only [hs, ite_true]
  omega

private theorem endpointOrdinaryBlockers_r_branch_mem (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (e : Endpoint) (he : e ∈ l.endpoints) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = EndpointStreet.r.column p e)
    (hy : q.2.val = if e.side = .upper then readDepth p e.level + 2
      else p.H - (readDepth p e.level + 2)) :
    q ∈ l.endpointOrdinaryBlockers p hl hM ha e he := by
  by_cases hlast : e.level = p.levels
  · let g := lastReaderSeparator l p hl ha e he
    have hrow : InwardRow p e g.cell q := by
      refine ⟨Fin.ext ?_, ?_⟩
      · rw [g.row]
        simpa only [hlast, readDepth_eq p p.levels_pos le_rfl] using hy
      · have hg := g.forward
        have hx0 := readLength_add_lt_x p e.port 0
        rw [EndpointStreet.column_r] at hx
        cases hi : e.inward <;> simp only [hi, Bool.false_eq_true, ite_true, ite_false] at hx hg ⊢ <;> omega
    rcases r_wall_row_point l p hl e g q hrow with hwall | hpage
    · simp only [endpointOrdinaryBlockers, hlast, ite_true, endpointReaderBlockers]
      exact Finset.mem_union_left _ (Finset.mem_union_right _ hwall)
    · simp only [endpointOrdinaryBlockers, hlast, ite_true]
      exact reader_page_subset l p hl hM ha e he hpage
  · let g := levelReaderSeparator l p hl hM ha e he
    have hrow : InwardRow p e g.cell q := by
      refine ⟨Fin.ext (hy.trans g.row.symm), ?_⟩
      have hg := g.forward
      have hx0 := readLength_add_lt_x p e.port 0
      rw [EndpointStreet.column_r] at hx
      cases hi : e.inward <;> simp only [hi, Bool.false_eq_true, ite_true, ite_false] at hx hg ⊢ <;> omega
    rcases level_wall_point l p hl e g (fun _ h => h) q (Or.inr hrow) with hwall | hpage
    · simp only [endpointOrdinaryBlockers, hlast, ite_false, endpointLevelReaderBlockers]
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hwall))
    · simp only [endpointOrdinaryBlockers, hlast, ite_false]
      exact level_reader_page l p hl hM ha e he hpage

end PushPuzzle.Push.AcceptanceSoundness
