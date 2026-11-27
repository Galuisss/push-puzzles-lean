/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceUpperProbeColumnsGeometry
public import Push.AcceptanceSoundnessProbeFixedSource
public import Push.AcceptanceOrdinaryReaderClosure
public import Push.AcceptanceSoundnessColumnRadius
import all Push.AcceptanceUpperProbeColumnsGeometry
import all Push.AcceptanceProgramProbeStockSignals
import all PushS.PortEndpointFStock
import all PushS.PortEndpointReaderWalk
import all PushS.PortOrdinaryFailure
import all PushS.PortWireGeometry

/-! Every non-main upper-page column keeps its original probe-row bitmap throughout accepted play. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate

private theorem canonical_upper_probe_endpoint_column_no_new_hole
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (e : Endpoint) (he : e ∈ l.endpoints) (hs : e.side = .upper) (k : EndpointStreet)
    {q : Cell (p.W + 1) (p.H + 1)} (hrow : q.2.val ∈ probeRows l p)
    (hx : q.1.val = k.column p e) (hq : q ∈ holes u) : q ∈ holes (I).initial := by
  classical
  by_contra hn
  have hb : q ∈ (I).initial.boxes := by
    by_contra hbox
    exact hn ((mem_holes _).mpr hbox)
  obtain ⟨ref, href, _, hy⟩ := probe_row_data l p hrow
  obtain ⟨hr0, hrM⟩ := l.endpoints_level_bounds p hl hM href
  obtain ⟨he0, heM⟩ := l.endpoints_level_bounds p hl hM he
  rw [← readDepth_eq p hr0 hrM] at hy
  have hf (hle : q.2.val ≤ readDepth p e.level + 2)
      (hxf : q.1.val = EndpointStreet.f.column p e) : False := by
    have hwalk : q ∈ endpointFWalk p e :=
      (mem_endpointFWalk p e q).mpr ⟨hxf, q.2.val, hle, by simp only [hs, ite_true]⟩
    have hempty : endpointFWalk p e ⊆ holes (I).initial := by
      by_cases hlast : e.level = p.levels
      · exact canonical_last_fwalk_empty_at l p hl hM haxes initial target hgate e he hlast
          .refl (hsu.trans hut) accepted
      · exact canonical_level_fwalk_empty_at_of_deeper l p hl hM haxes initial target hgate e he
          (by omega) .refl (hsu.trans hut) accepted
          (fun _ ha hat => canonical_deeperWalk_empty l p hl hM haxes initial target hgate e.level ha hat accepted)
    exact (mem_holes _).mp (hempty hwalk) hb
  have hdeep (hlt : e.level < ref.level) : False := by
    have hband := upper_probe_deep_band p e hs he0 hrM hlt k hx hy
    exact (mem_holes _).mp hq (canonical_endpoint_deep_occupied l p hl hM haxes initial target hgate
      e he (by omega) hband hb hsu hut accepted)
  cases k with
  | f =>
    by_cases hle : ref.level ≤ e.level
    · have hdepth := readDepth_le_level p hle
      rw [← readDepth_eq p he0 heM] at hdepth
      exact hf (by omega) hx
    · exact hdeep (by omega)
  | r =>
    rcases lt_trichotomy ref.level e.level with hlt | heq | hlt
    · have hgap := depth_gap p hr0 hlt heM
      have hwalk : q ∈ l.endpointReaderWalk p e := by
        apply Finset.mem_union_right
        apply Finset.mem_union_left
        exact (mem_endpointRWalk p e q).mpr ⟨hx, q.2.val, by omega, by simp only [hs, ite_true]⟩
      exact (mem_holes _).mp
        (canonical_ordinaryReaders_empty l p hl hM haxes initial target hgate e he .refl
          (hsu.trans hut) accepted hwalk) hb
    · have hclosure := endpointOrdinaryBlockers_r_branch_mem l p hl hM haxes e he hx (by
        simpa only [hs, ite_true, heq] using hy)
      exact (mem_holes _).mp hq (avoiding_box
        (canonical_ordinary_reader_avoiding_prefix l p hl hM haxes initial target hgate e he hsu hut accepted)
        hclosure hb)
    · exact hdeep hlt

/-- Every non-main upper-page column retains its exact initial bitmap on every actual probe row. -/
theorem canonical_upper_probe_page_column_constant
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    {q : Cell (p.W + 1) (p.H + 1)} (hrow : q.2.val ∈ probeRows l p)
    (hcol : q.1 ∈ l.pageColumnSet p .upper) (hnmain : q.1 ∉ l.mainColumnSet p) :
    (q ∈ holes u ↔ q ∈ holes (I).initial) := by
  obtain ⟨e, he, hs, k, hx⟩ := upper_page_auxiliary l p hl hcol hnmain
  exact ⟨canonical_upper_probe_endpoint_column_no_new_hole l p hl hM haxes initial target hgate
      hsu hut accepted e he hs k hrow hx,
    fun h => canonical_upper_probe_source_empty l p hl hM haxes initial target hgate
      hsu hut accepted h hrow hnmain⟩

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
