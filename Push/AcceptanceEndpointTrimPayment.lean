/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceEndpointTrimGeometry
public import Push.AcceptanceSoundnessWireTrimStock
public import PushS.PortEndpointHorizontalReadout
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramTrimStock

/-! Actual one-cell receiving-column collateral certifies the second horizontal work-row hole. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ []) (e : Endpoint) (he : e ∈ l.endpoints)

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate he

/-- All actual receiving-column collateral is the endpoint's own work cell. -/
private theorem canonical_r_trim_collateral_work {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (I).board none (I).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ rTrimCollateral l p target (holes t) e) :
    q.1.val = EndpointStreet.r.column p e ∧ pageDepth p e.side q = readDepth p e.level ∧ q ∈ holes t := by
  let T := targetHoles l p target
  let E := holes t
  let stages := schedule l p (T \ Boundary.frame).card
  let i := if e.side = .upper then 4 else 3
  obtain ⟨hqpaid, hnotcorridor⟩ := Finset.mem_sdiff.mp hq
  obtain ⟨hqpaid, hx⟩ := Finset.mem_filter.mp hqpaid
  obtain ⟨hqA, hqF⟩ := Finset.mem_sdiff.mp hqpaid
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) accepted).2
  have hqE := scan_subset (roundResidual_eval stages T E i hc) hqA
  have hf := canonical_residual_not_frame l p hl hM haxes initial target hr accepted i
    (by cases hs : e.side <;> simp [i, hs]) hqA
  have bounds := l.endpoints_level_bounds p hl hM he
  have hread := readDepth_eq p bounds.1 bounds.2
  have hrow := q.2.isLt
  have hpositive : 1 ≤ pageDepth p e.side q := by
    by_contra hn
    apply hf
    cases hs : e.side with
    | upper =>
      exact (Boundary.mem_frame q).mpr ⟨.north, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simp only [pageDepth, hs, ite_true] at hn
        omega⟩⟩
    | lower =>
      exact (Boundary.mem_frame q).mpr ⟨.south, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        simp only [pageDepth, hs, reduceCtorEq, ite_false] at hn
        omega⟩⟩
  have hnear : readDepth p e.level ≤ pageDepth p e.side q := by
    by_contra hn
    apply hnotcorridor
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx, hpositive, by omega⟩
  have heq : pageDepth p e.side q = readDepth p e.level := by
    by_contra hn
    obtain ⟨a, hac, hcol, hlevel, _⟩ := endpoint_trim_column l p e he .r
    have hfar := canonical_trim_payment_depth l p hl hM haxes initial target hr accepted e.side hac
      (hx.trans hcol.symm) hqA hqF
    rw [hlevel] at hfar
    have hcentral := canonical_trim_payment_not_central l p hl hM haxes initial target hr accepted e.side hqF
    exact (mem_holes _).mp hqE (canonical_r_trim_deep_occupied l p hl hM haxes initial target hgate e he hx
      (by omega) hfar hcentral hr .refl accepted)
  exact ⟨hx, heq, hqE⟩

/-- A target requesting the second inward horizontal hole certifies that very physical terminal cell. -/
theorem canonical_r_horizontal_target_payment {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (I).board none (I).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (hdelta : endpointWorkDelta l p target e = 1)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = if e.inward then p.x e.port + 2 else p.x e.port - 2)
    (hy : q.2.val = if e.side = .upper then readDepth p e.level else p.H - readDepth p e.level) : q ∈ holes t := by
  have hcard := canonical_r_trim_collateral_card l p hl hM haxes initial target hgate e he hr accepted
  rw [hdelta] at hcard
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < (rTrimCollateral l p target (holes t) e).card by omega)
  obtain ⟨hax, hay, hahole⟩ := canonical_r_trim_collateral_work l p hl hM haxes initial target hgate e he hr accepted ha
  have hsame : a = q := by
    apply Prod.ext
    · apply Fin.ext
      simpa only [EndpointStreet.column_r, hx] using hax
    · apply Fin.ext
      have haH := a.2.isLt
      have hqH := q.2.isLt
      cases hs : e.side <;> simp only [pageDepth, hs, reduceCtorEq, ite_true, ite_false] at hay hy <;> omega
  exact hsame ▸ hahole

/-- Every genuine endpoint horizontal word meets its actual target two-hole requirement. -/
theorem canonical_endpoint_horizontal_target_bound {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (I).board none (I).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (hdelta : endpointWorkDelta l p target e = 1) {horizontal : ℕ}
    (word : EndpointHorizontalReadout p e t horizontal) : 2 ≤ horizontal := by
  have hx0 := readLength_add_lt_x p e.port 0
  have hxW := x_add_readLength_lt_W p ((l.endpoints_port_lt hl he).trans_le haxes) 0
  have hyH := readDepth_add_lt_H p e.level
  let q : Cell (p.W + 1) (p.H + 1) :=
    (⟨if e.inward then p.x e.port + 2 else p.x e.port - 2, by split <;> omega⟩,
      ⟨if e.side = .upper then readDepth p e.level else p.H - readDepth p e.level, by split <;> omega⟩)
  exact (word.near_holes q 2 (by omega) (by omega) rfl rfl).mp
    (canonical_r_horizontal_target_payment l p hl hM haxes initial target hgate e he hr accepted hdelta rfl rfl)

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
