/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupportInterlevel
public import Push.AcceptanceSoundnessSupportHalf
public import Push.AcceptanceSoundnessSupportPrivate
public import PushS.PortInterlevelFreeze
public import PushS.PortGateMarkers
public import PushS.PortGateHalfMarkers
import all PushS.PortInterlevelFreeze
import all PushS.PortGateMarkers
import all PushS.PortGateHalfMarkers
import all PushS.PortSegments
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceSoundnessSupportPrivateStock

/-! Actual accepted endpoints retain the ordinary, gate-interlevel and gate-half marker inventories. -/

public section
namespace PushPuzzle.PushS.PortLayout

open PushFS Push.AcceptanceProgram

private theorem ordinary_marker_metadata (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) {j : ℕ}
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.interlevelMarkers p j) :
    ∃ side, InterlevelMarker l p side q := by
  obtain ⟨e, he, _, hjm, street, hx, hy⟩ := marker_data l p hq
  obtain ⟨hj, hm⟩ := l.endpoints_level_bounds p hl hM he
  obtain ⟨a, ha, hcol, hlevel, _⟩ := endpoint_trim_column l p e he street
  refine ⟨e.side, a, ha, hlevel.symm ▸ hj, hlevel.symm ▸ hjm, hx.trans hcol.symm, ?_⟩
  rw [hlevel, trimDepth, ite_eq_left hjm]
  rw [readDepth_eq p hj hm, readDepth_eq p (by omega) (by omega)] at hy
  have hb := interlevelDepth_bounds p hj hjm
  unfold interlevelDepth at hb
  have hh : p.H = 2 * p.D := rfl
  cases hs : e.side <;> simp only [pageDepth, hs, ite_true, reduceCtorEq, ite_false] at hy ⊢ <;> omega

private theorem gate_marker_metadata (l : PortLayout) (p : Scales.Parameters)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.gateInterlevelMarkers p) :
    InterlevelMarker l p .lower q := by
  obtain ⟨hlevels, middle, hi, hx, hy⟩ := gate_marker_data l p hq
  have hcols : ∀ a ∈ ([⟨p.x middle - 2, 1, false⟩, ⟨p.x middle + 4, 1, true⟩,
        ⟨p.x middle + 6, 1, false⟩, ⟨p.x middle + 8, 1, false⟩,
        ⟨p.x middle + 12, 1, false⟩] : List PageColumn), a ∈ Push.AcceptanceProgram.pageColumns l p .lower := by
    intro a ha
    apply List.mem_append_right
    rw [ite_eq_left rfl]
    exact List.mem_flatMap.mpr ⟨middle, hi, ha⟩
  have hd : pageDepth p .lower q = trimDepth p 1 := by
    rw [readDepth_eq p le_rfl p.levels_pos, readDepth_eq p (by omega) (by omega)] at hy
    have hb := interlevelDepth_bounds p le_rfl hlevels
    unfold interlevelDepth at hb
    simp only [Nat.reduceAdd] at hb
    have hh : p.H = 2 * p.D := rfl
    simp only [pageDepth, trimDepth, ite_eq_left hlevels, reduceCtorEq, ite_false, Nat.reduceAdd]
    omega
  change q.1.val ∈ [p.x middle - 2, p.x middle + 4, p.x middle + 6, p.x middle + 8, p.x middle + 12] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with hx | hx | hx | hx | hx
  · exact ⟨⟨_, 1, false⟩, hcols _ (by simp), le_rfl, hlevels, hx, hd⟩
  · exact ⟨⟨_, 1, true⟩, hcols _ (by simp), le_rfl, hlevels, hx, hd⟩
  · exact ⟨⟨_, 1, false⟩, hcols _ (by simp), le_rfl, hlevels, hx, hd⟩
  · exact ⟨⟨_, 1, false⟩, hcols _ (by simp), le_rfl, hlevels, hx, hd⟩
  · exact ⟨⟨_, 1, false⟩, hcols _ (by simp), le_rfl, hlevels, hx, hd⟩

end PushPuzzle.PushS.PortLayout

namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  {t : State (p.W + 1) (p.H + 1)}
  (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
    (l.canonicalInstance p hl hM haxes initial target).initial t)
  (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))

include hr ha

/-- All physical ordinary-endpoint interlevel markers are holes in every actual accepted endpoint. -/
theorem canonical_ordinary_interlevel_markers_terminal (j : ℕ) :
    l.interlevelMarkers p j ⊆ PushS.holes t := by
  intro q hq
  obtain ⟨side, hm⟩ := l.ordinary_marker_metadata p hl hM hq
  exact canonical_interlevel_marker_terminal l p hl hM haxes initial target hr ha side hm

/-- All physical five-column gate interlevel markers are holes in every actual accepted endpoint. -/
theorem canonical_gate_interlevel_markers_terminal : l.gateInterlevelMarkers p ⊆ PushS.holes t := by
  intro q hq
  exact canonical_interlevel_marker_terminal l p hl hM haxes initial target hr ha .lower
    (l.gate_marker_metadata p hq)

/-- Both physical core and private half-depth markers are holes in every actual accepted endpoint. -/
theorem canonical_gate_half_markers_terminal : l.gateHalfMarkers p ⊆ PushS.holes t := by
  intro q hq
  obtain ⟨middle, hi, hx, hy⟩ := l.half_marker_data p hq
  rw [readDepth_eq p le_rfl p.levels_pos] at hy
  rcases hx with hcore | hprivate
  · apply canonical_core_half_marker_terminal l p hl hM haxes initial target hr ha hy
    exact hcore ▸ gate_core_column l p hi
  · apply canonical_private_slot_terminal l p hl hM haxes initial target hr ha
      (hprivate ▸ gate_private_column l p hi)
    have hD := readDepth_add_lt_D p 1
    rw [readDepth_eq p le_rfl p.levels_pos] at hD
    have hh : p.H = 2 * p.D := rfl
    have hd : pageDepth p .lower q = p.Y 1 / 2 := by
      change p.H - q.2.val = p.Y 1 / 2
      omega
    rw [hd]
    exact Finset.mem_insert_self ..

end PushPuzzle.Push.AcceptanceSoundness
