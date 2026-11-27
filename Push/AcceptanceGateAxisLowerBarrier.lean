/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceGateWalks
public import Push.AcceptanceSoundnessColumnRadius
public import PushS.PortGateAxisNoInput
import all PushS.PortGateAxisNoInput
import all PushS.PortGatePrivateWalk
import all PushS.PortCentralStrip

/-! Actual private and deep-column blockers exclude lower horizontal box input into a gate middle axis. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

local notation "I" => l.canonicalInstance p hl hM ha initial target

include hgate

theorem canonical_lower_gate_horizontal_impossible {middle depth : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    {u v t : State (p.W + 1) (p.H + 1)} {d : Direction} {n : ℕ}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (run : Run (I).board d u n) (hn : 0 < n) (hp : v.player = run.cell 1)
    (hb : v.boxes = insert (run.cell ⟨n + 1, by omega⟩) (u.boxes.erase (run.cell 1)))
    (hd : d = .east ∨ d = .west) (hv : depth ∈ l.workingDepthCoordinates p) (hdepth : readDepth p 1 < depth)
    (hx : (run.cell ⟨n + 1, by omega⟩).1.val = p.x middle)
    (hy : (run.cell ⟨n + 1, by omega⟩).2.val = p.H - depth) : False := by
  let q : Cell (p.W + 1) (p.H + 1) := run.cell ⟨n, by omega⟩
  let z : Cell (p.W + 1) (p.H + 1) := run.cell ⟨n + 1, by omega⟩
  change z.1.val = _ at hx
  change z.2.val = _ at hy
  have hadj := run.adjacent ⟨n, by omega⟩
  change Adjacent d q z at hadj
  have hqy : q.2.val = p.H - depth := by rcases hd with rfl | rfl <;> exact (congrArg Fin.val hadj.2).symm.trans hy
  rcases l.workingDepthCoordinates_bands p (show 1 ≤ 1 by omega) p.levels_pos hv with hshallow | hbranch | ⟨hlevels, hdeep⟩
  · omega
  · have hx0 := readLength_add_lt_x p middle 0
    have hqx : q.1.val = p.x middle - 1 ∨ q.1.val = p.x middle + 1 := by
      rcases hd with rfl | rfl <;> simp only [Adjacent] at hadj <;> omega
    rcases hqx with hleft | hright
    · have hg := canonical_gate_private_step_avoiding l p hl hM ha initial target hgate hi hsu hm hvt accepted
      exact hg.2 d n run hn hp hb ⟨n, by omega⟩
        (private_bottom l p hl hM ha hi (Or.inl hleft) (hbranch ▸ hqy))
    · have hwalk : q ∈ gatePrivateWalk p middle := (mem_gatePrivateWalk p middle).mpr
        (Or.inr (Or.inr ⟨hbranch ▸ hqy, by omega, by omega⟩))
      have he := canonical_gate_privateWalk_empty l p hl hM ha initial target hgate hi hsu
        ((Relation.ReflTransGen.single hm).trans hvt) accepted
      exact (mem_holes q).mp (he hwalk) (run.occupied_at ⟨n, by omega⟩ hn le_rfl)
  · have hmax := workingRows_le_last l p hv
    have hband : z ∈ axisDeepBand p .lower middle 1 := by
      refine ⟨by rw [hx, Nat.dist_self]; omega, ?_⟩
      simp only [reduceCtorEq, ite_false]
      omega
    have hgap := readDepth_interlevel_margin p (show 1 ≤ 1 by omega) hlevels
    have hfull := gate_deep_axis_initial_full l p hl hM ha (l.canonical initial) (l.canonical target) hi hv (by omega) hx hy
    exact run.empty (canonical_gate_deep_occupied l p hl hM ha initial target hgate hi hlevels hband hfull hsu
      ((Relation.ReflTransGen.single hm).trans hvt) accepted)

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
