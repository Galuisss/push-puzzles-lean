/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessOrdinaryWalks
public import Push.AcceptanceOrdinaryBoundary
public import PushS.PortOrdinaryBlockers
import all PushS.PortOrdinaryBlockers
import all PushS.PortOrdinaryFailure
import all PushS.PortBackground

/-! Completed actual walk descent supplies the original ordinary reader closure and all pocket boundary boxes. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram AcceptanceOrdinaryFailure

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ []) (e : Endpoint) (he : e ∈ l.endpoints)

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate he

private theorem canonical_ordinary_basis_step {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (step : Step (I).board none u v)
    (hvt : Reachable (I).board none v t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t)) :
    Freeze.AvoidingStep (I).board none (ordinaryReaderBasis l p hl e) u v := by
  have hut := (Relation.ReflTransGen.single step).trans hvt
  have midU := canonical_allMidpointRows_excluded l p hl hM haxes initial target hgate e.level hsu hut accepted
  have midV := canonical_allMidpointRows_excluded l p hl hM haxes initial target hgate e.level (hsu.tail step) hvt accepted
  have page := canonical_page_step_avoiding l p hl hM haxes initial target hgate hsu step hvt accepted
  by_cases last : e.level = p.levels
  · simp only [ordinaryReaderBasis, ite_eq_left last]
    exact page.union_excluded (last ▸ midU) (last ▸ midV)
  · have interU := canonical_allInterlevel_excluded l p hl hM haxes initial target hgate e.level
      (l.endpoints_level_bounds p hl hM he).1 hsu hut accepted
    have interV := canonical_allInterlevel_excluded l p hl hM haxes initial target hgate e.level
      (l.endpoints_level_bounds p hl hM he).1 (hsu.tail step) hvt accepted
    simp only [ordinaryReaderBasis, ite_eq_right last]
    exact (page.union_excluded interU interV).union_excluded midU midV

private theorem canonical_ordinary_basis_prefix {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t)) :
    Relation.ReflTransGen (Freeze.AvoidingStep (I).board none (ordinaryReaderBasis l p hl e)) (I).initial u := by
  apply Path.enrich hsu
  intro a b hsa step hbu
  exact canonical_ordinary_basis_step l p hl hM haxes initial target hgate e he hsa step (hbu.trans hut) accepted

/-- Every actual accepted prefix avoids the full computed ordinary reader closure. -/
theorem canonical_ordinary_reader_avoiding_prefix {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t)) :
    Relation.ReflTransGen (Freeze.AvoidingStep (I).board none
      (l.endpointOrdinaryBlockers p hl hM haxes e he)) (I).initial u :=
  (ordinaryReader_closure l p hl hM haxes (l.canonical initial) (l.canonical target) e he).reachable
    (canonical_ordinary_basis_prefix l p hl hM haxes initial target hgate e he hsu hut accepted)

/-- The complete ray of each actual accepted next step avoids that same ordinary reader closure. -/
theorem canonical_ordinary_reader_step_avoiding {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (step : Step (I).board none u v)
    (hvt : Reachable (I).board none v t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t)) :
    Freeze.AvoidingStep (I).board none (l.endpointOrdinaryBlockers p hl hM haxes e he) u v :=
  (ordinaryReader_closure l p hl hM haxes (l.canonical initial) (l.canonical target) e he).step
    (canonical_ordinary_basis_prefix l p hl hM haxes initial target hgate e he hsu
      ((Relation.ReflTransGen.single step).trans hvt) accepted)
    (canonical_ordinary_basis_step l p hl hM haxes initial target hgate e he hsu step hvt accepted)

/-- All outward and diagonal ordinary pocket neighbours are occupied throughout the actual accepted trajectory. -/
theorem canonical_ordinary_boundary {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t)) : BoundaryBoxes p e u := by
  apply canonical_boundary_of_outward l p hl hM haxes initial target hsu hut accepted e he
  intro q hx hy
  have level := l.endpoints_level_bounds p hl hM he
  have hY := readDepth_ge p level.1 level.2
  have hH := readDepth_add_lt_H p e.level
  have hq := q.2.isLt
  have column : q.1.val = if e.inward then p.x e.port - 1 else p.x e.port + 1 := by
    cases hi : e.inward <;> simp only [hi, Bool.false_eq_true, ite_false, ite_true] at hx ⊢ <;> omega
  have row : q.2.val = if e.side = .upper then readDepth p e.level else p.H - readDepth p e.level := by
    cases hs : e.side <;> simp only [hs, reduceCtorEq, ite_false, ite_true] at hy ⊢ <;> omega
  have front := l.endpointFrontRod_back_mem p hl hM e he column row
  have full := l.endpointFrontRod_initial_full p hl hM haxes (l.canonical initial) (l.canonical target) e he
    (v := readDepth p e.level) (by omega) le_rfl
  have selected := (l.workingDepthCoordinates_mem p (e.level - 1) (by omega)).1
  simp only [Nat.sub_add_cancel level.1] at selected
  exact avoiding_box (canonical_ordinary_reader_avoiding_prefix l p hl hM haxes initial target hgate e he hsu hut accepted)
    (l.endpointOrdinaryBlockers_front_mem p hl hM haxes e he selected le_rfl column row) (full front)

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
