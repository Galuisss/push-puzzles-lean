/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceGateMarkers
public import Push.AcceptanceSoundnessPageClosure
public import Push.FirstExit
public import PushS.PortGateBlockers

/-! The actual accepted marker and walk certificate supplies the complete gate private first-motion closure. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate

private theorem canonical_gate_basis_step_of_walks {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (step : Step (I).board none u v)
    (hvt : Reachable (I).board none v t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (deeper : DeeperWalkInvariant l p hl hM haxes initial target 1 t)
    (walks : PublicWalkInvariant l p hl hM haxes initial target t) :
    Freeze.AvoidingStep (I).board none
      ((l.pageBlockers p hl ∪ l.gateInterlevelMarkers p) ∪ l.gateHalfMarkers p) u v := by
  have hut := (Relation.ReflTransGen.single step).trans hvt
  exact ((canonical_page_step_avoiding l p hl hM haxes initial target hgate hsu step hvt accepted).union_excluded
    (canonical_gate_interlevel_excluded_of_deeper l p hl hM haxes initial target hsu hut accepted deeper)
    (canonical_gate_interlevel_excluded_of_deeper l p hl hM haxes initial target (hsu.tail step) hvt accepted deeper)).union_excluded
      (canonical_gate_half_excluded_of_public l p hl hM haxes initial target hsu hut accepted walks)
      (canonical_gate_half_excluded_of_public l p hl hM haxes initial target (hsu.tail step) hvt accepted walks)

private theorem canonical_gate_basis_prefix_of_walks {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (deeper : DeeperWalkInvariant l p hl hM haxes initial target 1 t)
    (walks : PublicWalkInvariant l p hl hM haxes initial target t) :
    Relation.ReflTransGen (Freeze.AvoidingStep (I).board none
      ((l.pageBlockers p hl ∪ l.gateInterlevelMarkers p) ∪ l.gateHalfMarkers p)) (I).initial u := by
  apply Path.enrich hsu
  intro a b hsa step hbu
  exact canonical_gate_basis_step_of_walks l p hl hM haxes initial target hgate hsa step (hbu.trans hut) accepted deeper walks

/-- Every actual accepted prefix avoids the full gate private closure under the certified walk invariants. -/
theorem canonical_gate_private_avoiding_of_walks {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (deeper : DeeperWalkInvariant l p hl hM haxes initial target 1 t)
    (walks : PublicWalkInvariant l p hl hM haxes initial target t) :
    Relation.ReflTransGen (Freeze.AvoidingStep (I).board none (l.gatePrivateBlockers p hl hM haxes hi)) (I).initial u :=
  (l.gatePrivateBlockers_closure p hl hM haxes (l.canonical initial) (l.canonical target) hi).reachable
    (canonical_gate_basis_prefix_of_walks l p hl hM haxes initial target hgate hsu hut accepted deeper walks)

/-- The complete push ray of the actual next step avoids those same private blockers. -/
theorem canonical_gate_private_step_avoiding_of_walks {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (step : Step (I).board none u v)
    (hvt : Reachable (I).board none v t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (deeper : DeeperWalkInvariant l p hl hM haxes initial target 1 t)
    (walks : PublicWalkInvariant l p hl hM haxes initial target t) :
    Freeze.AvoidingStep (I).board none (l.gatePrivateBlockers p hl hM haxes hi) u v :=
  (l.gatePrivateBlockers_closure p hl hM haxes (l.canonical initial) (l.canonical target) hi).step
    (canonical_gate_basis_prefix_of_walks l p hl hM haxes initial target hgate hsu
      ((Relation.ReflTransGen.single step).trans hvt) accepted deeper walks)
    (canonical_gate_basis_step_of_walks l p hl hM haxes initial target hgate hsu step hvt accepted deeper walks)

/-- Every labelled private-blocker box keeps its original identity on the same actual accepted trajectory. -/
theorem canonical_gate_private_frozen_of_walks {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    {ι : Type} [Fintype ι] (S : LabelledState ι (p.W + 1) (p.H + 1))
    (hS : S.state = (I).initial) {t : State (p.W + 1) (p.H + 1)}
    (run : Reachable (I).board none (I).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (deeper : DeeperWalkInvariant l p hl hM haxes initial target 1 t)
    (walks : PublicWalkInvariant l p hl hM haxes initial target t) :
    ∃ T : LabelledState ι (p.W + 1) (p.H + 1), T.state = t ∧
      Labels.GuardedReachable (I).board none (l.gatePrivateBlockers p hl hM haxes hi) S T ∧
      ∀ i, S.position i ∈ l.gatePrivateBlockers p hl hM haxes hi → T.position i = S.position i := by
  have guard := canonical_gate_private_avoiding_of_walks l p hl hM haxes initial target hgate hi run .refl accepted deeper walks
  rw [← hS] at guard
  obtain ⟨T, ht, labels⟩ := Labels.lift_guarded guard
  exact ⟨T, ht, labels, fun i hi => labels.position i hi⟩

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
