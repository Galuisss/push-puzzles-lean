/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortStreetSupport
public import PushS.ClosureLabels

/-!
# Actual initial blockers and frozen background identities

Central holes are permanently excluded and every push ray lies on an original street.
Together these facts supply the initial blocker set for the geometric freezing closure.
-/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS

/-- The actual solid background outside the original streets and the central marker holes. -/
@[expose] noncomputable def backgroundBoxes (l : PortLayout) (p : Scales.Parameters) :
    Finset (Cell (p.W + 1) (p.H + 1)) := by
  classical
  exact Finset.univ.filter fun q =>
    q ∉ Support.streets (l.streetColumnSet p) (l.workingRowSet p) ∧ q ∉ l.centralMarkers p

/-- A background cell lies outside the original streets and the central holes. -/
theorem mem_backgroundBoxes (l : PortLayout) (p : Scales.Parameters)
    (q : Cell (p.W + 1) (p.H + 1)) :
    q ∈ l.backgroundBoxes p ↔
      q ∉ Support.streets (l.streetColumnSet p) (l.workingRowSet p) ∧ q ∉ l.centralMarkers p := by
  classical
  simp only [backgroundBoxes, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Permanent central holes and the solid background form the initial geometric blockers. -/
@[expose] noncomputable def geometricBlockers (l : PortLayout) (p : Scales.Parameters) :
    Finset (Cell (p.W + 1) (p.H + 1)) := l.centralMarkers p ∪ l.backgroundBoxes p

private theorem enrich_path {α : Type} {r q : α → α → Prop} {s t : α}
    (hr : Relation.ReflTransGen r s t) :
    (∀ u v, Relation.ReflTransGen r s u → r u v → Relation.ReflTransGen r v t → q u v) →
      Relation.ReflTransGen q s t := by
  induction hr with
  | refl => exact fun _ => .refl
  | @tail u v hsu huv ih =>
    intro h
    exact (ih fun a b hsa hab hbu => h a b hsa hab (hbu.tail huv)).tail (h u v hsu huv .refl)

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)

/-- Every background cell of the actual instance remains occupied at every solution prefix. -/
theorem physicalInstance_background_full {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    l.backgroundBoxes p ⊆ u.boxes := by
  classical
  intro q hq
  obtain ⟨hstreet, hcentral⟩ := (l.mem_backgroundBoxes p q).mp hq
  by_contra hbox
  apply hstreet
  apply l.physicalInstance_filled_supported_at p hl hM ha initial target hsu hut ht q
  exact fun h => (Finset.mem_union.mp h).elim hbox hcentral

/-- Every actual step with a successful completion avoids the computed geometric blockers. -/
theorem physicalInstance_step_avoiding {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hm : Step (l.physicalInstance p hl hM ha initial target).board none u v)
    (hvt : Reachable (l.physicalInstance p hl hM ha initial target).board none v t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    Freeze.AvoidingStep (l.physicalInstance p hl hM ha initial target).board none
      (l.geometricBlockers p) u v := by
  refine ⟨hm, ?_⟩
  intro d n r hn hp hb i hblock
  have hGu := l.physicalInstance_central_excluded p hl hM ha initial target hsu
    ((Relation.ReflTransGen.single hm).trans hvt) ht
  have hGv := l.physicalInstance_central_excluded p hl hM ha initial target (hsu.tail hm) hvt ht
  rcases Finset.mem_union.mp hblock with hcentral | hbackground
  · exact Blocked.run_avoids r hGu hGv hb i hcentral
  · have hstreet := l.physicalInstance_push_run_on_streets p hl hM ha initial target
      hsu r hn hp hb hvt ht i
    exact ((l.mem_backgroundBoxes p (r.cell i)).mp hbackground).1 hstreet

/-- Every solution prefix avoids the computed initial blockers along each complete push ray. -/
theorem physicalInstance_avoiding_prefix {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    Relation.ReflTransGen (Freeze.AvoidingStep
      (l.physicalInstance p hl hM ha initial target).board none (l.geometricBlockers p))
      (l.physicalInstance p hl hM ha initial target).initial u := by
  apply enrich_path hsu
  intro a b hsa hm hbu
  exact l.physicalInstance_step_avoiding p hl hM ha initial target hsa hm (hbu.trans hut) ht

/-- Every actual solution carries complete push-ray avoidance of the computed initial blockers. -/
theorem physicalInstance_avoiding {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    Relation.ReflTransGen (Freeze.AvoidingStep
      (l.physicalInstance p hl hM ha initial target).board none (l.geometricBlockers p))
      (l.physicalInstance p hl hM ha initial target).initial t :=
  l.physicalInstance_avoiding_prefix p hl hM ha initial target hr .refl ht

/-- The complete physical lifting of a solution fixes every background box at its initial cell. -/
theorem physicalInstance_background_frozen {ι : Type} [Fintype ι]
    (S : LabelledState ι (p.W + 1) (p.H + 1))
    (hS : S.state = (l.physicalInstance p hl hM ha initial target).initial)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    ∃ T : LabelledState ι (p.W + 1) (p.H + 1), T.state = t ∧
      Labels.GuardedReachable (l.physicalInstance p hl hM ha initial target).board none
        (l.geometricBlockers p) S T ∧
      ∀ i, S.position i ∈ l.backgroundBoxes p → T.position i = S.position i := by
  have hguard := l.physicalInstance_avoiding p hl hM ha initial target hr ht
  rw [← hS] at hguard
  obtain ⟨T, hT, hlabels⟩ := Labels.lift_guarded hguard
  exact ⟨T, hT, hlabels, fun i hi => hlabels.position i (Finset.mem_union_right _ hi)⟩

end Solution
end PushPuzzle.PushS.PortLayout
