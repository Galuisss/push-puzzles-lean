/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortOrdinaryFailureStep
public import PushS.PortCanonicalAccess
public import PushS.PortEndpointPocket
import all PushS.PortEndpointPocket
import all PushS.PortGateUpdates
import all PushS.PortBackground
import all PushS.PortSegments

/-! The actual outside-player W fault cannot reach any legal canonical storage target. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)
  (e : Endpoint) (he : e ∈ l.endpoints)

local notation "I" => l.physicalInstance p hl hM ha initial target

include he

/-- The same real successful suffix keeps the actual ordinary W fault and its outside player at every later state. -/
theorem physicalInstance_ordinary_failure_suffix {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) (fault : OrdinaryFaultReadout p e u)
    (hout : u.player ∉ ordinaryPocket p e) :
    ∃ _ : OrdinaryFaultReadout p e t, t.player ∉ ordinaryPocket p e := by
  let Inv (s : State (p.W + 1) (p.H + 1)) := ∃ _ : OrdinaryFaultReadout p e s, s.player ∉ ordinaryPocket p e
  have hpath : Relation.ReflTransGen (fun a b => Step (I).board none a b ∧ (Inv a → Inv b)) u t := by
    apply enrich_path hut
    intro a b hua hm hbt
    refine ⟨hm, ?_⟩
    rintro ⟨current, hplayer⟩
    exact l.physicalInstance_ordinary_failure_step p hl hM ha initial target e he (hsu.trans hua) hm hbt ht current hplayer
  have hstart : Inv u := ⟨fault, hout⟩
  have propagate {a b : State (p.W + 1) (p.H + 1)}
      (hr : Relation.ReflTransGen (fun a b => Step (I).board none a b ∧ (Inv a → Inv b)) a b)
      (hinit : Inv a) : Inv b := by
    induction hr with
    | refl => exact hinit
    | tail _ hm ih => exact hm.2 ih
  exact propagate hpath hstart

end Solution

/-- Every legal canonical storage target excludes every actual ordinary W fault. -/
theorem physicalInstance_ordinary_failure_target (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial : SignalState) (axes : List Bool) (hlegal : l.InputLegal axes)
    (e : Endpoint) (he : e ∈ l.endpoints) {t : State (p.W + 1) (p.H + 1)}
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial (l.canonical axes)).board.goals)
    (fault : OrdinaryFaultReadout p e t) : False := by
  have hY := readDepth_ge p (l.endpoints_level_bounds p hl hM he).1 (l.endpoints_level_bounds p hl hM he).2
  have hH := readDepth_add_lt_H p e.level
  have target_hole {q : Cell (p.W + 1) (p.H + 1)}
      (hq : q ∈ (l.cornerState p (l.canonical axes)).empty) : q ∉ t.boxes := by
    change q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p (l.canonical axes)) at hq
    have heq : ((l.physicalInstance p hl hM ha initial (l.canonical axes)).board.goals :
        Finset (Cell (p.W + 1) (p.H + 1)))ᶜ =
        SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p (l.canonical axes)) :=
      l.physicalInstance_goal_holes p hl hM ha initial (l.canonical axes)
    rw [← heq] at hq
    intro hb
    rw [ht] at hb
    exact Finset.mem_compl.mp hq hb
  cases hb : (if e.side = .upper then axes.getD e.port false else !(axes.getD e.port false)) with
  | true =>
    let q := pocketCell l p hl ha e he 0 (readDepth p e.level + 2) le_rfl
    have hx := pocket_axis_column l p hl ha e he (readDepth p e.level + 2) le_rfl
    have hslot := axis_slot_mem p (l.canonical axes) e (q := q) hx (readDepth p e.level + 2) (by omega) (by
      change readDepth p e.level + 2 ≤ readDepth p e.level + 1 +
        (if e.side = .upper then axes.getD e.port false else !(axes.getD e.port false)).toNat
      rw [hb, Bool.toNat_true]) rfl
    have hh := endpoint_signal_hole l p (l.canonical axes) e he ((finite_take_drop p _ 1 q).mpr (Or.inl hslot))
    have hdepth : (if e.side = .upper then q.2.val else p.H - q.2.val) = readDepth p e.level + 2 := by
      cases hs : e.side <;> simp only [q, pocketCell, onSide, coordinates, hs, reduceCtorEq, ite_true, ite_false]; omega
    exact target_hole hh (fault.axis_word.fault_axis_box fault.axis_failed (by omega) hx (Or.inr hdepth))
  | false =>
    have hrecv := l.canonical_endpoint_receiving axes hlegal he hb
    let q := pocketCell l p hl ha e he 2 (readDepth p e.level) (by omega)
    have hslot := horizontal_slot_mem p (l.canonical axes) e (q := q) 2 (by omega) (by
      change 2 ≤ 1 + (if e.inward then (l.canonical axes).internal.getD e.internal false
        else !((l.canonical axes).internal.getD e.internal false)).toNat
      rw [hrecv, Bool.toNat_true]) rfl rfl
    have hh := endpoint_signal_hole l p (l.canonical axes) e he ((finite_take_drop p _ 1 q).mpr (Or.inr hslot))
    exact target_hole hh (fault.horizontal_word.fault_probe_box fault.horizontal_failed rfl rfl)

/-- An actual W fault reached with its player outside has no successful suffix to a legal canonical target. -/
theorem physicalInstance_ordinary_failure_impossible (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial : SignalState) (axes : List Bool) (hlegal : l.InputLegal axes)
    (e : Endpoint) (he : e ∈ l.endpoints) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial (l.canonical axes)).board none
      (l.physicalInstance p hl hM ha initial (l.canonical axes)).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial (l.canonical axes)).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial (l.canonical axes)).board.goals)
    (fault : OrdinaryFaultReadout p e u) (hout : u.player ∉ ordinaryPocket p e) : False := by
  obtain ⟨finalFault, _⟩ := l.physicalInstance_ordinary_failure_suffix p hl hM ha initial (l.canonical axes) e he hsu hut ht fault hout
  exact l.physicalInstance_ordinary_failure_target p hl hM ha initial axes hlegal e he ht finalFault

end PushPuzzle.PushS.PortLayout
