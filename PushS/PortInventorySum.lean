/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortFixedSeparation
import all PushS.PortEndpointIndexing
import all PushS.PortEndpointEnumeration
import all PushS.PortCoreCrossing
import all PushS.PortEndpointEnumeration
import all PushS.PortEndpointCrossing
import all PushS.PortEndpointCounts
import all PushS.PortEndpointSeparation
import all PushS.PortSegments
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Exact equal inventories for the actual complete physical recipes

The actual page partitions enumerate every port once. Their axis-bit sums coincide, so
the per-placement wire/core inventory identities cancel all physical signal bits.
Full fixed/signal separation then supplies the actual finite-cell inventory equality.

## Main results

* `signalSegments_card_eq`: every physical state has the same signal-hole count.
* `encodedSegments_holes_card_eq`: the full finite-cell hole inventories agree.
* `segmentRecipe_valid`, `canonicalRecipe_valid`: validity of the actual complete recipes.
-/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS.Reduction SegmentRecipe PageLevels

private def portList : Group → List ℕ
  | .wire a b => [a, b]
  | .triple a => [a, a + 1, a + 2]

private theorem portList_mem (g : Group) (k : ℕ) : k ∈ portList g ↔ k ∈ g.ports := by
  cases g <;> simp [portList, Group.ports]

private theorem page_ports_nodup (page : Page) (hp : page.Valid) :
    (page.groups.flatMap portList).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro g hg
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hg
    have hb := hp.bounded i
    change (portList (page.group i)).Nodup
    cases hg : page.group i with
    | wire a b =>
      simp only [hg, Group.left, Group.right] at hb
      simp [portList, Nat.ne_of_lt hb.1]
    | triple a => simp [portList]
  · exact page_parts_pairwise page hp portList (fun g k hk => (portList_mem g k).mp hk)

private theorem page_ports_perm (page : Page) (hp : page.Valid) :
    (page.groups.flatMap portList).Perm (List.range page.portCount) := by
  apply (List.perm_ext_iff_of_nodup (page_ports_nodup page hp) (List.nodup_range)).mpr
  intro k
  simp only [List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨g, hg, hk⟩
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hg
    exact port_bound page hp i ((portList_mem _ k).mp hk)
  · intro hk
    obtain ⟨i, hi, _⟩ := hp.partition k hk
    exact ⟨page.group i, List.get_mem _ _, (portList_mem _ k).mpr hi⟩

private theorem sum_flatMap {α β : Type} (xs : List α) (f : α → List β) (g : β → ℕ) :
    ((xs.flatMap f).map g).sum = (xs.map fun a => ((f a).map g).sum).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [List.flatMap_cons, List.map_append, List.sum_append, ih]

private theorem page_port_sum (page : Page) (hp : page.Valid) (f : ℕ → ℕ) :
    (page.groups.map fun g => ((portList g).map f).sum).sum =
      ((List.range page.portCount).map f).sum := by
  rw [← sum_flatMap]
  exact ((page_ports_perm page hp).map f).sum_eq

private def endCount (p : Scales.Parameters) (state : SignalState) (g : Placement) : ℕ :=
  ([⟨g.side, g.left, true, g.level, g.internal⟩,
    ⟨g.side, g.right, false, g.level, g.internal + if g.gate.isSome then 2 else 0⟩].map
      fun e => (pointHoles (endpointSegments (coordinates p) state e)).card).sum

private def coreCount (p : Scales.Parameters) (state : SignalState) (g : Placement) : ℕ :=
  (pointHoles (tripleSignal (coordinates p) state g)).card

private theorem placement_gate_side (l : PortLayout) {g : Placement} {kind : Shuttle.Kind}
    (hg : g ∈ placements l) (hk : g.gate = some kind) : g.side = .lower := by
  simp only [placements, List.mem_append, List.mem_map] at hg
  rcases hg with ⟨⟨⟨a, b⟩, i⟩, hi, rfl⟩ | ⟨⟨lower, i⟩, hi, rfl⟩
  · cases hk
  · cases lower <;> simp [encLowerGroup_elim, encLowerGroup_toSum] at hk ⊢

private theorem cores_pairwise (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (state : SignalState) : (placements l).Pairwise fun g h =>
      Disjoint (pointHoles (tripleSignal (coordinates p) state g))
        (pointHoles (tripleSignal (coordinates p) state h)) := by
  have hkeys : ((placements l).flatMap placementKeys).Nodup := by
    rw [← endpoint_keys]
    exact l.endpoints_keys_nodup hl
  refine List.Pairwise.imp_of_mem (fun {g h} hg hh hd => ?_) (List.nodup_flatMap.mp hkeys).2
  cases hgate : g.gate with
  | none => simp [tripleSignal, hgate, pointHoles]
  | some kind =>
    cases hhgate : h.gate with
    | none => simp [tripleSignal, hhgate, pointHoles]
    | some hkind =>
      have hgs := placement_gate_side l hg hgate
      have hhs := placement_gate_side l hh hhgate
      have hne : g.left ≠ h.left := by
        intro heq
        have hkG : (Side.lower, g.left) ∈ placementKeys g := by simp [placementKeys, hgs]
        have hkH : (Side.lower, g.left) ∈ placementKeys h := by simp [placementKeys, hhs, heq]
        exact List.disjoint_left.mp hd hkG hkH
      simp only [tripleSignal, hgate, hhgate, Option.elim_some]
      apply Finset.disjoint_left.mpr
      intro q hqg hqh
      have hG := gate_signal_span p state kind g.left g.internal hqg
      have hH := gate_signal_span p state hkind h.left h.internal hqh
      rcases lt_or_gt_of_ne hne with he | he
      · have hx := axes_separated p (show g.left + 1 < h.left + 1 by omega)
        omega
      · have hx := axes_separated p (show h.left + 1 < g.left + 1 by omega)
        omega

private theorem endpoint_gate_disjoint (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (state : SignalState) {e : Endpoint} (he : e ∈ l.endpoints) {kind : Shuttle.Kind}
    {first : ℕ} (hg : .gate kind first ∈ l.lowerGroups) (internal : ℕ) :
    Disjoint (pointHoles (endpointSegments (coordinates p) state e))
      (pointHoles (gateSegments (coordinates p) state kind first internal)) := by
  apply Finset.disjoint_left.mpr
  intro q hqe hqg
  by_cases hp : e.port = first + 1
  · cases hs : e.side with
    | upper =>
      have hE := signal_endpoint_page p state e hqe
      have hG := gate_signal_page p state kind first internal hqg
      simp only [hs, ite_true] at hE
      omega
    | lower => exact l.endpoints_lower_ne_gate_middle hl hg he hs hp
  · have hE := signal_span p state e hqe
    have hG := gate_signal_span p state kind first internal hqg
    rcases lt_or_gt_of_ne hp with hlt | hlt
    · have hx := axes_separated p hlt
      omega
    · have hx := axes_separated p hlt
      omega

private theorem endpoint_core_disjoint (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (state : SignalState) :
    Disjoint (pointHoles (l.endpoints.flatMap (endpointSegments (coordinates p) state)))
      (pointHoles ((placements l).flatMap (tripleSignal (coordinates p) state))) := by
  apply Finset.disjoint_left.mpr
  intro q he hg
  obtain ⟨se, hse, hqe⟩ := (mem_pointHoles _ q).mp he
  obtain ⟨e, he, hse⟩ := List.mem_flatMap.mp hse
  obtain ⟨sg, hsg, hqg⟩ := (mem_pointHoles _ q).mp hg
  obtain ⟨g, hg, hsg⟩ := List.mem_flatMap.mp hsg
  cases hgate : g.gate with
  | none => simp [tripleSignal, hgate] at hsg
  | some kind =>
    have hraw := placement_gate_mem l hg hgate
    have hd := endpoint_gate_disjoint l p hl state he hraw g.internal
    exact Finset.disjoint_left.mp hd ((mem_pointHoles _ q).mpr ⟨se, hse, hqe⟩)
      ((mem_pointHoles _ q).mpr ⟨sg, by simpa [tripleSignal, hgate] using hsg, hqg⟩)

private theorem end_count_sum (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (state : SignalState) :
    (pointHoles (l.endpoints.flatMap (endpointSegments (coordinates p) state))).card =
      ((placements l).map (endCount p state)).sum := by
  rw [pointHoles_flatMap_card (l.endpoints_signals_pairwise p hl state)]
  unfold endpoints
  rw [sum_flatMap]
  rfl

private theorem signal_count_sum (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (state : SignalState) : (pointHoles (l.signalSegments p state)).card =
    ((placements l).map (endCount p state)).sum + ((placements l).map (coreCount p state)).sum := by
  unfold signalSegments rawSignals
  rw [pointHoles_append, Finset.card_union_of_disjoint (endpoint_core_disjoint l p hl state),
    end_count_sum l p hl state, pointHoles_flatMap_card (cores_pairwise l p hl state)]
  rfl

private def charge (state : SignalState) (g : Placement) : ℕ :=
  (state.axes.getD g.left false).toNat + (state.axes.getD g.right false).toNat +
    if g.gate.isSome then (state.axes.getD (g.left + 1) false).toNat else 0

private def upperCharge (state : SignalState) (g : Placement) : ℕ :=
  if g.side = .upper then charge state g else 0

private def lowerCharge (state : SignalState) (g : Placement) : ℕ :=
  if g.side = .upper then 0 else charge state g

private def constant (g : Placement) : ℕ :=
  if g.side = .upper then 7 else g.gate.elim 9 (fun kind => kind.kappa.toNat + 19)

private theorem bit_complement (b : Bool) : b.toNat + (!b).toNat = 1 := by
  cases b <;> rfl

private theorem placement_inventory (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (state : SignalState) {g : Placement}
    (hg : g ∈ placements l) :
    endCount p state g + coreCount p state g + lowerCharge state g =
      constant g + upperCharge state g := by
  have hj := placement_level_bounds l hl hg
  have hjm := hj.2.trans hM
  have hL := endpointSegments_card p state ⟨g.side, g.left, true, g.level, g.internal⟩ hj.1 hjm
  have hR := endpointSegments_card p state ⟨g.side, g.right, false, g.level,
    g.internal + if g.gate.isSome then 2 else 0⟩ hj.1 hjm
  unfold endCount
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  rw [hL, hR]
  dsimp only
  have hbL := bit_complement (state.axes.getD g.left false)
  have hbR := bit_complement (state.axes.getD g.right false)
  have hbI := bit_complement (state.internal.getD g.internal false)
  have hbJ := bit_complement (state.internal.getD (g.internal + 2) false)
  have hside : Side.lower ≠ .upper := by decide
  cases hs : g.side with
  | upper =>
    cases hgate : g.gate with
    | none =>
      simp [coreCount, tripleSignal, hgate, lowerCharge, upperCharge, charge, constant, hs, pointHoles] at hbL hbR hbI hbJ ⊢
      omega
    | some kind =>
      have hlow := placement_gate_side l hg hgate
      rw [hs] at hlow
      cases hlow
  | lower =>
    cases hgate : g.gate with
    | none =>
      simp [coreCount, tripleSignal, hgate, lowerCharge, upperCharge, charge, constant, hs, pointHoles] at hbL hbR hbI hbJ ⊢
      omega
    | some kind =>
      have hc := gateSegments_card p state kind g.left g.internal
      dsimp only [coreCount, tripleSignal, lowerCharge, upperCharge, constant, charge] at hc ⊢
      simp only [hgate, Option.elim_some, hs, hside, ite_false, Option.isSome_some,
        ite_true, Bool.false_eq_true] at hc ⊢
      omega

private def upperPlacement (l : PortLayout) (ab : ℕ × ℕ) (i : ℕ) : Placement :=
  ⟨.upper, ab.1, ab.2, l.upperLevel i, i, none⟩

private def lowerPlacement (l : PortLayout) (g : LowerGroup) (i : ℕ) : Placement :=
  encLowerGroup_elim g
    (fun ab => ⟨.lower, ab.1, ab.2, l.lowerLevel i, l.lowerOffset i, none⟩)
    (fun ka => ⟨.lower, ka.2, ka.2 + 2, l.lowerLevel i, l.lowerOffset i, some ka.1⟩)

private def portSum (state : SignalState) (g : Group) : ℕ :=
  ((portList g).map fun k => (state.axes.getD k false).toNat).sum

@[local simp] private theorem upperCharge_upper (l : PortLayout) (state : SignalState)
    (ab : ℕ × ℕ) (i : ℕ) :
    upperCharge state (upperPlacement l ab i) = portSum state (.wire ab.1 ab.2) := by
  simp [upperPlacement, upperCharge, charge, portSum, portList]

@[local simp] private theorem lowerCharge_upper (l : PortLayout) (state : SignalState)
    (ab : ℕ × ℕ) (i : ℕ) : lowerCharge state (upperPlacement l ab i) = 0 := by
  simp [upperPlacement, lowerCharge]

@[local simp] private theorem upperCharge_lower (l : PortLayout) (state : SignalState)
    (g : LowerGroup) (i : ℕ) : upperCharge state (lowerPlacement l g i) = 0 := by
  cases g <;> simp [lowerPlacement, encLowerGroup_elim, encLowerGroup_toSum, upperCharge]

@[local simp] private theorem lowerCharge_lower (l : PortLayout) (state : SignalState)
    (g : LowerGroup) (i : ℕ) : lowerCharge state (lowerPlacement l g i) = portSum state g.shape := by
  cases g <;> simp [lowerPlacement, encLowerGroup_elim, encLowerGroup_toSum,
    lowerCharge, charge, portSum, portList, LowerGroup.shape]; omega

private theorem map_zipIdx_ignore {α β : Type} (xs : List α) (f : α → β) :
    xs.zipIdx.map (fun p => f p.1) = xs.map f := by
  have h := congrArg (fun as : List α => as.map f) (List.zipIdx_map_fst 0 xs)
  simpa only [List.map_map, Function.comp_def] using h

private theorem upperCharge_sum (l : PortLayout) (state : SignalState) :
    ((placements l).map (upperCharge state)).sum =
      (l.pages.upperPage.groups.map (portSum state)).sum := by
  simp only [placements, List.map_append, List.map_map]
  change ((l.upperPairs.zipIdx.map fun p => upperCharge state (upperPlacement l p.1 p.2)) ++
    (l.lowerGroups.zipIdx.map fun p => upperCharge state (lowerPlacement l p.1 p.2))).sum = _
  simp only [upperCharge_upper, upperCharge_lower, List.sum_append, List.sum_map_zero, Nat.add_zero]
  rw [map_zipIdx_ignore l.upperPairs (fun ab => portSum state (.wire ab.1 ab.2))]
  simp only [pages, Pages.upperPage, List.map_map, Function.comp_def]

private theorem lowerCharge_sum (l : PortLayout) (state : SignalState) :
    ((placements l).map (lowerCharge state)).sum =
      (l.pages.lowerPage.groups.map (portSum state)).sum := by
  simp only [placements, List.map_append, List.map_map]
  change ((l.upperPairs.zipIdx.map fun p => lowerCharge state (upperPlacement l p.1 p.2)) ++
    (l.lowerGroups.zipIdx.map fun p => lowerCharge state (lowerPlacement l p.1 p.2))).sum = _
  simp only [lowerCharge_upper, lowerCharge_lower, List.sum_append, List.sum_map_zero, Nat.zero_add]
  rw [map_zipIdx_ignore l.lowerGroups (fun g => portSum state g.shape)]
  simp only [pages, Pages.lowerPage, List.map_map, Function.comp_def]

private theorem charges_eq (l : PortLayout) (hl : l.pages.Valid) (state : SignalState) :
    ((placements l).map (upperCharge state)).sum =
      ((placements l).map (lowerCharge state)).sum := by
  rw [upperCharge_sum, lowerCharge_sum]
  exact (page_port_sum l.pages.upperPage hl.upper _).trans
    (page_port_sum l.pages.lowerPage hl.lower _).symm

private theorem signal_constant (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (state : SignalState) :
    (pointHoles (l.signalSegments p state)).card = ((placements l).map constant).sum := by
  have hsum : ((placements l).map fun g =>
      endCount p state g + coreCount p state g + lowerCharge state g).sum =
      ((placements l).map fun g => constant g + upperCharge state g).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro g hg
    exact placement_inventory l p hl hM state hg
  simp only [List.sum_map_add] at hsum
  have hcharges := charges_eq l hl state
  rw [signal_count_sum l p hl state]
  omega

/-- Every physical signal state on the valid fixed-level layout has the same actual hole count. -/
theorem signalSegments_card_eq (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (initial target : SignalState) :
    (pointHoles (l.signalSegments p initial)).card = (pointHoles (l.signalSegments p target)).card :=
  (signal_constant l p hl hM initial).trans (signal_constant l p hl hM target).symm

/-- The complete actual initial and target finite-cell hole inventories agree. -/
theorem encodedSegments_holes_card_eq (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState) :
    (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p initial)).card =
      (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p target)).card := by
  rw [l.encodedSegments_holes_card_eq_add p hl hM ha initial,
    l.encodedSegments_holes_card_eq_add p hl hM ha target, l.signalSegments_card_eq p hl hM initial target]

/-- The actual complete recipe is valid for any two physical signal states. -/
theorem segmentRecipe_valid (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState) :
    (l.segmentRecipe p initial target).Valid :=
  (l.segmentRecipe_valid_iff p initial target).mpr (l.encodedSegments_holes_card_eq p hl hM ha initial target)

/-- Canonical interface bits produce a valid actual marked instance recipe. -/
theorem canonicalRecipe_valid (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : List Bool) :
    (l.canonicalRecipe p initial target).Valid :=
  l.segmentRecipe_valid p hl hM ha (l.canonical initial) (l.canonical target)

end PushPuzzle.PushS.PortLayout
