/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortEndpointAxisReadout
public import PushS.PortEndpointHorizontalReadout
public import PushS.PortOrdinaryBlockers
import all PushS.PortEndpointFrontRod
import all PushS.PortStreetSeparation
import all PushS.PortPageBackground
import all PushS.PortBackground
import all PushS.PortSegments

/-! The actual three-cell ordinary pocket is inaccessible after losing both input supplies. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS

private def localX (p : Scales.Parameters) (e : Endpoint) (q : Cell (p.W + 1) (p.H + 1)) : ℤ :=
  if e.inward then (q.1.val : ℤ) - p.x e.port else (p.x e.port : ℤ) - q.1.val

private def localDepth (p : Scales.Parameters) (e : Endpoint) (q : Cell (p.W + 1) (p.H + 1)) : ℕ :=
  if e.side = .upper then q.2.val else p.H - q.2.val

/-- The ordinary endpoint's actual three-cell L, reflected on the lower page. -/
@[expose] def ordinaryPocket (p : Scales.Parameters) (e : Endpoint) : Finset (Cell (p.W + 1) (p.H + 1)) :=
  Finset.univ.filter fun q =>
    ((if e.inward then (q.1.val : ℤ) - p.x e.port else (p.x e.port : ℤ) - q.1.val) = 0 ∧
      ((if e.side = .upper then q.2.val else p.H - q.2.val) = readDepth p e.level ∨
        (if e.side = .upper then q.2.val else p.H - q.2.val) = readDepth p e.level + 1)) ∨
      ((if e.inward then (q.1.val : ℤ) - p.x e.port else (p.x e.port : ℤ) - q.1.val) = 1 ∧
        (if e.side = .upper then q.2.val else p.H - q.2.val) = readDepth p e.level)

private theorem outside_neighbor (p : Scales.Parameters) (e : Endpoint) {d : Direction}
    {q r : Cell (p.W + 1) (p.H + 1)} (ha : Adjacent d q r)
    (hq : q ∉ ordinaryPocket p e) (hr : r ∈ ordinaryPocket p e) (hY : 3 ≤ readDepth p e.level) :
    (localX p e q = 0 ∧ (localDepth p e q = readDepth p e.level - 1 ∨ localDepth p e q = readDepth p e.level + 2)) ∨
      (localX p e q = 2 ∧ localDepth p e q = readDepth p e.level) ∨
      (localX p e q = -1 ∧ localDepth p e q = readDepth p e.level) ∨
      ((localX p e q = -1 ∨ localX p e q = 1) ∧
        (localDepth p e q = readDepth p e.level - 1 ∨ localDepth p e q = readDepth p e.level + 1)) := by
  have hqy := q.2.isLt
  have hry := r.2.isLt
  simp only [ordinaryPocket, Finset.mem_filter, Finset.mem_univ, true_and] at hq hr
  cases d <;> cases hi : e.inward <;> cases hs : e.side <;>
    simp only [localX, localDepth, hi, hs, Bool.false_eq_true, reduceCtorEq, ite_false, ite_true, Adjacent] at ha hq hr ⊢ <;> omega

private theorem avoiding_box {w h : ℕ} {B : Board w h} {cap : Option ℕ} {G : Finset (Cell w h)}
    {s t : State w h} (hr : Relation.ReflTransGen (Freeze.AvoidingStep B cap G) s t)
    {q : Cell w h} (hq : q ∈ G) (hb : q ∈ s.boxes) : q ∈ t.boxes := by
  induction hr with
  | refl => exact hb
  | @tail u v _ hm ih =>
    obtain ⟨d, hmove⟩ := hm.1
    cases hmove with
    | walk _ _ _ _ hboxes => simpa only [hboxes] using ih
    | @push n _ hn _ run hp hboxes =>
      rw [hboxes]
      exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun heq => hm.2 d n run hn hp hboxes 1 (heq ▸ hq), ih⟩)

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)
  (e : Endpoint) (he : e ∈ l.endpoints)

local notation "I" => l.physicalInstance p hl hM ha initial target

include he

private theorem diagonal_box {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : localX p e q = -1 ∨ localX p e q = 1)
    (hy : localDepth p e q = readDepth p e.level - 1 ∨ localDepth p e q = readDepth p e.level + 1) : q ∈ u.boxes := by
  have hxe := x_even p e.port
  have hye := readDepth_even p e.level
  have hHe := H_even p
  have hD := readDepth_add_lt_D p e.level
  have hH : p.H = 2 * p.D := rfl
  have hqy := q.2.isLt
  have hY := readDepth_ge p (l.endpoints_level_bounds p hl hM he).1 (l.endpoints_level_bounds p hl hM he).2
  have hxodd : q.1.val % 2 = 1 := by
    cases hi : e.inward <;> simp only [localX, hi, Bool.false_eq_true, ite_false, ite_true] at hx <;> omega
  have hyodd : q.2.val % 2 = 1 := by
    cases hs : e.side <;> simp only [localDepth, hs, reduceCtorEq, ite_false, ite_true] at hy <;> omega
  apply l.physicalInstance_background_full p hl hM ha initial target hsu hut ht
  apply (l.mem_backgroundBoxes p q).mpr
  constructor
  · rintro (hcol | hrow)
    · have := l.streetColumnSet_even p hcol
      omega
    · have := l.workingRowSet_even p hrow
      omega
  · intro hc
    have hband := (Finset.mem_filter.mp hc).2
    cases hs : e.side <;> simp only [localDepth, hs, reduceCtorEq, ite_false, ite_true] at hy <;> omega

private theorem outward_box {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : localX p e q = -1) (hy : localDepth p e q = readDepth p e.level) : q ∈ u.boxes := by
  have hY := readDepth_ge p (l.endpoints_level_bounds p hl hM he).1 (l.endpoints_level_bounds p hl hM he).2
  have hHy := readDepth_add_lt_H p e.level
  have hqy := q.2.isLt
  have hqx : q.1.val = if e.inward then p.x e.port - 1 else p.x e.port + 1 := by
    cases hi : e.inward <;> simp only [localX, hi, Bool.false_eq_true, ite_false, ite_true] at hx ⊢ <;> omega
  have hqy' : q.2.val = if e.side = .upper then readDepth p e.level else p.H - readDepth p e.level := by
    cases hs : e.side <;> simp only [localDepth, hs, reduceCtorEq, ite_false, ite_true] at hy ⊢ <;> omega
  have hfront := l.endpointFrontRod_back_mem p hl hM e he hqx hqy'
  have hfull := l.endpointFrontRod_initial_full p hl hM ha initial target e he (v := readDepth p e.level) (by omega) le_rfl
  have hlevel := l.endpoints_level_bounds p hl hM he
  have hselected := (l.workingDepthCoordinates_mem p (e.level - 1) (by omega)).1
  simp only [Nat.sub_add_cancel hlevel.1] at hselected
  exact avoiding_box (l.physicalInstance_ordinary_reader_avoiding_prefix p hl hM ha initial target e he hsu hut ht)
    (l.endpointOrdinaryBlockers_front_mem p hl hM ha e he hselected le_rfl hqx hqy') (hfull hfront)

/-- At a failed ordinary interface, every outside neighbour of the actual pocket remains occupied. -/
private theorem ordinary_fault_boundary {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) {parameter shift : ℕ}
    (haxis : EndpointAxisReadout p e u parameter shift) (hbad : 2 ≤ parameter)
    (hhorizontal : ∀ q : Cell (p.W + 1) (p.H + 1),
      q.1.val = (if e.inward then p.x e.port + 2 else p.x e.port - 2) →
      q.2.val = (if e.side = .upper then readDepth p e.level else p.H - readDepth p e.level) → q ∈ u.boxes)
    {d : Direction} {q r : Cell (p.W + 1) (p.H + 1)} (hadj : Adjacent d q r)
    (hq : q ∉ ordinaryPocket p e) (hr : r ∈ ordinaryPocket p e) : q ∈ u.boxes := by
  have hY := readDepth_ge p (l.endpoints_level_bounds p hl hM he).1 (l.endpoints_level_bounds p hl hM he).2
  have hHy := readDepth_add_lt_H p e.level
  have hqy := q.2.isLt
  rcases outside_neighbor p e hadj hq hr (by omega) with ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · apply haxis.fault_axis_box hbad (by omega) ?_ hy
    cases hi : e.inward <;> simp only [localX, hi, Bool.false_eq_true, ite_false, ite_true] at hx <;> omega
  · apply hhorizontal q
    · cases hi : e.inward <;> simp only [localX, hi, Bool.false_eq_true, ite_false, ite_true] at hx ⊢ <;> omega
    · cases hs : e.side <;> simp only [localDepth, hs, reduceCtorEq, ite_false, ite_true] at hy ⊢ <;> omega
  · exact outward_box l p hl hM ha initial target e he hsu hut ht hx hy
  · exact diagonal_box l p hl hM ha initial target e he hsu hut ht hx hy

/-- A real successful step from outside a failed ordinary pocket keeps its player outside that pocket. -/
private theorem ordinary_fault_no_entry {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals) {parameter shift : ℕ}
    (haxis : EndpointAxisReadout p e u parameter shift) (hbad : 2 ≤ parameter)
    (hhorizontal : ∀ q : Cell (p.W + 1) (p.H + 1),
      q.1.val = (if e.inward then p.x e.port + 2 else p.x e.port - 2) →
      q.2.val = (if e.side = .upper then readDepth p e.level else p.H - readDepth p e.level) → q ∈ u.boxes)
    (hout : u.player ∉ ordinaryPocket p e) : v.player ∉ ordinaryPocket p e := by
  intro hin
  have hb := ordinary_fault_boundary l p hl hM ha initial target e he hsu
    ((Relation.ReflTransGen.single hm).trans hvt) ht haxis hbad hhorizontal
    (players_adjacent hm.choose_spec) hout hin
  exact hm.choose_spec.valid_source.2.2 hb

/-- The actual W fault isolates its three-cell pocket from every next real successful player move. -/
theorem physicalInstance_ordinary_failure_no_entry {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals) {parameter shift horizontal : ℕ}
    (haxis : EndpointAxisReadout p e u parameter shift) (hbadAxis : 2 ≤ parameter)
    (hread : EndpointHorizontalReadout p e u horizontal) (hbadHorizontal : horizontal ≤ 1)
    (hout : u.player ∉ ordinaryPocket p e) : v.player ∉ ordinaryPocket p e :=
  ordinary_fault_no_entry l p hl hM ha initial target e he hsu hm hvt ht haxis hbadAxis
    (fun _ hx hy => hread.fault_probe_box hbadHorizontal hx hy) hout

end Solution
end PushPuzzle.PushS.PortLayout
