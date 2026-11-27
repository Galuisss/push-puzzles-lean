/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortEndpointConnections
public import PushS.PortEndpointBranch
import all PushS.PortEndpointConnections
import all PushS.PortEndpointBranch
import all PushS.PortGateRail
import all PushS.PortGateUpdates
import all PushS.PortEndpointCounts
import all PushS.PortSegments

/-! Concrete frame access to every signal hole of an ordinary three-cell-L endpoint pocket. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

private def axisInput (state : SignalState) (e : Endpoint) : Bool :=
  if e.side = .upper then state.axes.getD e.port false else !(state.axes.getD e.port false)

private def horizontalInput (state : SignalState) (e : Endpoint) : Bool :=
  if e.inward then state.internal.getD e.internal false else !(state.internal.getD e.internal false)

private def pocketCell (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (ha : l.portCount ≤ p.axes) (e : Endpoint) (he : e ∈ l.endpoints) (dx : Fin 3)
    (depth : ℕ) (hd : depth ≤ readDepth p e.level + 2) : Cell (p.W + 1) (p.H + 1) :=
  (⟨inward (p.x e.port) e.inward dx.val, by
    have hx := x_add_readLength_lt_W p ((l.endpoints_port_lt hl he).trans_le ha) 0
    have hi := dx.isLt
    cases e.inward <;> simp only [inward, Bool.false_eq_true, ite_false, ite_true] <;> omega⟩,
    ⟨onSide (coordinates p) e.side depth, by
      have hH := readDepth_add_lt_H p e.level
      cases e.side <;> simp only [onSide, reduceCtorEq, ite_true, ite_false, coordinates] <;> omega⟩)

private theorem endpoint_signal_hole (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    (e : Endpoint) (he : e ∈ l.endpoints) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (endpointSegments (coordinates p) state e)) :
    q ∈ (l.cornerState p state).empty := by
  obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hq
  exact (SegmentRecipe.mem_holes _ q).mpr ⟨s,
    List.mem_append_right _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨e, he, hs⟩)), hc⟩

private theorem axis_slot_mem (p : Scales.Parameters) (state : SignalState) (e : Endpoint)
    {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val = p.x e.port)
    (v : ℕ) (hlo : readDepth p e.level ≤ v) (hhi : v ≤ readDepth p e.level + 1 + (axisInput state e).toNat)
    (hy : q.2.val = onSide (coordinates p) e.side v) :
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) ((endpointSegments (coordinates p) state e).take 1) := by
  apply (finite_point_mem p _ q).mpr
  apply (axis_mem p state e _).mpr
  have hb := Bool.toNat_le (axisInput state e)
  have hH := readDepth_add_lt_H p e.level
  refine ⟨hx, ?_⟩
  cases hs : e.side <;>
    simp only [axisInput, hs, onSide, reduceCtorEq, ite_true, ite_false,
      show (coordinates p).H = p.H from rfl] at hhi hy ⊢ <;> omega

private theorem horizontal_slot_mem (p : Scales.Parameters) (state : SignalState) (e : Endpoint)
    {q : Cell (p.W + 1) (p.H + 1)} (dx : ℕ) (hlo : 1 ≤ dx) (hhi : dx ≤ 1 + (horizontalInput state e).toNat)
    (hx : q.1.val = inward (p.x e.port) e.inward dx)
    (hy : q.2.val = onSide (coordinates p) e.side (readDepth p e.level)) :
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) ((endpointSegments (coordinates p) state e).drop 1) := by
  apply (finite_point_mem p _ q).mpr
  apply (endpoint_horizontal_mem p state e _).mpr
  refine ⟨hy, ?_⟩
  have hb := Bool.toNat_le (horizontalInput state e)
  have hlow := readLength_add_lt_x p e.port 0
  cases hi : e.inward <;>
    simp only [horizontalInput, inward, hi, Bool.false_eq_true, ite_false, ite_true] at hhi hb hx ⊢ <;> omega

private theorem axis_interval_hole (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    (e : Endpoint) (he : e ∈ l.endpoints) (q r : Cell (p.W + 1) (p.H + 1))
    (hq : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) ((endpointSegments (coordinates p) state e).take 1))
    (hr : r ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) ((endpointSegments (coordinates p) state e).take 1))
    (z : Cell (p.W + 1) (p.H + 1)) (hx : z.1 = q.1)
    (hlo : min q.2.val r.2.val ≤ z.2.val) (hhi : z.2.val ≤ max q.2.val r.2.val) :
    z ∈ (l.cornerState p state).empty := by
  have hq := (axis_mem p state e _).mp ((finite_point_mem p _ q).mp hq)
  have hr := (axis_mem p state e _).mp ((finite_point_mem p _ r).mp hr)
  apply endpoint_signal_hole l p state e he
  apply (finite_take_drop p _ 1 z).mpr
  left
  apply (finite_point_mem p _ z).mpr
  apply (axis_mem p state e _).mpr
  exact ⟨(congrArg Fin.val hx).trans hq.1, by omega, by omega⟩

private theorem pocket_row_hole (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    (e : Endpoint) (he : e ∈ l.endpoints) (q : Cell (p.W + 1) (p.H + 1))
    (hq : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) ((endpointSegments (coordinates p) state e).drop 1))
    (z : Cell (p.W + 1) (p.H + 1)) (hy : z.2.val = onSide (coordinates p) e.side (readDepth p e.level))
    (hlo : min (p.x e.port) q.1.val ≤ z.1.val) (hhi : z.1.val ≤ max (p.x e.port) q.1.val) :
    z ∈ (l.cornerState p state).empty := by
  by_cases hx : z.1.val = p.x e.port
  · apply endpoint_signal_hole l p state e he
    exact (finite_take_drop p _ 1 z).mpr (Or.inl (axis_slot_mem p state e hx _ le_rfl (by omega) hy))
  · have hm := (endpoint_horizontal_mem p state e _).mp ((finite_point_mem p _ q).mp hq)
    apply endpoint_signal_hole l p state e he
    apply (finite_take_drop p _ 1 z).mpr
    right
    apply (finite_point_mem p _ z).mpr
    apply (endpoint_horizontal_mem p state e _).mpr
    refine ⟨hy, ?_⟩
    have hh := hm.2
    have hlow := readLength_add_lt_x p e.port 0
    split at hh
    · rename_i hd
      simp only [ite_eq_left hd]
      exact ⟨by omega, by omega⟩
    · rename_i hd
      simp only [ite_eq_right hd]
      exact ⟨by omega, by omega⟩

private theorem long_access_hole (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (state : SignalState)
    (e : Endpoint) (he : e ∈ l.endpoints) (haxis : axisInput state e = true)
    (q : Cell (p.W + 1) (p.H + 1))
    (hy : q.2.val = onSide (coordinates p) e.side (readDepth p e.level + 2))
    (hlo : min (EndpointStreet.f.column p e) (p.x e.port) ≤ q.1.val)
    (hhi : q.1.val ≤ max (EndpointStreet.f.column p e) (p.x e.port)) :
    q ∈ (l.cornerState p state).empty := by
  by_cases hx : q.1.val = p.x e.port
  · apply endpoint_signal_hole l p state e he
    apply (finite_take_drop p _ 1 q).mpr
    exact Or.inl (axis_slot_mem p state e hx _ (by omega) (by rw [haxis]; simp only [Bool.toNat_true]; omega) hy)
  by_cases hf : q.1.val = EndpointStreet.f.column p e
  · have hq : q = endpointStreetCell l p hl ha e he .f (readDepth p e.level + 2) le_rfl :=
      Prod.ext (Fin.ext hf) (Fin.ext hy)
    rw [hq]
    exact l.endpointStreet_hole p hl hM ha state e he .f _ le_rfl
  · apply l.endpointLongBranch_subset_encoded p hl hM state e he
    apply (mem_endpointLongBranch p e q).mpr
    refine ⟨hy, ?_⟩
    rw [EndpointStreet.column_f] at hlo hhi hf ⊢
    have hlevels := l.endpoints_level_bounds p hl hM he
    have hL := readLength_ge p hlevels.1 hlevels.2
    have hx0 := readLength_add_lt_x p e.port e.level
    split <;> simp_all only [Bool.false_eq_true, ite_false, ite_true] <;> omega

private theorem pocket_axis_column (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (ha : l.portCount ≤ p.axes) (e : Endpoint) (he : e ∈ l.endpoints)
    (v : ℕ) (hv : v ≤ readDepth p e.level + 2) :
    (pocketCell l p hl ha e he 0 v hv).1.val = p.x e.port := by
  dsimp only [pocketCell, inward]
  split <;> rfl

private theorem center_connected_of_axis (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (state : SignalState)
    (e : Endpoint) (he : e ∈ l.endpoints) (haxis : axisInput state e = true)
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) (cap : Option ℕ) :
    FrameConnection l p state B cap (pocketCell l p hl ha e he 0 (readDepth p e.level) (by omega)) := by
  let w := pocketCell l p hl ha e he 0 (readDepth p e.level) (by omega)
  let v := pocketCell l p hl ha e he 0 (readDepth p e.level + 2) le_rfl
  have hwx := pocket_axis_column l p hl ha e he (readDepth p e.level) (by omega)
  have hvx := pocket_axis_column l p hl ha e he (readDepth p e.level + 2) le_rfl
  have hw := axis_slot_mem p state e (q := w) hwx _ le_rfl (by omega) rfl
  have hv := axis_slot_mem p state e (q := v) hvx _ (by omega) (by rw [haxis]; simp only [Bool.toNat_true]; omega) rfl
  have hf := l.endpointStreet_connected p hl hM ha state e he .f (readDepth p e.level + 2) le_rfl B hB cap
  have hvc : v.1.val = p.x e.port := hvx
  have hfc : (endpointStreetCell l p hl ha e he .f (readDepth p e.level + 2) le_rfl).1.val =
      EndpointStreet.f.column p e := rfl
  have hto := hf.walk_horizontal v rfl (fun r hrow hlo hhi => by
    apply long_access_hole l p hl hM ha state e he haxis r (congrArg Fin.val hrow)
    · simpa only [hvc, hfc] using hlo
    · simpa only [hvc, hfc] using hhi) hB
  exact hto.walk_vertical w rfl (fun r hx hlo hhi => axis_interval_hole l p state e he v w hv hw r hx hlo hhi) hB

private theorem center_connected_of_horizontal (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (state : SignalState)
    (e : Endpoint) (he : e ∈ l.endpoints) (hhorizontal : horizontalInput state e = true)
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) (cap : Option ℕ) :
    FrameConnection l p state B cap (pocketCell l p hl ha e he 0 (readDepth p e.level) (by omega)) := by
  let w := pocketCell l p hl ha e he 0 (readDepth p e.level) (by omega)
  let v := pocketCell l p hl ha e he 2 (readDepth p e.level) (by omega)
  let a := endpointStreetCell l p hl ha e he .r (readDepth p e.level - 1) le_rfl
  let d : Direction := if e.side = .upper then .south else .north
  have hwx := pocket_axis_column l p hl ha e he (readDepth p e.level) (by omega)
  have hv := horizontal_slot_mem p state e (q := v) 2 (by omega)
    (by rw [hhorizontal]; decide +kernel) rfl rfl
  have hvH := endpoint_signal_hole l p state e he ((finite_take_drop p _ 1 v).mpr (Or.inr hv))
  have hlevels := l.endpoints_level_bounds p hl hM he
  have hY := readDepth_ge p hlevels.1 hlevels.2
  have hHeight := readDepth_add_lt_H p e.level
  have hadj : Adjacent d a v := by
    apply (adjacent_iff_coordinates d _ _).mpr
    constructor
    · have hx : v.1.val = EndpointStreet.r.column p e := by rw [EndpointStreet.column_r]; rfl
      cases hs : e.side <;> simpa only [d, hs, reduceCtorEq, ite_true, ite_false, Direction.lane,
        a, endpointStreetCell] using hx
    · cases hs : e.side <;>
        simp only [d, hs, reduceCtorEq, ite_true, ite_false, Direction.position] <;>
        simp only [a, v, pocketCell, endpointStreetCell, onSide, hs, reduceCtorEq,
          ite_true, ite_false, show (coordinates p).H = p.H from rfl] <;> omega
  have hr := l.endpointStreet_connected p hl hM ha state e he .r (readDepth p e.level - 1) le_rfl B hB cap
  have hvconn := hr.walk_adjacent v hvH d hadj hB
  apply hvconn.walk_horizontal w rfl ?_ hB
  intro r hrow hlo hhi
  apply pocket_row_hole l p state e he v hv r (congrArg Fin.val hrow)
  · have hh : w.1.val = p.x e.port := hwx
    omega
  · have hh : w.1.val = p.x e.port := hwx
    omega

/-- A supplied ordinary endpoint pocket connects every one of its actual signal holes to the frame. -/
theorem endpointPocket_connected (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (state : SignalState)
    (e : Endpoint) (he : e ∈ l.endpoints)
    (hentry : (if e.side = .upper then state.axes.getD e.port false else !(state.axes.getD e.port false)) = true ∨
      (if e.inward then state.internal.getD e.internal false else !(state.internal.getD e.internal false)) = true)
    (q : Cell (p.W + 1) (p.H + 1))
    (hq : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (endpointSegments (coordinates p) state e))
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) (cap : Option ℕ) :
    FrameConnection l p state B cap q := by
  let w := pocketCell l p hl ha e he 0 (readDepth p e.level) (by omega)
  have hwx := pocket_axis_column l p hl ha e he (readDepth p e.level) (by omega)
  have hw := axis_slot_mem p state e (q := w) hwx _ le_rfl (by omega) rfl
  have hcenter : FrameConnection l p state B cap w := hentry.elim
    (fun h => center_connected_of_axis l p hl hM ha state e he h B hB cap)
    (fun h => center_connected_of_horizontal l p hl hM ha state e he h B hB cap)
  rcases (finite_take_drop p _ 1 q).mp hq with haxis | hhorizontal
  · have hm := (axis_mem p state e _).mp ((finite_point_mem p _ q).mp haxis)
    exact hcenter.walk_vertical q (Fin.ext (hm.1.trans hwx.symm))
      (fun r hx hlo hhi => axis_interval_hole l p state e he w q hw haxis r hx hlo hhi) hB
  · have hm := (endpoint_horizontal_mem p state e _).mp ((finite_point_mem p _ q).mp hhorizontal)
    apply hcenter.walk_horizontal q (Fin.ext hm.1) ?_ hB
    intro r hrow hlo hhi
    apply pocket_row_hole l p state e he q hhorizontal r (congrArg Fin.val hrow)
    · have hh : w.1.val = p.x e.port := hwx
      omega
    · have hh : w.1.val = p.x e.port := hwx
      omega

end PushPuzzle.PushS.PortLayout
