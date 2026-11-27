/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortOrdinaryFailureStep
import all PushS.PortAxisGroups
import all PushS.PortGateAxisTrainReadout
import all PushS.PortGateIndexing
import all PushS.PortWireTrains
import all PushS.PortCoreCrossing
import all PushS.PortSegments

/-! Losing an ordinary endpoint supply forces the actual player to the opposite end of its train. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS RowLabels

private theorem entry_column {p : Scales.Parameters} {e : Endpoint} {d : Direction}
    {q r : Cell (p.W + 1) (p.H + 1)} (ha : Adjacent d q r) (hr : r ∈ ordinaryPocket p e) :
    (p.x e.port : ℤ) - 2 ≤ q.1.val ∧ (q.1.val : ℤ) ≤ p.x e.port + 2 := by
  have hx := readLength_add_lt_x p e.port 0
  simp only [ordinaryPocket, Finset.mem_filter, Finset.mem_univ, true_and] at hr
  cases d <;> cases hi : e.inward <;>
    simp only [hi, Bool.false_eq_true, ite_false, ite_true, Adjacent] at ha hr <;> omega

private theorem entry_row {p : Scales.Parameters} {e : Endpoint} {d : Direction}
    {q r : Cell (p.W + 1) (p.H + 1)} (ha : Adjacent d q r) (hr : r ∈ ordinaryPocket p e)
    (hY : 3 ≤ readDepth p e.level) :
    if e.side = .upper then readDepth p e.level - 1 ≤ q.2.val ∧ q.2.val ≤ readDepth p e.level + 2
    else p.H - (readDepth p e.level + 2) ≤ q.2.val ∧ q.2.val ≤ p.H - (readDepth p e.level - 1) := by
  have hH := readDepth_add_lt_H p e.level
  have hq := q.2.isLt
  have hrr := r.2.isLt
  simp only [ordinaryPocket, Finset.mem_filter, Finset.mem_univ, true_and] at hr
  cases d <;> cases hs : e.side <;>
    simp only [hs, reduceCtorEq, ite_false, ite_true, Adjacent] at ha hr ⊢ <;> omega

private theorem ordinary_upper_loss {p : Scales.Parameters} {upper lower : Endpoint}
    {u v : State (p.W + 1) (p.H + 1)} {before after : ThreeBlocks}
    (motion : OrdinaryAxisMotion p upper lower u v before after) (hs : upper.side = .upper)
    (hY : 3 ≤ readDepth p upper.level)
    (hbefore : (ordinaryAxisPlacement p upper before).parameter ≤ 1)
    (hafter : 2 ≤ (ordinaryAxisPlacement p upper after).parameter)
    {d : Direction} (hadj : Adjacent d u.player v.player) : v.player ∉ ordinaryPocket p upper := by
  intro hin
  have hy := entry_row hadj hin hY
  simp only [hs, ite_true] at hy
  change ((readDepth p upper.level : ℤ) + 4 - before.middle).toNat ≤ 1 at hbefore
  change 2 ≤ ((readDepth p upper.level : ℤ) + 4 - after.middle).toNat at hafter
  have hb := motion.middle_bounds
  have hmoved : after.middle < before.middle := by omega
  have hp := motion.middle_backward hmoved
  have hlen := motion.before_shape.middle_length
  have hDu := readDepth_add_lt_D p upper.level
  have hDl := readDepth_add_lt_D p lower.level
  have hH : p.H = 2 * p.D := rfl
  omega

private theorem ordinary_lower_loss {p : Scales.Parameters} {upper lower : Endpoint}
    {u v : State (p.W + 1) (p.H + 1)} {before after : ThreeBlocks}
    (motion : OrdinaryAxisMotion p upper lower u v before after) (hs : lower.side = .lower)
    (hY : 3 ≤ readDepth p lower.level)
    (hbefore : (ordinaryAxisPlacement p upper before).lowerParameter ≤ 1)
    (hafter : 2 ≤ (ordinaryAxisPlacement p upper after).lowerParameter)
    {d : Direction} (hadj : Adjacent d u.player v.player) : v.player ∉ ordinaryPocket p lower := by
  intro hin
  have hy := entry_row hadj hin hY
  simp only [hs, reduceCtorEq, ite_false] at hy
  change 3 - ((readDepth p upper.level : ℤ) + 4 - before.middle).toNat ≤ 1 at hbefore
  change 2 ≤ 3 - ((readDepth p upper.level : ℤ) + 4 - after.middle).toNat at hafter
  have hb := motion.middle_bounds
  have hmoved : before.middle < after.middle := by omega
  have hp := motion.middle_forward hmoved
  have hDu := readDepth_add_lt_D p upper.level
  have hDl := readDepth_add_lt_D p lower.level
  have hH : p.H = 2 * p.D := rfl
  omega

private theorem gate_upper_loss {p : Scales.Parameters} {g : Placement} {upper : Endpoint}
    {u v : State (p.W + 1) (p.H + 1)} {before after : TwoBlocks}
    (motion : GateAxisTrainMotion p g upper u v before after) (hs : upper.side = .upper)
    (hY : 3 ≤ readDepth p upper.level)
    (hbefore : (gateAxisPlacement p upper before).parameter ≤ 1)
    (hafter : 2 ≤ (gateAxisPlacement p upper after).parameter)
    {d : Direction} (hadj : Adjacent d u.player v.player) : v.player ∉ ordinaryPocket p upper := by
  intro hin
  have hy := entry_row hadj hin hY
  simp only [hs, ite_true] at hy
  change ((readDepth p upper.level : ℤ) + 4 - before.last).toNat ≤ 1 at hbefore
  change 2 ≤ ((readDepth p upper.level : ℤ) + 4 - after.last).toNat at hafter
  have hb := motion.last_bounds
  have hmoved : after.last < before.last := by omega
  have hp := motion.last_backward hmoved
  have hlen := motion.before_shape.last_length
  have hDu := readDepth_add_lt_D p upper.level
  have hDl := readDepth_add_lt_D p 1
  have hH : p.H = 2 * p.D := rfl
  omega

private theorem wire_left_loss {p : Scales.Parameters} {g : Placement} {B : Board (p.W + 1) (p.H + 1)}
    {u v : State (p.W + 1) (p.H + 1)} (motion : WireTrainStep p g B u v)
    (hspan : p.x g.left + 40 < p.x g.right)
    (hbefore : 2 ≤ (motion.first - (p.x g.left : ℤ) - 1).toNat)
    (hafter : (motion.next - (p.x g.left : ℤ) - 1).toNat ≤ 1)
    {d : Direction} (hadj : Adjacent d u.player v.player) :
    v.player ∉ ordinaryPocket p ⟨g.side, g.left, true, g.level, g.internal⟩ := by
  intro hin
  have hx := entry_column hadj hin
  have hb := motion.start_bounds
  have hmoved : motion.next < motion.first := by omega
  have hp := motion.force_decrease hmoved
  simp only [wireTrainLength] at hp
  change (p.x g.left : ℤ) - 2 ≤ u.player.1.val ∧ (u.player.1.val : ℤ) ≤ p.x g.left + 2 at hx
  omega

private theorem wire_right_loss {p : Scales.Parameters} {g : Placement} {B : Board (p.W + 1) (p.H + 1)}
    {u v : State (p.W + 1) (p.H + 1)} (motion : WireTrainStep p g B u v)
    (hspan : p.x g.left + 40 < p.x g.right)
    (hbefore : 2 ≤ ((p.x g.right : ℤ) - motion.first - wireTrainLength p g).toNat)
    (hafter : ((p.x g.right : ℤ) - motion.next - wireTrainLength p g).toNat ≤ 1)
    {d : Direction} (hadj : Adjacent d u.player v.player) :
    v.player ∉ ordinaryPocket p ⟨g.side, g.right, false, g.level, g.internal⟩ := by
  intro hin
  have hx := entry_column hadj hin
  have hb := motion.start_bounds
  have hmoved : motion.first < motion.next := by omega
  have hp := motion.force_increase hmoved
  simp only [wireTrainLength] at hbefore hafter
  change (p.x g.right : ℤ) - 2 ≤ u.player.1.val ∧ (u.player.1.val : ℤ) ≤ p.x g.right + 2 at hx
  omega

private theorem gate_left_loss {p : Scales.Parameters} {g : Placement} {kind : Shuttle.Kind}
    {u v : State (p.W + 1) (p.H + 1)} {before after : ThreeBlocks}
    (motion : GateTrainMotion p g kind u v before after)
    (hbefore : 2 ≤ (gateTrainPlacement p g before).left) (hafter : (gateTrainPlacement p g after).left ≤ 1)
    {d : Direction} (hadj : Adjacent d u.player v.player) :
    v.player ∉ ordinaryPocket p ⟨g.side, g.left, true, g.level, g.internal⟩ := by
  intro hin
  have hx := entry_column hadj hin
  have hsource := motion.before_shape.placement_coordinates
  have htarget := motion.after_shape.placement_coordinates
  have hb := motion.first_bounds
  have hmoved : after.first < before.first := by omega
  have hp := motion.first_backward hmoved
  have hlen := motion.before_shape.first_length
  have hD := p.outer_distance
  have hk : kind.kappa.toNat ≤ 4 := by cases kind <;> decide +kernel
  change (p.x g.left : ℤ) - 2 ≤ u.player.1.val ∧ (u.player.1.val : ℤ) ≤ p.x g.left + 2 at hx
  omega

private theorem gate_right_loss {p : Scales.Parameters} {g : Placement} {kind : Shuttle.Kind}
    {u v : State (p.W + 1) (p.H + 1)} {before after : ThreeBlocks}
    (motion : GateTrainMotion p g kind u v before after)
    (hbefore : 2 ≤ (gateTrainPlacement p g before).right) (hafter : (gateTrainPlacement p g after).right ≤ 1)
    {d : Direction} (hadj : Adjacent d u.player v.player) :
    v.player ∉ ordinaryPocket p ⟨g.side, g.right, false, g.level, g.internal + 2⟩ := by
  intro hin
  have hx := entry_column hadj hin
  have hsource := motion.before_shape.placement_coordinates
  have htarget := motion.after_shape.placement_coordinates
  have hbeforeLen := motion.before_shape.last_length
  have hafterLen := motion.after_shape.last_length
  have hb := motion.last_bounds
  have hmoved : before.last < after.last := by omega
  have hp := motion.last_forward hmoved
  have hD := p.outer_distance
  change (p.x g.right : ℤ) - 2 ≤ u.player.1.val ∧ (u.player.1.val : ℤ) ≤ p.x g.right + 2 at hx
  omega

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)
  (e : Endpoint) (he : e ∈ l.endpoints)

local notation "I" => l.physicalInstance p hl hM ha initial target

include he

/-- A real loss of an ordinary endpoint's axis supply leaves its target player outside that endpoint's pocket. -/
theorem physicalInstance_endpoint_axis_loss_outside {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals)
    {beforeParameter beforeShift afterParameter afterShift : ℕ}
    (hsource : EndpointAxisReadout p e u beforeParameter beforeShift)
    (htarget : EndpointAxisReadout p e v afterParameter afterShift)
    (hbefore : beforeParameter ≤ 1) (hafter : 2 ≤ afterParameter) : v.player ∉ ordinaryPocket p e := by
  have hY := readDepth_ge p (l.endpoints_level_bounds p hl hM he).1 (l.endpoints_level_bounds p hl hM he).2
  have hadj := players_adjacent hm.choose_spec
  cases hs : e.side with
  | lower =>
    obtain ⟨upper, hu, hsuSide, hp⟩ := l.endpoints_upper_exists hl (l.endpoints_port_lt hl he)
    obtain ⟨before, after, motion⟩ := l.physicalInstance_ordinaryAxis_train_motion p hl hM ha initial target
      hu he hsuSide hs hp.symm hsu hm hvt ht
    have hsrc := l.endpoint_axis_parameter_unique p hl hM ha he hsource (motion.before_readout.lower_endpoint hs hp.symm)
    have htgt := l.endpoint_axis_parameter_unique p hl hM ha he htarget (motion.after_readout.lower_endpoint hs hp.symm)
    exact ordinary_lower_loss motion hs (by omega) (by rwa [← hsrc]) (by rwa [← htgt]) hadj
  | upper =>
    obtain ⟨groups⟩ := l.axisGroups_nonempty hl (l.endpoints_port_lt hl he)
    have ordinary (hk : e.port = groups.lower.left ∨ e.port = groups.lower.right) : v.player ∉ ordinaryPocket p e := by
      obtain ⟨lower, hlow, hls, hlp, _⟩ := placement_outer_endpoint l groups.lower_mem hk
      obtain ⟨before, after, motion⟩ := l.physicalInstance_ordinaryAxis_train_motion p hl hM ha initial target
        he hlow hs (hls.trans groups.lower_side) hlp hsu hm hvt ht
      have hsrc := l.endpoint_axis_parameter_unique p hl hM ha he hsource (motion.before_readout.upper_endpoint hs)
      have htgt := l.endpoint_axis_parameter_unique p hl hM ha he htarget (motion.after_readout.upper_endpoint hs)
      exact ordinary_upper_loss motion hs (by omega) (by rwa [← hsrc]) (by rwa [← htgt]) hadj
    rcases groups.lower_port with hleft | hright | ⟨hgate, hmid⟩
    · exact ordinary (Or.inl hleft)
    · exact ordinary (Or.inr hright)
    · cases hk : groups.lower.gate with
      | none => simp only [hk, Option.isSome_none, Bool.false_eq_true] at hgate
      | some kind =>
        obtain ⟨before, after, motion⟩ := l.physicalInstance_gateAxis_train_motion p hl hM ha initial target
          groups.lower_mem hk he hs hmid hsu hm hvt ht
        have hsrc := l.endpoint_axis_parameter_unique p hl hM ha he hsource
          ((motion.before_shape.readout motion.before_positive).upper_endpoint hs hmid)
        have htgt := l.endpoint_axis_parameter_unique p hl hM ha he htarget
          ((motion.after_shape.readout motion.after_positive).upper_endpoint hs hmid)
        exact gate_upper_loss motion hs (by omega) (by rwa [← hsrc]) (by rwa [← htgt]) hadj

/-- A real loss of an ordinary endpoint's horizontal supply leaves its target player outside its pocket. -/
theorem physicalInstance_endpoint_horizontal_loss_outside {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals) {beforeHorizontal afterHorizontal : ℕ}
    (hsource : EndpointHorizontalReadout p e u beforeHorizontal)
    (htarget : EndpointHorizontalReadout p e v afterHorizontal)
    (hbefore : 2 ≤ beforeHorizontal) (hafter : afterHorizontal ≤ 1) : v.player ∉ ordinaryPocket p e := by
  have hadj := players_adjacent hm.choose_spec
  obtain ⟨g, hg, hend⟩ := List.mem_flatMap.mp he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hend
  cases hk : g.gate with
  | none =>
    obtain ⟨motion⟩ := l.physicalInstance_wire_train_step p hl hM ha initial target hg hk hsu hm hvt ht
    have hspan := wire_train_margin l p hl hg hk
    have hs := motion.source_shape.readout motion.marked.length_pos
    have hv := motion.target_shape.readout motion.marked.length_pos
    simp only [hk, Option.isSome_none, Bool.false_eq_true, ite_false, Nat.add_zero] at hend
    rcases hend with rfl | rfl
    · have hsrc := l.endpoint_horizontal_failed_iff p hl ha he hsource (hs.left_endpoint hl hg hk)
      have htgt := l.endpoint_horizontal_failed_iff p hl ha he htarget (hv.left_endpoint hl hg hk)
      exact wire_left_loss motion hspan (by omega) (htgt.mp hafter) hadj
    · have hsrc := l.endpoint_horizontal_failed_iff p hl ha he hsource (hs.right_endpoint hl hg hk)
      have htgt := l.endpoint_horizontal_failed_iff p hl ha he htarget (hv.right_endpoint hl hg hk)
      exact wire_right_loss motion hspan (by omega) (htgt.mp hafter) hadj
  | some kind =>
    obtain ⟨before, after, motion⟩ := l.physicalInstance_gate_train_motion p hl hM ha initial target hg hk hsu hm hvt ht
    simp only [hk, Option.isSome_some, ite_true] at hend
    rcases hend with rfl | rfl
    · have hsrc := l.endpoint_horizontal_failed_iff p hl ha he hsource (motion.before_shape.left_endpoint hl hg hk)
      have htgt := l.endpoint_horizontal_failed_iff p hl ha he htarget (motion.after_shape.left_endpoint hl hg hk)
      exact gate_left_loss motion (by omega) (htgt.mp hafter) hadj
    · have hsrc := l.endpoint_horizontal_failed_iff p hl ha he hsource (motion.before_shape.right_endpoint hl hg hk)
      have htgt := l.endpoint_horizontal_failed_iff p hl ha he htarget (motion.after_shape.right_endpoint hl hg hk)
      exact gate_right_loss motion (by omega) (htgt.mp hafter) hadj

/-- The first occurrence of a real ordinary W fault has its actual target player outside the three-cell pocket. -/
theorem physicalInstance_ordinary_failure_onset {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals)
    (fault : OrdinaryFaultReadout p e v) (hsource : ¬Nonempty (OrdinaryFaultReadout p e u)) :
    v.player ∉ ordinaryPocket p e := by
  have hut := (Relation.ReflTransGen.single hm).trans hvt
  obtain ⟨parameter, shift, haxis⟩ := l.physicalInstance_endpoint_axis_readout p hl hM ha initial target e he hsu hut ht
  by_cases hsupplied : parameter ≤ 1
  · exact l.physicalInstance_endpoint_axis_loss_outside p hl hM ha initial target e he hsu hm hvt ht
      haxis fault.axis_word hsupplied fault.axis_failed
  · obtain ⟨horizontal, hread⟩ := l.physicalInstance_endpoint_horizontal_readout p hl hM ha initial target e he hsu hut ht
    have hhorizontal : 2 ≤ horizontal := by
      by_contra hnot
      exact hsource ⟨⟨parameter, shift, horizontal, haxis, by omega, hread, by omega⟩⟩
    exact l.physicalInstance_endpoint_horizontal_loss_outside p hl hM ha initial target e he hsu hm hvt ht
      hread fault.horizontal_word hhorizontal fault.horizontal_failed

end Solution

end PushPuzzle.PushS.PortLayout
