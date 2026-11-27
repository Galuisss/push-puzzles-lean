/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.Contacts
public import PushS.Source.Strip.OfConstraintGraph

/-!
# Original vertex ports in the actual strip sweep

Each original port has a distinct unit segment beside its vertex center. Slot zero approaches
from the left, slot one leaves upward, and slot two leaves to the right. The original incidence
scan recovers the original port and its weight at that same slot.

## Main definitions

* `PushPuzzle.NCL.Strip.Sweep.portNeighbor`: the actual grid neighbor assigned to an original vertex slot.

## Main results

* `PushPuzzle.NCL.Strip.Sweep.port_arcs`: actual unit-arc labels beside every original incidence.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep

open PushPuzzle.Orthogonal

open Cslib.Complexity Cslib.Complexity.NCL Cslib Cslib.Orthogonal

variable {V E : Type*} {A K : ℕ} (R : Environment V E A K)

/-- The grid neighbor of a source center in its original local slot. -/
@[expose] def portNeighbor (v : V) (s : Fin 3) : Point :=
  ((R.center v).1 + (s.val : ℤ) - 1, (R.center v).2 + if s = 1 then 1 else 0)

private def fanPair (e : E) (d : Bool) : Point × Point :=
  match d with
  | true =>
    (PushPuzzle.NCL.Strip.Tracks.elbow (R.vertices.address (R.endpoint e d)) (R.port e d), R.center (R.endpoint e d))
  | false =>
    (R.center (R.endpoint e d), PushPuzzle.NCL.Strip.Tracks.elbow (R.vertices.address (R.endpoint e d)) (R.port e d))

private theorem fanPair_mem (e : E) (d : Bool) :
    fanPair R e d ∈ (R.route e).consecutivePairs := by
  cases d <;> simp [fanPair, PushPuzzle.NCL.Strip.Environment.route, PushPuzzle.NCL.Strip.Environment.center, PushPuzzle.NCL.Strip.Tracks.route,
    List.consecutivePairs]

private theorem fan_horizontal (e : E) (d : Bool) (hs : R.port e d ≠ 1) :
    StraightThrough (R.unitRoute e) (portNeighbor R (R.endpoint e d) (R.port e d)) (1, 0) := by
  apply subdivide_horizontal (R.route_orthogonal e) (fanPair_mem R e d)
  all_goals cases d
  all_goals simp only [portNeighbor,
    PushPuzzle.NCL.Strip.Environment.center, PushPuzzle.NCL.Strip.Tracks.center, PushPuzzle.NCL.Strip.Tracks.elbow, PushPuzzle.NCL.Strip.Tracks.column, Layout.column,
    Fin.ext_iff, Fin.val_one] at hs ⊢
  all_goals omega

private theorem fan_vertical (e : E) (d : Bool) (hs : R.port e d = 1) :
    StraightThrough (R.unitRoute e) (portNeighbor R (R.endpoint e d) (R.port e d)) (0, 1) := by
  apply subdivide_vertical (R.route_orthogonal e) (fanPair_mem R e d)
  all_goals cases d
  all_goals simp only [portNeighbor,
    PushPuzzle.NCL.Strip.Environment.center, PushPuzzle.NCL.Strip.Tracks.center, PushPuzzle.NCL.Strip.Tracks.elbow, PushPuzzle.NCL.Strip.Tracks.column, Layout.column,
    hs, Fin.val_one, Int.natCast_one, ↓reduceIte]
  all_goals omega

/-- Every original incidence has its actual adjacent unit-arc label, on the correct sweep side. -/
theorem port_arcs (e : E) (d : Bool) :
    if R.port e d = 0 then
      ∃ a : Arc R, a.edge = e ∧
        a.lower R = portNeighbor R (R.endpoint e d) (R.port e d) ∧
        a.upper R = R.center (R.endpoint e d)
    else
      ∃ a : Arc R, a.edge = e ∧ a.lower R = R.center (R.endpoint e d) ∧
        a.upper R = portNeighbor R (R.endpoint e d) (R.port e d) := by
  by_cases hs : R.port e d = 1
  · have h := (vertical_arcs R e _ (fan_vertical R e d hs)).1
    have hzero : R.port e d ≠ 0 := by rw [hs]; decide
    rw [ite_eq_right hzero]
    simpa only [portNeighbor, PushPuzzle.NCL.Strip.Environment.center, PushPuzzle.NCL.Strip.Tracks.center, hs, Fin.val_one,
      Nat.cast_one, ↓reduceIte, add_sub_cancel_right, add_sub_cancel_left,
      Int.reduceAdd, Int.reduceSub] using h
  · have h := horizontal_arcs R e _ (fan_horizontal R e d hs)
    by_cases hz : R.port e d = 0
    · rw [ite_eq_left hz]
      simpa only [portNeighbor, PushPuzzle.NCL.Strip.Environment.center, PushPuzzle.NCL.Strip.Tracks.center, hz, Fin.val_zero,
        Nat.cast_zero, add_zero, Fin.zero_ne_one, ↓reduceIte, sub_add_cancel] using h.2
    · have ht : R.port e d = 2 := by apply Fin.ext; simp only [Fin.ext_iff] at hs hz ⊢; omega
      rw [ite_eq_right hz]
      obtain ⟨a, ha, hlo, hup⟩ := h.1
      refine ⟨a, ha, ?_, hup⟩
      rw [hlo]
      simp only [portNeighbor, PushPuzzle.NCL.Strip.Environment.center, PushPuzzle.NCL.Strip.Tracks.center, ht, Fin.val_two,
        Nat.cast_ofNat, show (2 : Fin 3) ≠ 1 by decide, ↓reduceIte, add_zero, Prod.ext_iff]
      constructor
      · omega
      · trivial

private theorem pair_touch_of_endpoints (a : Arc R) {p : Point}
    (ha : a.lower R = p ∨ a.upper R = p) : (a.pair R).1 = p ∨ (a.pair R).2 = p := by
  rcases a.pair_eq R with h | h
  · simpa only [h] using ha
  · simpa only [h] using ha.symm

/-- At an original endpoint, the original carrier has exactly one incident unit-arc label. -/
theorem endpoint_arc_unique (e : E) (d : Bool) {a b : Arc R}
    (ha : a.edge = e) (hb : b.edge = e)
    (hap : a.lower R = R.center (R.endpoint e d) ∨ a.upper R = R.center (R.endpoint e d))
    (hbp : b.lower R = R.center (R.endpoint e d) ∨ b.upper R = R.center (R.endpoint e d)) :
    a = b := by
  have hp : (R.unitRoute e).head? = some (R.center (R.endpoint e d)) ∨
      (R.unitRoute e).getLast? = some (R.center (R.endpoint e d)) := by
    cases d
    · left
      rw [PushPuzzle.NCL.Strip.Environment.unitRoute, subdivide_head]
      rfl
    · right
      rw [PushPuzzle.NCL.Strip.Environment.unitRoute, subdivide_last (R.route_orthogonal e)]
      rfl
  have hpa : a.pair R ∈ (R.unitRoute e).consecutivePairs := ha ▸ a.pair_mem R
  have hpb : b.pair R ∈ (R.unitRoute e).consecutivePairs := hb ▸ b.pair_mem R
  exact Arc.eq_of_pair_eq R (ha.trans hb.symm)
    (pair_eq_of_touch_endpoint (R.unitRoute_nodup e) hp hpa hpb
      (pair_touch_of_endpoints R a hap) (pair_touch_of_endpoints R b hbp))

private theorem port_arc_exists (e : E) (d : Bool) :
    ∃ a ∈ arcs R [e],
      a.lower R = R.center (R.endpoint e d) ∨ a.upper R = R.center (R.endpoint e d) := by
  have h := port_arcs R e d
  split at h
  · obtain ⟨a, ha, _, hup⟩ := h
    exact ⟨a, (mem_arcs R [e] a).mpr (by simp [ha]), Or.inr hup⟩
  · obtain ⟨a, ha, hlo, _⟩ := h
    exact ⟨a, (mem_arcs R [e] a).mpr (by simp [ha]), Or.inl hlo⟩

/-- Scan the actual unit-arc list for the unique arc beside an original incidence. -/
@[expose] def portArc (e : E) (d : Bool) : Arc R :=
  ((arcs R [e]).find? (fun a => decide
    (a.lower R = R.center (R.endpoint e d) ∨ a.upper R = R.center (R.endpoint e d)))).get (by
      obtain ⟨a, ha, hp⟩ := port_arc_exists R e d
      exact List.find?_isSome.mpr ⟨a, ha, by simpa only [decide_eq_true_eq] using hp⟩)

/-- The computed source port retains its original carrier and occupies its original local slot. -/
theorem portArc_spec (e : E) (d : Bool) :
    (portArc R e d).edge = e ∧
      if R.port e d = 0 then
        (portArc R e d).lower R = portNeighbor R (R.endpoint e d) (R.port e d) ∧
          (portArc R e d).upper R = R.center (R.endpoint e d)
      else
        (portArc R e d).lower R = R.center (R.endpoint e d) ∧
          (portArc R e d).upper R = portNeighbor R (R.endpoint e d) (R.port e d) := by
  have hf : ((arcs R [e]).find? (fun a => decide
      (a.lower R = R.center (R.endpoint e d) ∨ a.upper R = R.center (R.endpoint e d)))) =
      some (portArc R e d) := (Option.some_get _).symm
  have hm := List.mem_of_find?_eq_some hf
  have he : (portArc R e d).edge = e := by simpa only [mem_arcs, List.mem_singleton] using hm
  have hp : (portArc R e d).lower R = R.center (R.endpoint e d) ∨
      (portArc R e d).upper R = R.center (R.endpoint e d) :=
    of_decide_eq_true (List.find?_some (p := fun a : Arc R => decide
      (a.lower R = R.center (R.endpoint e d) ∨ a.upper R = R.center (R.endpoint e d))) hf)
  refine ⟨he, ?_⟩
  have h := port_arcs R e d
  by_cases hz : R.port e d = 0
  · rw [ite_eq_left hz] at h ⊢
    obtain ⟨a, ha, hlo, hup⟩ := h
    have heq := endpoint_arc_unique R e d he ha hp (Or.inr hup)
    exact heq.symm ▸ ⟨hlo, hup⟩
  · rw [ite_eq_right hz] at h ⊢
    obtain ⟨a, ha, hlo, hup⟩ := h
    have heq := endpoint_arc_unique R e d he ha hp (Or.inl hlo)
    exact heq.symm ▸ ⟨hlo, hup⟩

private theorem portNeighbor_ne (v : V) (s : Fin 3) : portNeighbor R v s ≠ R.center v := by
  intro h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  simp only [portNeighbor] at hx hy
  split_ifs at hy <;> simp only [Fin.ext_iff, Fin.val_one] at * <;> omega

private theorem portArc_touch (e : E) (d : Bool) :
    (portArc R e d).lower R = R.center (R.endpoint e d) ∨
      (portArc R e d).upper R = R.center (R.endpoint e d) := by
  have h := (portArc_spec R e d).2
  split at h
  · exact Or.inr h.2
  · exact Or.inl h.1

private theorem source_incidence {v : V} {a : Arc R}
    (ha : a.lower R = R.center v ∨ a.upper R = R.center v) :
    ∃ d, R.endpoint a.edge d = v ∧ portArc R a.edge d = a := by
  have ht := pair_touch_of_endpoints R a ha
  have hm : realPoint (R.center v) ∈ support (R.route a.edge) := by
    rcases ht with h | h
    · exact h ▸ (a.endpoints_mem R).1
    · exact h ▸ (a.endpoints_mem R).2
  have hv := (R.center_mem_support_iff a.edge v).mp hm
  have finish (d : Bool) (hd : R.endpoint a.edge d = v) : portArc R a.edge d = a := by
    apply endpoint_arc_unique R a.edge d (portArc_spec R _ _).1 rfl (portArc_touch R _ _)
    simpa only [hd] using ha
  rcases hv with hv | hv
  · exact ⟨false, hv.symm, finish false hv.symm⟩
  · exact ⟨true, hv.symm, finish true hv.symm⟩

/-- The actual incoming source ports are precisely the original slot-zero incidences. -/
private theorem source_incoming_iff (es : List E) (v : V) (a : Arc R) :
    a ∈ (slice R es (R.center v)).incoming ↔
      ∃ d, a.edge ∈ es ∧ R.endpoint a.edge d = v ∧ R.port a.edge d = 0 ∧
        portArc R a.edge d = a := by
  constructor
  · intro ha
    obtain ⟨he, hu⟩ := (mem_slice_incoming R es _ a).mp ha
    obtain ⟨d, hd, hpa⟩ := source_incidence R (Or.inr hu)
    refine ⟨d, he, hd, ?_, hpa⟩
    by_contra hz
    have hs := (portArc_spec R a.edge d).2
    rw [ite_eq_right hz] at hs
    have hn := hs.2.symm.trans ((congrArg (PushPuzzle.NCL.Strip.Sweep.Arc.upper R) hpa).trans hu)
    exact portNeighbor_ne R _ _ (by simpa only [hd] using hn)
  · rintro ⟨d, he, hd, hz, hpa⟩
    apply (mem_slice_incoming R es _ a).mpr
    refine ⟨he, ?_⟩
    have hs := (portArc_spec R a.edge d).2
    rw [ite_eq_left hz] at hs
    exact (congrArg (PushPuzzle.NCL.Strip.Sweep.Arc.upper R) hpa).symm.trans (by simpa only [hd] using hs.2)

/-- Rebasing the original port bit by its actual unit-arc reversal gives the sweep-side bit. -/
theorem portArc_dir (e : E) (d : Bool) :
    ((portArc R e d).reversed R ^^ d) = decide (R.port e d = 0) := by
  let a := portArc R e d
  have he : a.edge = e := (portArc_spec R e d).1
  have hmem : a.pair R ∈ (R.unitRoute e).consecutivePairs := he ▸ a.pair_mem R
  have htouch := pair_touch_of_endpoints R a (portArc_touch R e d)
  have hne : a.lower R ≠ a.upper R := by
    intro h
    have := a.level_lt R
    rw [h] at this
    exact (lt_self_iff_false _).mp this
  have hpne : (a.pair R).1 ≠ (a.pair R).2 := by
    intro h
    have hu := a.unit R
    simp only [length, h, sub_self, Int.natAbs_zero, Nat.zero_add] at hu
    contradiction
  have hs := (portArc_spec R e d).2
  cases d
  · have h₀ : (a.pair R).1 = R.center (R.endpoint e false) := by
      apply fst_eq_of_touch_head (R.unitRoute_nodup e) ?_ hmem htouch
      rw [PushPuzzle.NCL.Strip.Environment.unitRoute, subdivide_head]
      rfl
    by_cases hz : R.port e false = 0
    · rw [ite_eq_left hz] at hs
      have hr : (a.pair R).1 = a.upper R := h₀.trans hs.2.symm
      simp [a, PushPuzzle.NCL.Strip.Sweep.Arc.reversed, hr, hz]
    · rw [ite_eq_right hz] at hs
      have hr : (a.pair R).1 ≠ a.upper R :=
        fun h => hne (hs.1.trans (h₀.symm.trans h))
      simp [a, PushPuzzle.NCL.Strip.Sweep.Arc.reversed, hr, hz]
  · have h₁ : (a.pair R).2 = R.center (R.endpoint e true) := by
      apply snd_eq_of_touch_last (R.unitRoute_nodup e) ?_ hmem htouch
      rw [PushPuzzle.NCL.Strip.Environment.unitRoute, subdivide_last (R.route_orthogonal e)]
      rfl
    by_cases hz : R.port e true = 0
    · rw [ite_eq_left hz] at hs
      have hr : (a.pair R).1 ≠ a.upper R :=
        fun h => hpne (h.trans (hs.2.trans h₁.symm))
      simp [a, PushPuzzle.NCL.Strip.Sweep.Arc.reversed, hr, hz]
    · rw [ite_eq_right hz] at hs
      have hr : (a.pair R).1 = a.upper R := by
        rcases a.pair_eq R with h | h
        · have hh : a.upper R = a.lower R :=
            (congrArg Prod.snd h).symm.trans (h₁.trans hs.1.symm)
          exact False.elim (hne hh.symm)
        · exact congrArg Prod.fst h
      simp [a, PushPuzzle.NCL.Strip.Sweep.Arc.reversed, hr, hz]

/-- A declared original slot-zero incidence is the entire actual incoming source block. -/
theorem source_incoming_eq {es : List E} (hes : es.Nodup) {e : E} {d : Bool}
    (he : e ∈ es) (hs : R.port e d = 0) :
    (slice R es (R.center (R.endpoint e d))).incoming = [portArc R e d] := by
  have hspec := portArc_spec R e d
  rw [ite_eq_left hs] at hspec
  have hmem : portArc R e d ∈ (slice R es (R.center (R.endpoint e d))).incoming :=
    (mem_slice_incoming R es _ _).mpr ⟨hspec.1.symm ▸ he, hspec.2.2⟩
  have hu (a : Arc R) (ha : a ∈ (slice R es (R.center (R.endpoint e d))).incoming) :
      a = portArc R e d := by
    obtain ⟨d', _, hv, hs', hpa⟩ := (source_incoming_iff R es _ a).mp ha
    have hi : (a.edge, d') = (e, d) :=
      R.incidence_injective (Prod.ext hv (hs'.trans hs.symm))
    have heq : a.edge = e := congrArg Prod.fst hi
    have hdq : d' = d := congrArg Prod.snd hi
    rw [heq, hdq] at hpa
    exact hpa.symm
  have hn : (slice R es (R.center (R.endpoint e d))).incoming.Nodup :=
    (frontier_nodup R hes _).filter _
  apply List.perm_singleton.mp
  apply (List.perm_ext_iff_of_nodup hn (List.nodup_singleton _)).mpr
  intro a
  simp only [List.mem_singleton]
  exact ⟨hu a, fun h => h ▸ hmem⟩

/-- Original slots one and two exhaust the actual outgoing source block, in top/right order. -/
theorem source_outgoing_eq {es : List E} (hes : es.Nodup) {e f : E} {d d' : Bool}
    (he : e ∈ es) (hf : f ∈ es) (hv : R.endpoint e d = R.endpoint f d')
    (hs : R.port e d = 1) (ht : R.port f d' = 2) :
    (slice R es (R.center (R.endpoint e d))).outgoing = [portArc R e d, portArc R f d'] := by
  have hs₀ : R.port e d ≠ 0 := by rw [hs]; decide
  have ht₀ : R.port f d' ≠ 0 := by rw [ht]; decide
  have hse := portArc_spec R e d
  have hte := portArc_spec R f d'
  rw [ite_eq_right hs₀] at hse
  rw [ite_eq_right ht₀] at hte
  have hem : portArc R e d ∈ (slice R es (R.center (R.endpoint e d))).outgoing :=
    (mem_slice_outgoing R es _ _).mpr ⟨hse.1.symm ▸ he, hse.2.1⟩
  have hfm : portArc R f d' ∈ (slice R es (R.center (R.endpoint e d))).outgoing :=
    (mem_slice_outgoing R es _ _).mpr ⟨hte.1.symm ▸ hf, hte.2.1.trans (congrArg R.center hv.symm)⟩
  apply outgoing_eq_pair R hes hem hfm
  simp only [PushPuzzle.NCL.Strip.Sweep.Arc.position, hse.2.1, hse.2.2, hte.2.1, hte.2.2, portNeighbor, hs, ht,
    Fin.val_one, Fin.val_two, hv]
  split_ifs <;> omega

/-- The rebased actual port arc ends at the exact center of its original incidence. -/
theorem portArc_endpoint (e : E) (d : Bool) :
    (portArc R e d).endpoint R ((portArc R e d).reversed R ^^ d) =
      R.center (R.endpoint e d) := by
  rw [portArc_dir]
  have hs := (portArc_spec R e d).2
  by_cases hz : R.port e d = 0
  · rw [ite_eq_left hz] at hs
    simpa only [hz, decide_true, PushPuzzle.NCL.Strip.Sweep.Arc.endpoint, ite_true] using hs.2
  · rw [ite_eq_right hz] at hs
    simpa only [hz, decide_false, PushPuzzle.NCL.Strip.Sweep.Arc.endpoint, Bool.false_eq_true, ite_false] using hs.1

end PushPuzzle.NCL.Strip.Sweep
