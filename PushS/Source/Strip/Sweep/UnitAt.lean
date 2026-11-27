/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.JointPorts
public import PushS.Source.Strip.Sweep.Wires

/-!
# Actual unit-subdivision constraints at a grid site

Group the actual subdivided vertices by their computed physical grid sites. Original source
centers contain one original vertex; an ordinary carrier site contains one interior joint.

## Main definitions

* `PushPuzzle.NCL.Strip.Sweep.UnitLegalAt`: all actual unit-graph constraints at one actual grid site.

## Main results

* `PushPuzzle.NCL.Strip.Sweep.unitLegalAt_center`: a source center contains its original source constraint.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep

open Cslib.Complexity Cslib.Complexity.NCL Cslib Cslib.Orthogonal ConstraintGraph

variable {V E : Type*} {A K : ℕ} (R : Environment V E A K)

/-- All vertices of the actual unit graph whose computed physical grid site is `p` are legal. -/
@[expose] def UnitLegalAt (G : ConstraintGraph V E) (w : E → ℕ) (p : Point)
    (s : Arc R → Bool) : Prop :=
  ∀ v, unitPoint R v = p → (unitGraph R G w v).Sat s

/-- Every source center carries exactly its original vertex constraint. -/
theorem unitLegalAt_center (G : ConstraintGraph V E) (w : E → ℕ) (v : V)
    (s : Arc R → Bool) :
    UnitLegalAt R G w (R.center v) s ↔ (unitGraph R G w (.inl v)).Sat s := by
  constructor
  · intro h
    exact h (.inl v) rfl
  · intro h u hu
    cases u with
    | inl u =>
      have he := R.center_injective hu
      subst u
      exact h
    | inr j => exact False.elim (joint_not_center R j v hu)

/-- An ordinary visited site has exactly the single actual joint constraint of its carrier. -/
theorem unitLegalAt_wire [DecidableEq E] (G : ConstraintGraph V E) (w : E → ℕ)
    {es : List E} (hes : es.Nodup) (hall : ∀ e, e ∈ es) {p : Point} {e : E}
    (hp : p ∈ R.unitRoute e) (hc : ∀ v, p ≠ R.center v)
    (hx : ∀ c ∈ R.events es, p ≠ c.site R) (s : Arc R → Bool) :
    UnitLegalAt R G w p s ↔
      (Vertex.mk ((localPorts R es p w).filter
        (fun q => decide (q.1.edge.edge = e))) (w e)).Sat s := by
  obtain ⟨j, hj, _⟩ := existsUnique_joint R e hp hc
  constructor
  · intro h
    have hs := (joint_sat_iff R G w hes ⟨e, j⟩ (hall e) s).mp (h _ hj)
    simpa only [hj] using hs
  · intro h v hv
    cases v with
    | inl v => exact False.elim (hc v hv.symm)
    | inr j =>
      have he := carrier_unique_at R (hall e) (hall j.1) hp
        (by simpa only [hv] using unitPoint_joint_mem R j) hc hx
      apply (joint_sat_iff R G w hes j (hall j.1) s).mpr
      simpa only [hv, he] using h

/-- At an ordinary carrier site all actual local weighted ports belong to that carrier. -/
theorem wire_localPorts_filter [DecidableEq E] (w : E → ℕ) {es : List E} {p : Point} {e : E}
    (he : e ∈ es) (hp : p ∈ R.unitRoute e) (hc : ∀ v, p ≠ R.center v)
    (hx : ∀ c ∈ R.events es, p ≠ c.site R) :
    (localPorts R es p w).filter (fun q => decide (q.1.edge.edge = e)) = localPorts R es p w := by
  apply List.filter_eq_self.mpr
  intro q hq
  obtain ⟨hf, _, hpt⟩ := (mem_localPorts R es p w q).mp hq
  have hqp : p ∈ R.unitRoute q.1.edge.edge :=
    hpt ▸ q.1.edge.endpoint_mem_unitRoute R q.1.dir
  simpa only [decide_eq_true_eq] using carrier_unique_at R he hf hp hqp hc hx

/-- An actual crossing contains precisely the two participating original carrier constraints. -/
theorem unitLegalAt_crossing [DecidableEq E] (G : ConstraintGraph V E) (w : E → ℕ)
    {es : List E} (hes : es.Nodup) (hall : ∀ e, e ∈ es) {c : Event E}
    (hc : c ∈ R.events es) (s : Arc R → Bool) :
    UnitLegalAt R G w (c.site R) s ↔
      (Vertex.mk ((localPorts R es (c.site R) w).filter
        (fun q => decide (q.1.edge.edge = c.bridge))) (w c.bridge)).Sat s ∧
      (Vertex.mk ((localPorts R es (c.site R) w).filter
        (fun q => decide (q.1.edge.edge = c.stem))) (w c.stem)).Sat s := by
  have hc' := ((R.mem_events es c).mp hc).2.2
  have hcent : ∀ v, c.site R ≠ R.center v := by
    intro v hv
    exact R.crossing_not_center hc' v (congrArg realPoint hv)
  obtain ⟨jb, hjb, _⟩ := existsUnique_joint R c.bridge
    ((R.site_mem_unitRoute hc' c.bridge).mpr (Or.inl rfl)) hcent
  obtain ⟨jt, hjt, _⟩ := existsUnique_joint R c.stem
    ((R.site_mem_unitRoute hc' c.stem).mpr (Or.inr rfl)) hcent
  constructor
  · intro h
    constructor
    · have hs := (joint_sat_iff R G w hes ⟨c.bridge, jb⟩ (hall _) s).mp (h _ hjb)
      simpa only [hjb] using hs
    · have hs := (joint_sat_iff R G w hes ⟨c.stem, jt⟩ (hall _) s).mp (h _ hjt)
      simpa only [hjt] using hs
  · rintro ⟨hb, ht⟩ v hv
    cases v with
    | inl v => exact False.elim (hcent v hv.symm)
    | inr j =>
      have he := (R.site_mem_unitRoute hc' j.1).mp
        (by simpa only [hv] using unitPoint_joint_mem R j)
      apply (joint_sat_iff R G w hes j (hall _) s).mpr
      rcases he with he | he
      · simpa only [hv, he] using hb
      · simpa only [hv, he] using ht

end PushPuzzle.NCL.Strip.Sweep
