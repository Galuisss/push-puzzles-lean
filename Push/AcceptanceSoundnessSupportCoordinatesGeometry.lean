/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupportCoordinatesGuards

/-! Two actual sparse supports meet in the original streets and isolated permanently occupied points. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

/-- The actual original, guard and sample columns contain no consecutive coordinates. -/
theorem columns_separated (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid) :
    Support.Separated ((supportCoordinates l p).columns ∪ (supportCoordinates l p).guards ∪
      (supportCoordinates l p).samples) := by
  let c := supportCoordinates l p
  have hfar (g : Fin (p.W + 1)) (hg : g ∈ c.guards) (x : Fin (p.W + 1))
      (hx : x ∈ c.columns ∪ c.samples) : 1 < Nat.dist g.val x.val := by
    rcases hx with hx | hx
    · exact lt_trans (by decide : 1 < 14) (l.acceptanceGuard_street_far p hg hx)
    · exact lt_trans (by decide : 1 < 4) (l.acceptanceGuard_sample_far p hl hg hx)
  have hseparated : Support.Separated ((c.columns ∪ c.samples) ∪ c.guards) := by
    intro a b ha hb he
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact columns_samples_separated l p ha hb he
    · have hh := hfar b hb a ha
      simp only [Nat.dist] at hh
      omega
    · have hh := hfar a ha b hb
      simp only [Nat.dist] at hh
      omega
    · exact l.acceptanceGuards_separated p ha hb he
  have heq : c.columns ∪ c.guards ∪ c.samples = (c.columns ∪ c.samples) ∪ c.guards := by
    ext x
    simp only [Set.mem_union]
    tauto
  change Support.Separated (c.columns ∪ c.guards ∪ c.samples)
  rw [heq]
  exact hseparated

/-- The actual first sparse support satisfies reverse complete-lane support. -/
private theorem first_axisClosed (l : PortLayout) (p : Scales.Parameters) :
    Support.AxisClosed (supportCoordinates l p).first :=
  Support.streets_axisClosed (l.streetColumnSet_separated p) (rows_separated l p)

/-- The actual second sparse support satisfies reverse complete-lane support. -/
private theorem second_axisClosed (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid) :
    Support.AxisClosed (supportCoordinates l p).second :=
  Support.streets_axisClosed (columns_separated l p hl) (l.workingRowSet_separated p)

/-- Their actual physical intersection retains reverse complete-lane support. -/
private theorem intersection_axisClosed (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) :
    Support.AxisClosed ((supportCoordinates l p).first ∩ (supportCoordinates l p).second) :=
  axisClosed_inter (first_axisClosed l p) (second_axisClosed l p hl)

/-- Each extra intersection point has no physical neighbor in the actual two-support intersection. -/
private theorem extra_intersection_isolated (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ (supportCoordinates l p).first ∩ (supportCoordinates l p).second)
    (ho : q ∉ (supportCoordinates l p).original) :
    Isolated ((supportCoordinates l p).first ∩ (supportCoordinates l p).second) q :=
  (supportCoordinates l p).crossing_isolated (rows_separated l p) (columns_separated l p hl) hq ho

/-- Every point outside the original streets starts occupied in the actual filled canonical source. -/
private theorem canonical_filled_off_original_box (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : List Bool)
    {q : Cell (p.W + 1) (p.H + 1)} (ho : q ∉ (supportCoordinates l p).original) :
    q ∈ (Blocked.fill (l.canonicalInstance p hl hM ha initial target).initial (newCentralMarkers l p)).boxes := by
  by_contra hq
  exact ho (canonical_filled_original_supported l p hl hM ha initial target q hq)

/-- Actual play from the filled canonical source and terminal two-support membership yields original-street support. -/
theorem canonical_filled_original_of_intersection (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : List Bool)
    {B : Board (p.W + 1) (p.H + 1)} {cap : Option ℕ} {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable B cap
      (Blocked.fill (l.canonicalInstance p hl hM ha initial target).initial (newCentralMarkers l p)) t)
    (ht : Support.Supported ((supportCoordinates l p).first ∩ (supportCoordinates l p).second) t) :
    Support.Supported (supportCoordinates l p).original t := by
  intro q hq
  by_contra ho
  have hpoint := ht q hq
  have hi := extra_intersection_isolated l p hl hpoint ho
  have hbox := canonical_filled_off_original_box l p hl hM ha initial target ho
  exact hq ((isolated_box_reachable (intersection_axisClosed l p hl) hi hr ht).mpr hbox)

end PushPuzzle.Push.AcceptanceSoundness
