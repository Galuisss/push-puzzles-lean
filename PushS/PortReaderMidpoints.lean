/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortReaderExits
public import PushS.EndpointWalking
import all PushS.PortStreetEnumeration
import all PushS.PortLayoutCoordinates
import all PushS.PortWalkBudget
import all PushS.PortSegments

/-! Actual ordinary-reader midpoints are farther than the residual hole budget from every exit. -/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction

private theorem midpoint_gap {x L P K z : ℕ} (d : Bool) (hx : L + 64 < x)
    (hK : K < L / 2 - P - 12)
    (hz : (x - (P + 12) ≤ z ∧ z ≤ x + (P + 12)) ∨ z ≤ x - L ∨ x + L ≤ z) :
    K < Nat.dist z (((if d then x - L else x + L) + x) / 2) := by
  rcases hz with hz | hz | hz <;> cases d <;>
    simp only [Bool.false_eq_true, ite_false, ite_true, Nat.dist_eq_max_sub_min] <;> omega

private theorem midpoint_close_span (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) {e : Endpoint}
    (he : e ∈ l.endpoints) {z : ℕ}
    (hz : Nat.dist z ((EndpointStreet.f.column p e + p.x e.port) / 2) ≤ p.K e.level) :
    p.x e.port - columnRadius p ≤ z ∧ z ≤ p.x e.port + columnRadius p := by
  obtain ⟨hj, hm⟩ := l.endpoints_level_bounds p hl hM he
  have hK := p.reader_distance e.level hj
  have hx := readLength_add_lt_x p e.port e.level
  have hL := L_le p hm
  rw [readLength_eq p hj hm] at hx
  rw [EndpointStreet.column_f, readLength_eq p hj hm] at hz
  cases hd : e.inward <;>
    simp only [hd, Bool.false_eq_true, ite_false, ite_true, Nat.dist_eq_max_sub_min] at hz <;>
    dsimp only [columnRadius] <;> omega

private theorem midpoint_near_axis_far (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) {e : Endpoint}
    (he : e ∈ l.endpoints) {z : ℕ} (hz : Nat.dist z (p.x e.port) ≤ 12) :
    p.K e.level < Nat.dist z ((EndpointStreet.f.column p e + p.x e.port) / 2) := by
  obtain ⟨hj, hm⟩ := l.endpoints_level_bounds p hl hM he
  have hx := readLength_add_lt_x p e.port e.level
  rw [readLength_eq p hj hm] at hx
  rw [EndpointStreet.column_f, readLength_eq p hj hm]
  apply midpoint_gap e.inward hx (p.reader_distance e.level hj)
  apply Or.inl
  simp only [Nat.dist_eq_max_sub_min] at hz
  omega

private theorem midpoint_other_f_far (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) {e f : Endpoint}
    (he : e ∈ l.endpoints) (hf : f ∈ l.endpoints) (hport : f.port = e.port) :
    p.K e.level < Nat.dist (EndpointStreet.f.column p f)
      ((EndpointStreet.f.column p e + p.x e.port) / 2) := by
  obtain ⟨hj, hm⟩ := l.endpoints_level_bounds p hl hM he
  obtain ⟨hfj, hfm⟩ := l.endpoints_level_bounds p hl hM hf
  have hx := readLength_add_lt_x p e.port e.level
  rw [readLength_eq p hj hm] at hx
  simp only [EndpointStreet.column_f, hport, readLength_eq p hj hm]
  apply midpoint_gap e.inward hx (p.reader_distance e.level hj)
  by_cases hsmall : f.level < e.level
  · have hprev := readLength_le_level p (show f.level ≤ e.level - 1 by omega)
    apply Or.inl
    cases hd : f.inward <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega
  · have hlong : p.L e.level ≤ readLength p f.level := by
      rw [readLength_eq p hfj hfm]
      exact L_le p (by omega)
    cases hd : f.inward <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega

private theorem street_column_midpoint_far (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    {e : Endpoint} (he : e ∈ l.endpoints) {z : ℕ}
    (hz : z ∈ streetColumns l (coordinates p)) :
    p.K e.level < Nat.dist z ((EndpointStreet.f.column p e + p.x e.port) / 2) := by
  by_contra! hclose
  have hspan := midpoint_close_span l p hl hM he hclose
  have hinside := column_inside p (lt_of_lt_of_le (l.endpoints_port_lt hl he) ha) hspan
  simp only [streetColumns, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    or_assoc] at hz
  rcases hz with hz | hz | hz | hz
  · omega
  · change z = p.W at hz
    omega
  · obtain ⟨i, _, hzi⟩ := List.mem_map.mp hz
    have hi : p.x i - columnRadius p ≤ z ∧ z ≤ p.x i + columnRadius p := by
      change p.x i = z at hzi
      rw [← hzi]
      omega
    have hport := column_owner p hi hspan
    have hnear : Nat.dist z (p.x e.port) ≤ 12 := by
      change p.x i = z at hzi
      rw [← hzi, hport, Nat.dist_self]
      omega
    have := midpoint_near_axis_far l p hl hM he hnear
    omega
  · rcases List.mem_append.mp hz with hz | hz
    · obtain ⟨f, hf, hz⟩ := List.mem_flatMap.mp hz
      have hfcol : z ∈ endpointColumns p f := by
        simp only [endpointColumns, List.mem_cons, List.not_mem_nil, or_false]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        exact hz.elim Or.inl (fun h => Or.inr (Or.inr h))
      have hport := column_owner p (endpoint_columns_span p f hfcol) hspan
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with hz | hz
      · change z = EndpointStreet.f.column p f at hz
        have := midpoint_other_f_far l p hl hM he hf hport
        rw [← hz] at this
        omega
      · have hnear : Nat.dist z (p.x e.port) ≤ 12 := by
          have hx := readLength_add_lt_x p f.port 0
          change z = (if f.inward then p.x f.port + 2 else p.x f.port - 2) at hz
          rw [← hport]
          cases hd : f.inward <;>
            simp only [hd, Bool.false_eq_true, ite_false, ite_true] at hz <;>
            simp only [Nat.dist_eq_max_sub_min] <;> change 64 < p.x f.port at hx <;> omega
        have := midpoint_near_axis_far l p hl hM he hnear
        omega
    · obtain ⟨i, _, hz⟩ := List.mem_flatMap.mp hz
      have hicol : z ∈ centerColumns p i := List.mem_cons_of_mem _ hz
      have hport := column_owner p (center_columns_span p i hicol) hspan
      have hnear : Nat.dist z (p.x e.port) ≤ 12 := by
        have hx := readLength_add_lt_x p i 0
        change 64 < p.x i at hx
        rw [← hport]
        simp only [specialColumns, List.mem_cons, List.not_mem_nil, or_false] at hz
        change z = p.x i - 2 ∨ z = p.x i + 4 ∨ z = p.x i + 6 ∨ z = p.x i + 8 ∨ z = p.x i + 12 at hz
        simp only [Nat.dist_eq_max_sub_min]
        omega
      have := midpoint_near_axis_far l p hl hM he hnear
      omega

private theorem readerExit_midpoint_column_far (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    {e : Endpoint} (he : e ∈ l.endpoints) {a : Cell (p.W + 1) (p.H + 1)}
    (hae : a ∈ l.readerExitSet p) :
    p.K e.level < Nat.dist a.1.val ((EndpointStreet.f.column p e + p.x e.port) / 2) := by
  rcases hae with hcol | ⟨i, _, hi⟩
  · exact street_column_midpoint_far l p hl hM ha he hcol
  · by_contra! hclose
    have hspan := midpoint_close_span l p hl hM he hclose
    have hiSpan : p.x i - columnRadius p ≤ a.1.val ∧ a.1.val ≤ p.x i + columnRadius p := by
      dsimp only [columnRadius]
      simp only [Nat.dist_eq_max_sub_min] at hi
      omega
    have hport := column_owner p hiSpan hspan
    rw [hport] at hi
    have := midpoint_near_axis_far l p hl hM he (show Nat.dist a.1.val (p.x e.port) ≤ 12 by omega)
    omega

/-- Every precise reader exit is farther than `K` from an actual ordinary f-axis midpoint. -/
theorem endpoint_midpoint_readerExit_far (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    {e : Endpoint} (he : e ∈ l.endpoints) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q.1.val = (EndpointStreet.f.column p e + p.x e.port) / 2) :
    ∀ a ∈ l.readerExitSet p, p.K e.level < distance a q := by
  intro a hae
  have hcol := readerExit_midpoint_column_far l p hl hM ha he hae
  simp only [distance, hq]
  omega

end PushPuzzle.PushS.PortLayout
