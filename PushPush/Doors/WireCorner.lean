/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.WireDeadlock

/-! A travelling wire signal may advance or consume its next stopping pin. -/

@[expose] public section

namespace PushPuzzle.PushPush.Doors.Wire

open PushFS (Cell State Direction Adjacent)

variable {w h : ℕ}

/-- The previous pin is beside the signal, perpendicular to its next leg. -/
def Corner (forward : Direction) (signal previous stop : Cell w h) : Prop :=
  (∃ side, Adjacent side signal previous) ∧
    forward.lane previous ≠ forward.lane signal ∧
    forward.lane stop = forward.lane signal ∧
    forward.position signal + 3 ≤ forward.position stop

/-- The previous pin and the next pin cover both physical lines through the signal. -/
theorem corner_lane_cover {forward : Direction} {signal previous stop : Cell w h}
    (hc : Corner forward signal previous stop) (d : Direction) :
    d.lane signal = d.lane previous ∨ d.lane signal = d.lane stop := by
  obtain ⟨⟨side, hside⟩, hperp, hstoplane, _⟩ := hc
  cases forward <;> cases side <;> cases d <;>
    simp_all [Adjacent, Direction.lane]

theorem opposite_lane (d : Direction) (p : Cell w h) :
    d.opposite.lane p = d.lane p := by cases d <;> rfl

private theorem opposite_position (d : Direction) (p : Cell w h) :
    d.opposite.position p = -d.position p := by
  cases d <;> simp [Direction.opposite, Direction.position]

theorem corner_forward_isolated {forward : Direction} {signal previous stop q : Cell w h}
    (hc : Corner forward signal previous stop) (ha : Adjacent forward signal q) :
    q ∉ ({signal, previous, stop} : Finset (Cell w h)) := by
  intro hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl
  · exact ha.ne rfl
  · exact hc.2.1 ha.lane
  · have hp := ha.position
    have hb := hc.2.2.2
    omega

private theorem corner_reverse_isolated {forward : Direction} {signal previous stop q : Cell w h}
    (hc : Corner forward signal previous stop) (ha : Adjacent forward.opposite stop q) :
    q ∉ ({signal, previous, stop} : Finset (Cell w h)) := by
  intro hq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl | rfl
  · have hp := ha.position
    simp only [opposite_position] at hp
    have hb := hc.2.2.2
    omega
  · have hl := ha.lane
    simp only [opposite_lane] at hl
    exact hc.2.1 (hl.trans hc.2.2.1)
  · exact ha.ne rfl

/-- Consuming the next pin creates an adjacent right-angle cluster. -/
theorem reverse_corner_lineConvex {forward : Direction}
    {signal previous stop landed : Cell w h} (hc : Corner forward signal previous stop)
    (hland : Adjacent forward signal landed) :
    LineConvex ({signal, previous, landed} : Finset (Cell w h)) := by
  obtain ⟨⟨side, hside⟩, hperp, _, _⟩ := hc
  apply elbow_lineConvex hside hland
  cases side <;> cases forward <;>
    simp_all [Adjacent, Direction.lane] <;> omega

/-- The sole separated collinear pair in a wire corner is signal/next-pin. -/
private theorem corner_pair {forward d : Direction} {signal previous stop p q : Cell w h}
    (hc : Corner forward signal previous stop)
    (hp : p ∈ ({signal, previous, stop} : Finset (Cell w h)))
    (hq : q ∈ ({signal, previous, stop} : Finset (Cell w h)))
    (hlane : d.lane q = d.lane p) (hpos : d.position p + 2 ≤ d.position q) :
    (p = signal ∧ q = stop ∧ d = forward) ∨
      (p = stop ∧ q = signal ∧ d = forward.opposite) := by
  obtain ⟨⟨side, hside⟩, hperp, hstoplane, hstopp⟩ := hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
  rcases hp with rfl | rfl | rfl <;>
    rcases hq with rfl | rfl | rfl <;>
    cases forward <;> cases side <;> cases d <;>
    simp_all [Direction.position, Direction.lane, Direction.opposite, Adjacent] <;> omega

-- Enumerate directions and the four possible cluster cells.
set_option maxHeartbeats 800000 in
/-- A pin beside the previous pin adds only an adjacent pair to the corner.
This is the temporary fourth box in a same-sign B/C reverse-pin branch. -/
private theorem extended_corner_pair {forward d : Direction}
    {signal previous extra stop p q : Cell w h}
    (hc : Corner forward signal previous stop) (he : Adjacent forward.opposite previous extra)
    (hp : p ∈ ({signal, previous, extra, stop} : Finset (Cell w h)))
    (hq : q ∈ ({signal, previous, extra, stop} : Finset (Cell w h)))
    (hlane : d.lane q = d.lane p) (hpos : d.position p + 2 ≤ d.position q) :
    (p = signal ∧ q = stop ∧ d = forward) ∨
      (p = stop ∧ q = signal ∧ d = forward.opposite) := by
  have hx : ∀ (e : Direction), ∀ z ∈ ({signal, previous, extra, stop} : Finset (Cell w h)),
      e.lane z = e.lane extra → e.position extra + 2 ≤ e.position z → False := by
    intro e z hz hl hp
    obtain ⟨⟨side, hside⟩, hperp, hstoplane, hstopp⟩ := hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl | rfl <;>
      cases forward <;> cases side <;> cases e <;>
      simp only [Direction.position, Direction.lane, Direction.opposite, Adjacent] at * <;> omega
  by_cases hpe : p = extra
  · subst p
    exact False.elim (hx d q hq hlane hpos)
  by_cases hqe : q = extra
  · subst q
    apply False.elim
    apply hx d.opposite p hp
    · simpa only [opposite_lane] using hlane.symm
    · simp only [opposite_position]
      omega
  apply corner_pair hc _ _ hlane hpos
  · simpa only [Finset.mem_insert, Finset.mem_singleton, hpe, false_or] using hp
  · simpa only [Finset.mem_insert, Finset.mem_singleton, hqe, false_or] using hq

-- Enumerate directions and the four possible cluster cells.
set_option maxHeartbeats 800000 in
/-- Pulling the distant box toward the near box leaves a compact four-box dead cluster. -/
theorem extended_reverse_lineConvex {forward : Direction}
    {signal previous extra stop landed : Cell w h}
    (hc : Corner forward signal previous stop) (he : Adjacent forward.opposite previous extra)
    (hland : Adjacent forward signal landed) :
    LineConvex ({signal, previous, extra, landed} : Finset (Cell w h)) := by
  obtain ⟨⟨side, hside⟩, hperp, _, _⟩ := hc
  apply lineConvex_of_short_lines
  intro d p hp q hq hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
  rcases hp with rfl | rfl | rfl | rfl <;>
    rcases hq with rfl | rfl | rfl | rfl <;>
    cases forward <;> cases side <;> cases d <;>
    simp only [Direction.position, Direction.lane, Direction.opposite, Adjacent] at * <;> omega

-- Enumerate directions and the four possible cluster cells.
set_option maxHeartbeats 800000 in
/-- Sliding the near box to the distant one leaves two isolated adjacent pairs. -/
theorem extended_forward_lineConvex {forward : Direction}
    {signal previous extra stop landed : Cell w h}
    (hc : Corner forward signal previous stop) (he : Adjacent forward.opposite previous extra)
    (hland : Adjacent forward landed stop) :
    LineConvex ({previous, extra, stop, landed} : Finset (Cell w h)) := by
  obtain ⟨⟨side, hside⟩, hperp, hstoplane, hstopp⟩ := hc
  apply lineConvex_of_short_lines
  intro d p hp q hq hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
  rcases hp with rfl | rfl | rfl | rfl <;>
    rcases hq with rfl | rfl | rfl | rfl <;>
    cases forward <;> cases side <;> cases d <;>
    simp only [Direction.position, Direction.lane, Direction.opposite, Adjacent] at * <;> omega

/-- An interior slide involving this corner can only move the signal forward or
the distant pin backward. This includes all lengths allowed by unlimited pushing. -/
theorem corner_slide_pair {s : State w h} {d forward : Direction} {n k : ℕ}
    (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hinterior : ∀ p ∈ r.boxes, ¬ Boundary p) (signal previous stop : Cell w h)
    (hc : Corner forward signal previous stop)
    (hclosed : LineClosed {signal, previous, stop} s.boxes)
    (hfirst : r.cell ⟨1, by omega⟩ ∈ ({signal, previous, stop} : Finset (Cell w h))) :
    ∃ stopper ∈ s.boxes, Adjacent d (r.cell ⟨n + k, by omega⟩) stopper ∧
      ((r.cell ⟨1, by omega⟩ = signal ∧ stopper = stop ∧ d = forward) ∨
        (r.cell ⟨1, by omega⟩ = stop ∧ stopper = signal ∧ d = forward.opposite)) := by
  obtain ⟨stopper, hbox, ha⟩ := r.exists_stopper hn hinterior
  have hlanestop : d.lane stopper = d.lane s.player := ha.lane.trans (r.lane _)
  have hs : stopper ∈ ({signal, previous, stop} : Finset (Cell w h)) :=
    hclosed d _ hfirst stopper hbox (hlanestop.trans (r.lane _).symm)
  refine ⟨stopper, hbox, ha, corner_pair hc hfirst hs
    (hlanestop.trans (r.lane _).symm) ?_⟩
  have hp := r.position ⟨1, by omega⟩
  have hlast := r.position ⟨n + k, by omega⟩
  have hstop := ha.position
  change d.position (r.cell ⟨1, by omega⟩) = d.position s.player + (1 : ℕ) at hp
  change d.position (r.cell ⟨n + k, by omega⟩) =
    d.position s.player + (n + k : ℕ) at hlast
  omega

/-- The complete physical classification of a normal private corner. -/
theorem corner_slide {s : State w h} {d forward : Direction} {n k : ℕ}
    (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hinterior : ∀ p ∈ r.boxes, ¬ Boundary p) (signal previous stop : Cell w h)
    (hc : Corner forward signal previous stop)
    (hclosed : LineClosed {signal, previous, stop} s.boxes)
    (hfirst : r.cell ⟨1, by omega⟩ ∈ ({signal, previous, stop} : Finset (Cell w h))) :
    n = 1 ∧
      ((d = forward ∧ r.cell ⟨1, by omega⟩ = signal ∧
          Adjacent d (r.cell ⟨n + k, by omega⟩) stop) ∨
        (d = forward.opposite ∧ r.cell ⟨1, by omega⟩ = stop ∧
          Adjacent d (r.cell ⟨n + k, by omega⟩) signal)) := by
  obtain ⟨stopper, _, ha, hpair⟩ := corner_slide_pair r hn hk hinterior signal previous stop
    hc hclosed hfirst
  rcases hpair with ⟨hfirsteq, rfl, rfl⟩ | ⟨hfirsteq, rfl, rfl⟩
  · have hn1 : n = 1 := by
      apply Doors.slide_length_one r hn
      intro q hq hb
      apply corner_forward_isolated hc (hfirsteq ▸ hq)
      exact hclosed _ _ hfirst q hb hq.lane
    exact ⟨hn1, Or.inl ⟨rfl, hfirsteq, ha⟩⟩
  · have hn1 : n = 1 := by
      apply Doors.slide_length_one r hn
      intro q hq hb
      apply corner_reverse_isolated hc (hfirsteq ▸ hq)
      exact hclosed _ _ hfirst q hb hq.lane
    exact ⟨hn1, Or.inr ⟨rfl, hfirsteq, ha⟩⟩

/-- The same-sign reverse-pin branch permits only the single attraction of its
two separated boxes; both choices leave the compact clusters certified above. -/
private theorem extended_corner_slide_pair {s : State w h} {d forward : Direction} {n k : ℕ}
    (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hinterior : ∀ p ∈ r.boxes, ¬ Boundary p) (signal previous extra stop : Cell w h)
    (hc : Corner forward signal previous stop) (he : Adjacent forward.opposite previous extra)
    (hclosed : LineClosed {signal, previous, extra, stop} s.boxes)
    (hfirst : r.cell ⟨1, by omega⟩ ∈ ({signal, previous, extra, stop} : Finset (Cell w h))) :
    ∃ stopper ∈ s.boxes, Adjacent d (r.cell ⟨n + k, by omega⟩) stopper ∧
      ((r.cell ⟨1, by omega⟩ = signal ∧ stopper = stop ∧ d = forward) ∨
        (r.cell ⟨1, by omega⟩ = stop ∧ stopper = signal ∧ d = forward.opposite)) := by
  obtain ⟨stopper, hbox, ha⟩ := r.exists_stopper hn hinterior
  have hlanestop : d.lane stopper = d.lane s.player := ha.lane.trans (r.lane _)
  have hs : stopper ∈ ({signal, previous, extra, stop} : Finset (Cell w h)) :=
    hclosed d _ hfirst stopper hbox (hlanestop.trans (r.lane _).symm)
  refine ⟨stopper, hbox, ha, extended_corner_pair hc he hfirst hs
    (hlanestop.trans (r.lane _).symm) ?_⟩
  have hp := r.position ⟨1, by omega⟩
  have hlast := r.position ⟨n + k, by omega⟩
  have hstop := ha.position
  change d.position (r.cell ⟨1, by omega⟩) = d.position s.player + (1 : ℕ) at hp
  change d.position (r.cell ⟨n + k, by omega⟩) =
    d.position s.player + (n + k : ℕ) at hlast
  omega

/-- Both attraction choices in the four-box branch still move a single box. -/
theorem extended_corner_slide {s : State w h} {d forward : Direction} {n k : ℕ}
    (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hinterior : ∀ p ∈ r.boxes, ¬ Boundary p) (signal previous extra stop : Cell w h)
    (hc : Corner forward signal previous stop) (he : Adjacent forward.opposite previous extra)
    (hclosed : LineClosed {signal, previous, extra, stop} s.boxes)
    (hfirst : r.cell ⟨1, by omega⟩ ∈ ({signal, previous, extra, stop} : Finset (Cell w h))) :
    n = 1 ∧
      ((d = forward ∧ r.cell ⟨1, by omega⟩ = signal ∧
          Adjacent d (r.cell ⟨n + k, by omega⟩) stop) ∨
        (d = forward.opposite ∧ r.cell ⟨1, by omega⟩ = stop ∧
          Adjacent d (r.cell ⟨n + k, by omega⟩) signal)) := by
  have hextralane := he.lane
  simp only [opposite_lane] at hextralane
  obtain ⟨stopper, _, ha, hpair⟩ := extended_corner_slide_pair r hn hk hinterior
    signal previous extra stop hc he hclosed hfirst
  rcases hpair with ⟨hfirsteq, rfl, rfl⟩ | ⟨hfirsteq, rfl, rfl⟩
  · have hn1 : n = 1 := by
      apply Doors.slide_length_one r hn
      intro q hq hb
      have hmem := hclosed _ _ hfirst q hb hq.lane
      have hnotextra : q ≠ extra := by
        intro hqe
        subst q
        have hl := hq.lane
        rw [hfirsteq] at hl
        exact hc.2.1 (hextralane.symm.trans hl)
      apply corner_forward_isolated hc (hfirsteq ▸ hq)
      simpa only [Finset.mem_insert, Finset.mem_singleton, hnotextra, false_or] using hmem
    exact ⟨hn1, Or.inl ⟨rfl, hfirsteq, ha⟩⟩
  · have hn1 : n = 1 := by
      apply Doors.slide_length_one r hn
      intro q hq hb
      have hmem := hclosed _ _ hfirst q hb hq.lane
      have hnotextra : q ≠ extra := by
        intro hqe
        subst q
        have hl := hq.lane
        rw [hfirsteq] at hl
        simp only [opposite_lane] at hl
        exact hc.2.1 (hextralane.symm.trans (hl.trans hc.2.2.1))
      apply corner_reverse_isolated hc (hfirsteq ▸ hq)
      simpa only [Finset.mem_insert, Finset.mem_singleton, hnotextra, false_or] using hmem
    exact ⟨hn1, Or.inr ⟨rfl, hfirsteq, ha⟩⟩

end PushPuzzle.PushPush.Doors.Wire
