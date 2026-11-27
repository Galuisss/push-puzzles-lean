/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.RoomSlide

/-! Safe vertical motion in a two-slot door room. -/

@[expose] public section

namespace PushPuzzle.PushPush.Doors.Room

open PushFS (Cell State Direction Adjacent)

variable {w h : ℕ}

/-- Between two dividers the working column contains precisely the two slot boxes. -/
def Column (s : State w h) (x : Fin w) (g : ℕ) (moving stationary : Slot) : Prop :=
  ∀ p : Cell w h, p.1 = x → g ≤ p.2.val → p.2.val ≤ g + 90 →
    (p ∈ s.boxes ↔ p.2.val = g ∨ p.2.val = g + 90 ∨
      p.2.val = g + moving.row ∨ p.2.val = g + stationary.row)

/-- A safe room interaction slides one box into the other, leaving it adjacent.
Motion toward a divider would occupy one of its two forbidden neighboring cells. -/
theorem collision {s : State w h} {d : Direction} {n k : ℕ}
    (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (x : Fin w) (g : ℕ) (moving stationary : Slot)
    (hne : moving ≠ stationary) (hc : Column s x g moving stationary)
    (hfirst : (r.cell ⟨1, by omega⟩).1 = x ∧
      (r.cell ⟨1, by omega⟩).2.val = g + moving.row)
    (hvertical : d = .north ∨ d = .south)
    (hroom : g + 90 < h)
    (hsafe : (r.cell ⟨n + k, by omega⟩).2.val ≠ g + 1 ∧
      (r.cell ⟨n + k, by omega⟩).2.val ≠ g + 89) :
    n = 1 ∧ (r.cell ⟨n + k, by omega⟩).2.val = g + landing moving stationary := by
  have hm := slot_row_bounds moving
  have hs := slot_row_bounds stationary
  have hsep := slot_separation moving stationary hne
  have hn1 : n = 1 := by
    apply Doors.slide_length_one r hn
    intro q ha hbox
    rcases hvertical with rfl | rfl
    · simp only [Adjacent] at ha
      have hx : q.1 = x := ha.1.trans hfirst.1
      have hb := (hc q hx (by omega) (by omega)).mp hbox
      omega
    · simp only [Adjacent] at ha
      have hx : q.1 = x := ha.1.trans hfirst.1
      have hb := (hc q hx (by omega) (by omega)).mp hbox
      omega
  subst n
  refine ⟨rfl, ?_⟩
  rcases hvertical with rfl | rfl
  · have hpfirst := r.position ⟨1, by omega⟩
    have hlfirst := r.lane ⟨1, by omega⟩
    simp only [Direction.position, Direction.lane] at hpfirst hlfirst
    change -(r.cell ⟨1, by omega⟩).2.val = -(s.player.2.val : ℤ) + (1 : ℕ) at hpfirst
    have hpx : s.player.1 = x := Fin.ext (by omega)
    by_cases hlt : stationary.row < moving.row
    · let stop : Cell w h := (x, ⟨g + stationary.row, by omega⟩)
      have hd : k = moving.row - stationary.row - 1 := by
        apply Doors.slide_distance_eq r stop (moving.row - stationary.row - 1)
        · simp [Direction.lane, stop, hpx]
        · simp only [Direction.position]
          dsimp [stop]
          omega
        · apply (hc stop rfl (by dsimp [stop]; omega) (by dsimp [stop]; omega)).mpr
          exact Or.inr (Or.inr (Or.inr rfl))
        · intro p hpl hlo hhi hbox
          have hpcol : p.1 = x := Fin.ext (by
            simpa [Direction.lane, hpx] using hpl)
          simp only [Direction.position] at hlo hhi
          dsimp [stop] at hhi
          have hb := (hc p hpcol (by omega) (by omega)).mp hbox
          omega
      have hp := r.position ⟨1 + k, by omega⟩
      simp only [Direction.position] at hp
      change -(r.cell ⟨1 + k, by omega⟩).2.val =
        -(s.player.2.val : ℤ) + (1 + k : ℕ) at hp
      unfold landing
      split <;> omega
    · let stop : Cell w h := (x, ⟨g, by omega⟩)
      have hd : k = moving.row - 1 := by
        apply Doors.slide_distance_eq r stop (moving.row - 1)
        · simp [Direction.lane, stop, hpx]
        · simp only [Direction.position]
          dsimp [stop]
          omega
        · apply (hc stop rfl (by dsimp [stop]; omega) (by dsimp [stop]; omega)).mpr
          exact Or.inl rfl
        · intro p hpl hlo hhi hbox
          have hpcol : p.1 = x := Fin.ext (by
            simpa [Direction.lane, hpx] using hpl)
          simp only [Direction.position] at hlo hhi
          dsimp [stop] at hhi
          have hb := (hc p hpcol (by omega) (by omega)).mp hbox
          omega
      have hp := r.position ⟨1 + k, by omega⟩
      simp only [Direction.position] at hp
      change -(r.cell ⟨1 + k, by omega⟩).2.val =
        -(s.player.2.val : ℤ) + (1 + k : ℕ) at hp
      exact False.elim (hsafe.1 (by omega))
  · have hpfirst := r.position ⟨1, by omega⟩
    have hlfirst := r.lane ⟨1, by omega⟩
    simp only [Direction.position, Direction.lane] at hpfirst hlfirst
    change (r.cell ⟨1, by omega⟩).2.val = (s.player.2.val : ℤ) + (1 : ℕ) at hpfirst
    have hpx : s.player.1 = x := Fin.ext (by omega)
    by_cases hlt : moving.row < stationary.row
    · let stop : Cell w h := (x, ⟨g + stationary.row, by omega⟩)
      have hd : k = stationary.row - moving.row - 1 := by
        apply Doors.slide_distance_eq r stop (stationary.row - moving.row - 1)
        · simp [Direction.lane, stop, hpx]
        · simp only [Direction.position]
          dsimp [stop]
          omega
        · apply (hc stop rfl (by dsimp [stop]; omega) (by dsimp [stop]; omega)).mpr
          exact Or.inr (Or.inr (Or.inr rfl))
        · intro p hpl hlo hhi hbox
          have hpcol : p.1 = x := Fin.ext (by
            simpa [Direction.lane, hpx] using hpl)
          simp only [Direction.position] at hlo hhi
          dsimp [stop] at hhi
          have hb := (hc p hpcol (by omega) (by omega)).mp hbox
          omega
      have hp := r.position ⟨1 + k, by omega⟩
      simp only [Direction.position] at hp
      change (r.cell ⟨1 + k, by omega⟩).2.val =
        (s.player.2.val : ℤ) + (1 + k : ℕ) at hp
      unfold landing
      split <;> omega
    · let stop : Cell w h := (x, ⟨g + 90, hroom⟩)
      have hd : k = 90 - moving.row - 1 := by
        apply Doors.slide_distance_eq r stop (90 - moving.row - 1)
        · simp [Direction.lane, stop, hpx]
        · simp only [Direction.position]
          dsimp [stop]
          omega
        · apply (hc stop rfl (by dsimp [stop]; omega) (by dsimp [stop]; omega)).mpr
          exact Or.inr (Or.inl rfl)
        · intro p hpl hlo hhi hbox
          have hpcol : p.1 = x := Fin.ext (by
            simpa [Direction.lane, hpx] using hpl)
          simp only [Direction.position] at hlo hhi
          dsimp [stop] at hhi
          have hb := (hc p hpcol (by omega) (by omega)).mp hbox
          omega
      have hp := r.position ⟨1 + k, by omega⟩
      simp only [Direction.position] at hp
      change (r.cell ⟨1 + k, by omega⟩).2.val =
        (s.player.2.val : ℤ) + (1 + k : ℕ) at hp
      exact False.elim (hsafe.2 (by omega))

/-- The working column immediately after a two-slot collision. -/
def PairColumn (s : State w h) (x : Fin w) (g a : ℕ) : Prop :=
  ∀ p : Cell w h, p.1 = x → g ≤ p.2.val → p.2.val ≤ g + 90 →
    (p ∈ s.boxes ↔ p.2.val = g ∨ p.2.val = g + 90 ∨
      p.2.val = a ∨ p.2.val = a + 1)

/-- A resting room has one register box between its two dividers. -/
def SoloColumn (s : State w h) (x : Fin w) (g row : ℕ) : Prop :=
  ∀ p : Cell w h, p.1 = x → g ≤ p.2.val → p.2.val ≤ g + 90 →
    (p ∈ s.boxes ↔ p.2.val = g ∨ p.2.val = g + 90 ∨ p.2.val = g + row)

/-- A resting register pushed vertically stops in a forbidden divider-neighbor cell. -/
theorem solo_collision {s : State w h} {d : Direction} {n k : ℕ}
    (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (x : Fin w) (g row : ℕ) (hroom : g + 90 < h)
    (hrow : 3 ≤ row ∧ row + 3 ≤ 90) (hc : SoloColumn s x g row)
    (hfirst : (r.cell ⟨1, by omega⟩).1 = x ∧
      (r.cell ⟨1, by omega⟩).2.val = g + row)
    (hvertical : d = .north ∨ d = .south) :
    n = 1 ∧ ((r.cell ⟨n + k, by omega⟩).2.val = g + 1 ∨
      (r.cell ⟨n + k, by omega⟩).2.val = g + 89) := by
  have hn1 : n = 1 := by
    apply Doors.slide_length_one r hn
    intro q ha hbox
    rcases hvertical with rfl | rfl
    · simp only [Adjacent] at ha
      have hx : q.1 = x := ha.1.trans hfirst.1
      have hb := (hc q hx (by omega) (by omega)).mp hbox
      omega
    · simp only [Adjacent] at ha
      have hx : q.1 = x := ha.1.trans hfirst.1
      have hb := (hc q hx (by omega) (by omega)).mp hbox
      omega
  subst n
  refine ⟨rfl, ?_⟩
  rcases hvertical with rfl | rfl
  · apply Or.inl
    have hpfirst := r.position ⟨1, by omega⟩
    have hlfirst := r.lane ⟨1, by omega⟩
    simp only [Direction.position, Direction.lane] at hpfirst hlfirst
    change -(r.cell ⟨1, by omega⟩).2.val = -(s.player.2.val : ℤ) + (1 : ℕ) at hpfirst
    have hpx : s.player.1 = x := Fin.ext (by omega)
    let stop : Cell w h := (x, ⟨g, by omega⟩)
    have hd : k = row - 1 := by
      apply Doors.slide_distance_eq r stop (row - 1)
      · simp [Direction.lane, stop, hpx]
      · simp only [Direction.position]
        dsimp [stop]
        omega
      · apply (hc stop rfl (by dsimp [stop]; omega) (by dsimp [stop]; omega)).mpr
        exact Or.inl rfl
      · intro p hpl hlo hhi hbox
        have hpcol : p.1 = x := Fin.ext (by
          simpa [Direction.lane, hpx] using hpl)
        simp only [Direction.position] at hlo hhi
        dsimp [stop] at hhi
        have hb := (hc p hpcol (by omega) (by omega)).mp hbox
        omega
    have hp := r.position ⟨1 + k, by omega⟩
    simp only [Direction.position] at hp
    change -(r.cell ⟨1 + k, by omega⟩).2.val =
      -(s.player.2.val : ℤ) + (1 + k : ℕ) at hp
    omega
  · apply Or.inr
    have hpfirst := r.position ⟨1, by omega⟩
    have hlfirst := r.lane ⟨1, by omega⟩
    simp only [Direction.position, Direction.lane] at hpfirst hlfirst
    change (r.cell ⟨1, by omega⟩).2.val = (s.player.2.val : ℤ) + (1 : ℕ) at hpfirst
    have hpx : s.player.1 = x := Fin.ext (by omega)
    let stop : Cell w h := (x, ⟨g + 90, hroom⟩)
    have hd : k = 89 - row := by
      apply Doors.slide_distance_eq r stop (89 - row)
      · simp [Direction.lane, stop, hpx]
      · simp only [Direction.position]
        dsimp [stop]
        omega
      · apply (hc stop rfl (by dsimp [stop]; omega) (by dsimp [stop]; omega)).mpr
        exact Or.inr (Or.inl rfl)
      · intro p hpl hlo hhi hbox
        have hpcol : p.1 = x := Fin.ext (by
          simpa [Direction.lane, hpx] using hpl)
        simp only [Direction.position] at hlo hhi
        dsimp [stop] at hhi
        have hb := (hc p hpcol (by omega) (by omega)).mp hbox
        omega
    have hp := r.position ⟨1 + k, by omega⟩
    simp only [Direction.position] at hp
    change (r.cell ⟨1 + k, by omega⟩).2.val =
      (s.player.2.val : ℤ) + (1 + k : ℕ) at hp
    omega

/-- Moving the adjacent collision pair vertically necessarily occupies a divider neighbor. -/
theorem pair_collision {s : State w h} {d : Direction} {n k : ℕ}
    (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (x : Fin w) (g a : ℕ) (hroom : g + 90 < h)
    (hlo : g + 3 ≤ a) (hhi : a + 3 ≤ g + 90) (hc : PairColumn s x g a)
    (hfirst : (r.cell ⟨1, by omega⟩).1 = x)
    (hhead : (d = .north ∧ (r.cell ⟨1, by omega⟩).2.val = a + 1) ∨
      (d = .south ∧ (r.cell ⟨1, by omega⟩).2.val = a)) :
    n = 2 ∧ ((r.cell ⟨n + k, by omega⟩).2.val = g + 1 ∨
      (r.cell ⟨n + k, by omega⟩).2.val = g + 89) := by
  rcases hhead with ⟨rfl, hy⟩ | ⟨rfl, hy⟩
  · let next : Cell w h := (x, ⟨a, by omega⟩)
    have hn2 : n = 2 := by
      apply Doors.slide_length_two r hn hk next
      · simp only [Adjacent]
        exact ⟨hfirst.symm, by dsimp [next]; omega⟩
      · apply (hc next rfl (by dsimp [next]; omega) (by dsimp [next]; omega)).mpr
        exact Or.inr (Or.inr (Or.inl rfl))
      · intro q ha hbox
        simp only [Adjacent] at ha
        have hx : q.1 = x := ha.1
        dsimp [next] at ha
        have hb := (hc q hx (by omega) (by omega)).mp hbox
        omega
    subst n
    refine ⟨rfl, Or.inl ?_⟩
    have hpfirst := r.position ⟨1, by omega⟩
    have hlfirst := r.lane ⟨1, by omega⟩
    simp only [Direction.position, Direction.lane] at hpfirst hlfirst
    change -(r.cell ⟨1, by omega⟩).2.val = -(s.player.2.val : ℤ) + (1 : ℕ) at hpfirst
    have hpx : s.player.1 = x := Fin.ext (by omega)
    let stop : Cell w h := (x, ⟨g, by omega⟩)
    have hd : k = a - g - 1 := by
      apply Doors.slide_distance_eq r stop (a - g - 1)
      · simp [Direction.lane, stop, hpx]
      · simp only [Direction.position]
        dsimp [stop]
        omega
      · apply (hc stop rfl (by dsimp [stop]; omega) (by dsimp [stop]; omega)).mpr
        exact Or.inl rfl
      · intro p hpl hlo hhi hbox
        have hpcol : p.1 = x := Fin.ext (by
          simpa [Direction.lane, hpx] using hpl)
        simp only [Direction.position] at hlo hhi
        dsimp [stop] at hhi
        have hb := (hc p hpcol (by omega) (by omega)).mp hbox
        omega
    have hp := r.position ⟨2 + k, by omega⟩
    simp only [Direction.position] at hp
    change -(r.cell ⟨2 + k, by omega⟩).2.val =
      -(s.player.2.val : ℤ) + (2 + k : ℕ) at hp
    omega
  · let next : Cell w h := (x, ⟨a + 1, by omega⟩)
    have hn2 : n = 2 := by
      apply Doors.slide_length_two r hn hk next
      · simp only [Adjacent]
        exact ⟨hfirst.symm, by dsimp [next]; omega⟩
      · apply (hc next rfl (by dsimp [next]; omega) (by dsimp [next]; omega)).mpr
        exact Or.inr (Or.inr (Or.inr rfl))
      · intro q ha hbox
        simp only [Adjacent] at ha
        have hx : q.1 = x := ha.1
        dsimp [next] at ha
        have hb := (hc q hx (by omega) (by omega)).mp hbox
        omega
    subst n
    refine ⟨rfl, Or.inr ?_⟩
    have hpfirst := r.position ⟨1, by omega⟩
    have hlfirst := r.lane ⟨1, by omega⟩
    simp only [Direction.position, Direction.lane] at hpfirst hlfirst
    change (r.cell ⟨1, by omega⟩).2.val = (s.player.2.val : ℤ) + (1 : ℕ) at hpfirst
    have hpx : s.player.1 = x := Fin.ext (by omega)
    let stop : Cell w h := (x, ⟨g + 90, hroom⟩)
    have hd : k = g + 90 - a - 2 := by
      apply Doors.slide_distance_eq r stop (g + 90 - a - 2)
      · simp [Direction.lane, stop, hpx]
      · simp only [Direction.position]
        dsimp [stop]
        omega
      · apply (hc stop rfl (by dsimp [stop]; omega) (by dsimp [stop]; omega)).mpr
        exact Or.inr (Or.inl rfl)
      · intro p hpl hlo hhi hbox
        have hpcol : p.1 = x := Fin.ext (by
          simpa [Direction.lane, hpx] using hpl)
        simp only [Direction.position] at hlo hhi
        dsimp [stop] at hhi
        have hb := (hc p hpcol (by omega) (by omega)).mp hbox
        omega
    have hp := r.position ⟨2 + k, by omega⟩
    simp only [Direction.position] at hp
    change (r.cell ⟨2 + k, by omega⟩).2.val =
      (s.player.2.val : ℤ) + (2 + k : ℕ) at hp
    omega

end PushPuzzle.PushPush.Doors.Room
