/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Rack

/-! Equal initial and final rack occupancy freezes the whole extremal column. -/

@[expose] public section
namespace PushPuzzle.PushPush

open PushFS (Cell Direction Adjacent State)

variable {w h n k P : ℕ} {d : Direction} {s t u : State w h}

namespace Slide

private theorem vertical_column_of_ne (r : Slide d s n k) (hd : d = .north ∨ d = .south)
    (hx : s.player.1.val ≠ P) : line .south P r.boxes = line .south P s.boxes := by
  have hb : line .south P r.before = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨p, hp, hl, _⟩ := mem_line.mp hz
    exact hx ((r.vertical_before_lane hd hp).symm.trans hl)
  have ha : line .south P r.after = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨p, hp, hl, _⟩ := mem_line.mp hz
    exact hx ((r.vertical_after_lane hd hp).symm.trans hl)
  rw [Slide.boxes, line_union, line_sdiff, hb, ha, Finset.sdiff_empty, Finset.union_empty]

theorem vertical_column_starts (r : Slide d s n k) (hd : d = .north ∨ d = .south)
    (hx : s.player.1.val = P) (hn : 0 < n) (hk : 0 < k) (hv : s.player ∉ s.boxes)
    (ht : ∀ p ∈ r.boxes, ¬ Boundary p) :
    (Line.starts (line .south P r.boxes)).card + 1 =
      (Line.starts (line .south P s.boxes)).card := by
  have hc := r.line_starts_card hn hk hv ht
  rcases hd with rfl | rfl
  · change (Line.starts (line .north s.player.1.val r.boxes)).card + 1 =
      (Line.starts (line .north s.player.1.val s.boxes)).card at hc
    rw [hx] at hc
    have ht := line_starts_opposite_card .north P r.boxes
    have hs := line_starts_opposite_card .north P s.boxes
    simp only [Direction.opposite] at ht hs
    omega
  · change (Line.starts (line .south s.player.1.val r.boxes)).card + 1 =
      (Line.starts (line .south s.player.1.val s.boxes)).card at hc
    rwa [hx] at hc

end Slide

/-- With unchanged rack inventory, a move either fixes the rack or merges two components. -/
private theorem Move.rack_eq_or_starts_drop (hm : Move d s t) (hs : Supported .east P s)
    (ht : Interior t) (hcard : (line .south P t.boxes).card = (line .south P s.boxes).card) :
    line .south P t.boxes = line .south P s.boxes ∨
      (Line.starts (line .south P t.boxes)).card + 1 =
        (Line.starts (line .south P s.boxes)).card := by
  cases hm with
  | walk _ _ _ hb => exact Or.inl (by rw [hb])
  | push hv hn hk r _ hb =>
    have hti : ∀ p ∈ r.boxes, ¬ Boundary p := by simpa only [Interior, hb] using ht
    by_cases hd : d = .north ∨ d = .south
    · by_cases hx : s.player.1.val = P
      · exact Or.inr (by rw [hb]; exact r.vertical_column_starts hd hx hn hk hv hti)
      · exact Or.inl (by rw [hb]; exact r.vertical_column_of_ne hd hx)
    · have hh : d = .east ∨ d = .west := by cases d <;> simp_all
      apply Or.inl
      have hsub : line .south P t.boxes ⊆ line .south P s.boxes := by
        rw [hb, r.horizontal_column hn hk hh hs hti]
        exact Finset.sdiff_subset
      exact Finset.eq_of_subset_of_card_le hsub hcard.ge

private theorem Move.rack_starts_le (hm : Move d s t) (hs : Supported .east P s)
    (ht : Interior t) (hcard : (line .south P t.boxes).card = (line .south P s.boxes).card) :
    (Line.starts (line .south P t.boxes)).card ≤
      (Line.starts (line .south P s.boxes)).card := by
  rcases hm.rack_eq_or_starts_drop hs ht hcard with he | he
  · rw [he]
  · omega

/-- Equal endpoint rack inventory makes its number of components nonincreasing. -/
private theorem Reachable.rack_starts_le (hr : Reachable s t) (hs : Supported .east P s)
    (ht : Interior t) (hcard : (line .south P t.boxes).card = (line .south P s.boxes).card) :
    (Line.starts (line .south P t.boxes)).card ≤
      (Line.starts (line .south P s.boxes)).card := by
  induction hr with
  | refl => exact le_rfl
  | @tail v t hr hm ih =>
    have hv := hm.choose_spec.interior_source ht
    have hvs := Reachable.supported hr hv hs
    have hvcard := Reachable.rack_card_le hr hs hv
    have htcard := hm.choose_spec.rack_card_le hvs ht
    have hveq : (line .south P v.boxes).card = (line .south P s.boxes).card := by omega
    exact (hm.choose_spec.rack_starts_le hvs ht (by omega)).trans (ih hv hveq)

/-- Equal inventory and component counts force exact rack equality. -/
private theorem Reachable.rack_eq_of_counts_eq (hr : Reachable s t) (hs : Supported .east P s)
    (ht : Interior t) (hcard : (line .south P t.boxes).card = (line .south P s.boxes).card)
    (hstarts : (Line.starts (line .south P t.boxes)).card =
      (Line.starts (line .south P s.boxes)).card) :
    line .south P t.boxes = line .south P s.boxes := by
  induction hr with
  | refl => rfl
  | @tail v t hr hm ih =>
    have hv := hm.choose_spec.interior_source ht
    have hvs := Reachable.supported hr hv hs
    have hvcard := Reachable.rack_card_le hr hs hv
    have htcard := hm.choose_spec.rack_card_le hvs ht
    have hveq : (line .south P v.boxes).card = (line .south P s.boxes).card := by omega
    have hvcomp := Reachable.rack_starts_le hr hs hv hveq
    have htcomp := hm.choose_spec.rack_starts_le hvs ht (by omega)
    have hvc : (Line.starts (line .south P v.boxes)).card =
        (Line.starts (line .south P s.boxes)).card := by omega
    have he : line .south P t.boxes = line .south P v.boxes := by
      rcases hm.choose_spec.rack_eq_or_starts_drop hvs ht (by omega) with he | he
      · exact he
      · omega
    exact he.trans (ih hv hveq hvc)

/-- Every state of an interior trajectory with restored final rack has the initial rack. -/
theorem Reachable.rack_frozen (hprefix : Reachable s u) (hsuffix : Reachable u t)
    (hs : Supported .east P s) (ht : Interior t)
    (hfinal : line .south P t.boxes = line .south P s.boxes) :
    line .south P u.boxes = line .south P s.boxes := by
  have hu := hsuffix.interior_source ht
  have hus := hprefix.supported hu hs
  have hc1 := hprefix.rack_card_le hs hu
  have hc2 := hsuffix.rack_card_le hus ht
  have hcard := congrArg Finset.card hfinal
  have hucard : (line .south P u.boxes).card = (line .south P s.boxes).card := by omega
  have hscard : (line .south P t.boxes).card = (line .south P u.boxes).card := by omega
  have hh1 := hprefix.rack_starts_le hs hu hucard
  have hh2 := hsuffix.rack_starts_le hus ht hscard
  have hcomp := congrArg (fun S : Finset ℤ => (Line.starts S).card) hfinal
  exact hprefix.rack_eq_of_counts_eq hs hu hucard (by omega)

end PushPuzzle.PushPush
