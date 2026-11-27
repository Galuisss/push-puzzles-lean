/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushFS.Grid
public import Mathlib.Data.Finset.Card
public import Mathlib.Logic.Relation

/-! The committed reader's three-hole seal under column transports and transverse deletions. -/

@[expose] public section
namespace PushPuzzle.Push.Seal

/-- Coloured column holes and the number of holes deleted transversely in each colour. -/
structure State where
  red : Finset ℤ
  blue : Finset ℤ
  deletedRed : ℕ
  deletedBlue : ℕ

/-- The unlabelled one-dimensional hole set. -/
def State.holes (s : State) : Finset ℤ := s.red ∪ s.blue

def State.eraseRed (s : State) (q : ℤ) : State :=
  { s with red := s.red.erase q, deletedRed := s.deletedRed + 1 }

def State.eraseBlue (s : State) (q : ℤ) : State :=
  { s with blue := s.blue.erase q, deletedBlue := s.deletedBlue + 1 }

/-- The first destination hole is replaced by a hole of the support hole's red colour. -/
def State.redTransport (s : State) (q b : ℤ) : State :=
  { s with red := insert b (s.red.erase q), blue := s.blue.erase q }

def State.blueTransport (s : State) (q b : ℤ) : State :=
  { s with red := s.red.erase q, blue := insert b (s.blue.erase q) }

/-- Strictly between two coordinates, in either travel direction. -/
def Between (a q z : ℤ) : Prop := (a < z ∧ z < q) ∨ (q < z ∧ z < a)

/-- A complete occupied interval from a support hole to the first destination hole. -/
structure Ray (s : State) (a b q : ℤ) : Prop where
  support : a ∈ s.holes
  destination : q ∈ s.holes
  adjacent : b = a + 1 ∨ b = a - 1
  intermediate : Between a q b
  occupied : ∀ z ∈ s.holes, ¬ Between a q z

private theorem Ray.fresh {s : State} {a b q : ℤ} (r : Ray s a b q) : b ∉ s.holes :=
  fun hb => r.occupied b hb r.intermediate

/-- Actual one-dimensional hole operations; transports recolour only their new adjacent hole. -/
inductive Step : State → State → Prop
  | eraseRed (s : State) (q : ℤ) (hq : q ∈ s.red) : Step s (s.eraseRed q)
  | eraseBlue (s : State) (q : ℤ) (hq : q ∈ s.blue) : Step s (s.eraseBlue q)
  | red (s : State) (a b q : ℤ) (ha : a ∈ s.red) (ray : Ray s a b q) :
      Step s (s.redTransport q b)
  | blue (s : State) (a b q : ℤ) (ha : a ∈ s.blue) (ray : Ray s a b q) :
      Step s (s.blueTransport q b)

/-- The low hole is red; the adjacent upper pair is blue. -/
def initial (L : ℤ) : State := ⟨{0}, {L - 1, L}, 0, 0⟩

/-- Extremal rank bounds plus the exact three-hole inventory, including deleted holes. -/
structure Invariant (L : ℤ) (s : State) : Prop where
  disjoint : Disjoint s.red s.blue
  total : s.red.card + s.blue.card + s.deletedRed + s.deletedBlue = 3
  red_bound : ∀ z ∈ s.red, z + 1 ≤ (s.red.card : ℤ) + s.deletedRed
  blue_bound : ∀ z ∈ s.blue, L + 1 ≤ z + (s.blue.card : ℤ) + s.deletedBlue

private theorem initial_invariant {L : ℤ} (hL : 7 ≤ L) : Invariant L (initial L) := by
  have hne : L - 1 ≠ L := by omega
  have hz : 0 ≠ L - 1 ∧ 0 ≠ L := by omega
  constructor
  · simp [initial, hz]
  · simp [initial, hne]
  · intro z hz
    simp only [initial, Finset.mem_singleton] at hz
    simp [initial, hz]
  · intro z hz
    simp only [initial, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> simp [initial, hne]; omega

private theorem Invariant.red_le_two {L : ℤ} {s : State} (h : Invariant L s)
    {z : ℤ} (hz : z ∈ s.red) : z ≤ 2 := by
  have := h.red_bound z hz
  have := h.total
  omega

private theorem Invariant.blue_ge {L : ℤ} {s : State} (h : Invariant L s)
    {z : ℤ} (hz : z ∈ s.blue) : L - 2 ≤ z := by
  have := h.blue_bound z hz
  have := h.total
  omega

private theorem Invariant.erase_red {L : ℤ} {s : State} (h : Invariant L s)
    {q : ℤ} (hq : q ∈ s.red) : Invariant L (s.eraseRed q) := by
  have hc := Finset.card_erase_add_one hq
  constructor
  · exact h.disjoint.mono (Finset.erase_subset _ _) (Finset.Subset.refl _)
  · simp only [State.eraseRed]
    have := h.total
    omega
  · intro z hz
    have hb := h.red_bound z (Finset.mem_of_mem_erase hz)
    simp only [State.eraseRed]
    omega
  · exact h.blue_bound

private theorem Invariant.erase_blue {L : ℤ} {s : State} (h : Invariant L s)
    {q : ℤ} (hq : q ∈ s.blue) : Invariant L (s.eraseBlue q) := by
  have hc := Finset.card_erase_add_one hq
  constructor
  · exact h.disjoint.mono (Finset.Subset.refl _) (Finset.erase_subset _ _)
  · simp only [State.eraseBlue]
    have := h.total
    omega
  · exact h.red_bound
  · intro z hz
    have hb := h.blue_bound z (Finset.mem_of_mem_erase hz)
    simp only [State.eraseBlue]
    omega

private theorem red_transport_disjoint {s : State} {q b : ℤ}
    (hd : Disjoint s.red s.blue) (hb : b ∉ s.holes) :
    Disjoint (s.redTransport q b).red (s.redTransport q b).blue := by
  apply Finset.disjoint_insert_left.mpr
  exact ⟨fun hm => hb (Finset.mem_union_right _ (Finset.mem_of_mem_erase hm)),
    hd.mono (Finset.erase_subset _ _) (Finset.erase_subset _ _)⟩

private theorem blue_transport_disjoint {s : State} {q b : ℤ}
    (hd : Disjoint s.red s.blue) (hb : b ∉ s.holes) :
    Disjoint (s.blueTransport q b).red (s.blueTransport q b).blue := by
  apply Finset.disjoint_insert_right.mpr
  exact ⟨fun hm => hb (Finset.mem_union_left _ (Finset.mem_of_mem_erase hm)),
    hd.mono (Finset.erase_subset _ _) (Finset.erase_subset _ _)⟩

private theorem Invariant.transport_red {L : ℤ} {s : State} (hL : 7 ≤ L)
    (h : Invariant L s) {a b q : ℤ} (ha : a ∈ s.red) (r : Ray s a b q) :
    Invariant L (s.redTransport q b) := by
  have hbR : b ∉ s.red := fun hb => r.fresh (Finset.mem_union_left _ hb)
  have hbB : b ∉ s.blue := fun hb => r.fresh (Finset.mem_union_right _ hb)
  have hba : b ∉ s.red.erase q := fun hb => hbR (Finset.mem_of_mem_erase hb)
  have hred := Finset.card_insert_of_notMem hba
  rcases Finset.mem_union.mp r.destination with hq | hq
  · have hqB : q ∉ s.blue := Finset.disjoint_left.mp h.disjoint hq
    have hblue := Finset.erase_eq_of_notMem hqB
    have hrc := Finset.card_erase_add_one hq
    have hc : (s.redTransport q b).red.card = s.red.card := by
      simp only [State.redTransport]
      omega
    constructor
    · exact red_transport_disjoint h.disjoint r.fresh
    · change (s.redTransport q b).red.card + (s.blue.erase q).card +
        s.deletedRed + s.deletedBlue = 3
      rw [hc, hblue]
      exact h.total
    · intro z hz
      simp only [State.redTransport, Finset.mem_insert] at hz
      rw [hc]
      change z + 1 ≤ (s.red.card : ℤ) + s.deletedRed
      rcases hz with rfl | hz
      · have ha' := h.red_bound a ha
        have hq' := h.red_bound q hq
        rcases r.intermediate with ⟨_, hbq⟩ | ⟨_, hba⟩ <;> omega
      · exact h.red_bound z (Finset.mem_of_mem_erase hz)
    · simpa only [State.redTransport, hblue] using h.blue_bound
  · have hqR : q ∉ s.red := Finset.disjoint_right.mp h.disjoint hq
    have hrr := Finset.erase_eq_of_notMem hqR
    have hbc := Finset.card_erase_add_one hq
    have hc : (s.redTransport q b).red.card = s.red.card + 1 := by
      simpa only [State.redTransport, hrr] using hred
    constructor
    · exact red_transport_disjoint h.disjoint r.fresh
    · change (s.redTransport q b).red.card + (s.blue.erase q).card +
        s.deletedRed + s.deletedBlue = 3
      rw [hc]
      have := h.total
      omega
    · intro z hz
      simp only [State.redTransport, Finset.mem_insert] at hz
      rw [hc]
      change z + 1 ≤ ((s.red.card + 1 : ℕ) : ℤ) + s.deletedRed
      rcases hz with rfl | hz
      · have ha' := h.red_bound a ha
        rcases r.adjacent with rfl | rfl <;> omega
      · have := h.red_bound z (Finset.mem_of_mem_erase hz)
        omega
    · intro z hz
      have hz' := (Finset.mem_erase.mp hz).1
      have hzB := Finset.mem_of_mem_erase hz
      have haz : a < z := by have := h.red_le_two ha; have := h.blue_ge hzB; omega
      have haq : a < q := by have := h.red_le_two ha; have := h.blue_ge hq; omega
      have hqz : q < z := by
        by_contra hn
        exact r.occupied z (Finset.mem_union_right _ hzB) (Or.inl ⟨haz, by omega⟩)
      have := h.blue_bound q hq
      simp only [State.redTransport]
      omega

private theorem Invariant.transport_blue {L : ℤ} {s : State} (hL : 7 ≤ L)
    (h : Invariant L s) {a b q : ℤ} (ha : a ∈ s.blue) (r : Ray s a b q) :
    Invariant L (s.blueTransport q b) := by
  have hbR : b ∉ s.red := fun hb => r.fresh (Finset.mem_union_left _ hb)
  have hbB : b ∉ s.blue := fun hb => r.fresh (Finset.mem_union_right _ hb)
  have hba : b ∉ s.blue.erase q := fun hb => hbB (Finset.mem_of_mem_erase hb)
  have hblue := Finset.card_insert_of_notMem hba
  rcases Finset.mem_union.mp r.destination with hq | hq
  · have hqB : q ∉ s.blue := Finset.disjoint_left.mp h.disjoint hq
    have hbb := Finset.erase_eq_of_notMem hqB
    have hrc := Finset.card_erase_add_one hq
    have hc : (s.blueTransport q b).blue.card = s.blue.card + 1 := by
      simpa only [State.blueTransport, hbb] using hblue
    constructor
    · exact blue_transport_disjoint h.disjoint r.fresh
    · change (s.red.erase q).card + (s.blueTransport q b).blue.card +
        s.deletedRed + s.deletedBlue = 3
      rw [hc]
      have := h.total
      omega
    · intro z hz
      have hz' := (Finset.mem_erase.mp hz).1
      have hzR := Finset.mem_of_mem_erase hz
      have hza : z < a := by have := h.red_le_two hzR; have := h.blue_ge ha; omega
      have hqa : q < a := by have := h.red_le_two hq; have := h.blue_ge ha; omega
      have hzq : z < q := by
        by_contra hn
        exact r.occupied z (Finset.mem_union_left _ hzR) (Or.inr ⟨by omega, hza⟩)
      have := h.red_bound q hq
      simp only [State.blueTransport]
      omega
    · intro z hz
      simp only [State.blueTransport, Finset.mem_insert] at hz
      rw [hc]
      change L + 1 ≤ z + ((s.blue.card + 1 : ℕ) : ℤ) + s.deletedBlue
      rcases hz with rfl | hz
      · have ha' := h.blue_bound a ha
        rcases r.adjacent with rfl | rfl <;> omega
      · have := h.blue_bound z (Finset.mem_of_mem_erase hz)
        omega
  · have hqR : q ∉ s.red := Finset.disjoint_right.mp h.disjoint hq
    have hred := Finset.erase_eq_of_notMem hqR
    have hbc := Finset.card_erase_add_one hq
    have hc : (s.blueTransport q b).blue.card = s.blue.card := by
      simp only [State.blueTransport]
      omega
    constructor
    · exact blue_transport_disjoint h.disjoint r.fresh
    · change (s.red.erase q).card + (s.blueTransport q b).blue.card +
        s.deletedRed + s.deletedBlue = 3
      rw [hc, hred]
      exact h.total
    · simpa only [State.blueTransport, hred] using h.red_bound
    · intro z hz
      simp only [State.blueTransport, Finset.mem_insert] at hz
      rw [hc]
      change L + 1 ≤ z + (s.blue.card : ℤ) + s.deletedBlue
      rcases hz with rfl | hz
      · have ha' := h.blue_bound a ha
        have hq' := h.blue_bound q hq
        rcases r.intermediate with ⟨hab, _⟩ | ⟨hqb, _⟩ <;> omega
      · exact h.blue_bound z (Finset.mem_of_mem_erase hz)

/-- The extremal bounds are derived from the exact transport/delete dynamics. -/
private theorem reachable_invariant {L : ℤ} {s : State} (hL : 7 ≤ L)
    (hr : Relation.ReflTransGen Step (initial L) s) : Invariant L s := by
  induction hr with
  | refl => exact initial_invariant hL
  | tail _ hm ih =>
    cases hm with
    | eraseRed _ hq => exact ih.erase_red hq
    | eraseBlue _ hq => exact ih.erase_blue hq
    | red _ _ _ ha ray => exact ih.transport_red hL ha ray
    | blue _ _ _ ha ray => exact ih.transport_blue hL ha ray

/-- Landing at coordinate two forces both original blue holes to have been recoloured. -/
private theorem landing_seals {L : ℤ} {s : State} (hL : 7 ≤ L)
    (hr : Relation.ReflTransGen Step (initial L) s) (hland : 2 ∈ s.holes) :
    s.blue = ∅ ∧ s.deletedBlue = 0 ∧ L ∉ s.holes := by
  have hi := reachable_invariant hL hr
  have hr2 : 2 ∈ s.red := by
    rcases Finset.mem_union.mp hland with hh | hh
    · exact hh
    · have := hi.blue_ge hh
      omega
  have hb := hi.red_bound 2 hr2
  have ht := hi.total
  have hb0 : s.blue.card = 0 := by omega
  have hd0 : s.deletedBlue = 0 := by omega
  refine ⟨Finset.card_eq_zero.mp hb0, hd0, ?_⟩
  intro hhole
  rcases Finset.mem_union.mp hhole with hh | hh
  · have := hi.red_le_two hh
    omega
  · simp [Finset.card_eq_zero.mp hb0] at hh

/-- The corresponding operations on the ordinary unlabelled hole set. -/
inductive HoleStep : Finset ℤ → Finset ℤ → Prop
  | erase (E : Finset ℤ) (q : ℤ) (hq : q ∈ E) : HoleStep E (E.erase q)
  | transport (E : Finset ℤ) (a b q : ℤ) (support : a ∈ E) (destination : q ∈ E)
      (adjacent : b = a + 1 ∨ b = a - 1) (intermediate : Between a q b)
      (occupied : ∀ z ∈ E, ¬ Between a q z) : HoleStep E (insert b (E.erase q))

private theorem lift_holeStep {L : ℤ} {s : State} {E : Finset ℤ}
    (hi : Invariant L s) (hm : HoleStep s.holes E) :
    ∃ t, Step s t ∧ t.holes = E := by
  cases hm with
  | erase q hq =>
    rcases Finset.mem_union.mp hq with hq | hq
    · refine ⟨s.eraseRed q, .eraseRed s q hq, ?_⟩
      have hqB : q ∉ s.blue := Finset.disjoint_left.mp hi.disjoint hq
      ext z
      simp only [State.holes, State.eraseRed, Finset.mem_union, Finset.mem_erase]
      by_cases hz : z = q <;> simp_all
    · refine ⟨s.eraseBlue q, .eraseBlue s q hq, ?_⟩
      have hqR : q ∉ s.red := Finset.disjoint_right.mp hi.disjoint hq
      ext z
      simp only [State.holes, State.eraseBlue, Finset.mem_union, Finset.mem_erase]
      by_cases hz : z = q <;> simp_all
  | transport a b q ha hq hadj hmid hclear =>
    have ray : Ray s a b q := ⟨ha, hq, hadj, hmid, hclear⟩
    rcases Finset.mem_union.mp ha with ha | ha
    · refine ⟨s.redTransport q b, .red s a b q ha ray, ?_⟩
      ext z
      simp only [State.holes, State.redTransport, Finset.mem_union,
        Finset.mem_insert, Finset.mem_erase]
      tauto
    · refine ⟨s.blueTransport q b, .blue s a b q ha ray, ?_⟩
      ext z
      simp only [State.holes, State.blueTransport, Finset.mem_union,
        Finset.mem_insert, Finset.mem_erase]
      tauto

/-- Ordinary one-dimensional trajectories lift by colouring each newly opened hole at its support. -/
private theorem lift_reachable {L : ℤ} {E : Finset ℤ} (hL : 7 ≤ L)
    (hr : Relation.ReflTransGen HoleStep (initial L).holes E) :
    ∃ s, Relation.ReflTransGen Step (initial L) s ∧ s.holes = E := by
  induction hr with
  | refl => exact ⟨initial L, .refl, rfl⟩
  | tail _ hm ih =>
    obtain ⟨s, hs, hE⟩ := ih
    obtain ⟨t, ht, htE⟩ := lift_holeStep (reachable_invariant hL hs) (hE.symm ▸ hm)
    exact ⟨t, hs.tail ht, htE⟩

/-- The seal closes at its upper endpoint whenever its ordinary hole dynamics reach the landing. -/
theorem uncoloured_landing_seals {L : ℤ} {E : Finset ℤ} (hL : 7 ≤ L)
    (hr : Relation.ReflTransGen HoleStep ({0, L - 1, L} : Finset ℤ) E) (hland : 2 ∈ E) :
    L ∉ E := by
  have hi : (initial L).holes = ({0, L - 1, L} : Finset ℤ) := by
    ext z
    simp only [initial, State.holes, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  obtain ⟨s, hs, he⟩ := lift_reachable hL (hi.symm ▸ hr)
  rw [← he] at hland ⊢
  exact (landing_seals hL hs hland).2.2

end PushPuzzle.Push.Seal
