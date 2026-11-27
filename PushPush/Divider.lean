/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.RackFrozen

/-! An isolated divider immediately west of a frozen rack is preserved backwards. -/

@[expose] public section
namespace PushPuzzle.PushPush

open PushFS (Cell Direction Adjacent State)

variable {w h n k P : ℕ} {d : Direction} {s t u : State w h}

namespace Slide

/-- Adjacent occupied cells along the pushing line belong to the same complete run. -/
theorem before_adjacent (r : Slide d s n k) (hk : 0 < k) (hv : s.player ∉ s.boxes)
    {p q : Cell w h} (hp : p ∈ r.before) (hq : q ∈ s.boxes)
    (ha : Adjacent d p q ∨ Adjacent d q p) : q ∈ r.before := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  rcases ha with ha | ha
  · by_cases hi : i.val + 1 < n
    · have he : q = r.cell ⟨i.val + 2, by omega⟩ := by
        apply d.cell_ext
        · exact ha.lane.trans ((r.lane _).trans (r.lane _).symm)
        · have hp := ha.position
          have h1 := r.position ⟨i.val + 1, by omega⟩
          have h2 := r.position ⟨i.val + 2, by omega⟩
          dsimp only at h1 h2
          omega
      exact Finset.mem_image.mpr ⟨⟨i.val + 1, hi⟩, Finset.mem_univ _, by rw [he]⟩
    · have he : q = r.cell ⟨n + 1, by omega⟩ := by
        apply d.cell_ext
        · exact ha.lane.trans ((r.lane _).trans (r.lane _).symm)
        · have hp := ha.position
          have h1 := r.position ⟨i.val + 1, by omega⟩
          have h2 := r.position ⟨n + 1, by omega⟩
          dsimp only at h1 h2
          omega
      exact False.elim (r.clear ⟨0, hk⟩ (by simpa only [Nat.add_zero, ← he] using hq))
  · by_cases hi : i.val = 0
    · have he : q = s.player := by
        apply d.cell_ext
        · exact ha.lane.symm.trans (r.lane _)
        · have hp := ha.position
          have h1 := r.position ⟨i.val + 1, by omega⟩
          dsimp only at h1
          omega
      exact False.elim (hv (he ▸ hq))
    · have he : q = r.cell ⟨i.val, by omega⟩ := by
        apply d.cell_ext
        · exact ha.lane.symm.trans ((r.lane _).trans (r.lane _).symm)
        · have hp := ha.position
          have h1 := r.position ⟨i.val + 1, by omega⟩
          have h2 := r.position ⟨i.val, by omega⟩
          dsimp only at h1 h2
          omega
      exact Finset.mem_image.mpr ⟨⟨i.val - 1, by omega⟩, Finset.mem_univ _, by
        rw [he]
        congr 1
        apply Fin.ext
        change i.val - 1 + 1 = i.val
        omega⟩

/-- A moved box is joined to another box on the forward side of its final component. -/
theorem after_neighbor (r : Slide d s n k) (hn : 0 < n)
    (ht : ∀ p ∈ r.boxes, ¬ Boundary p) {p : Cell w h} (hp : p ∈ r.after) :
    ∃ q ∈ r.boxes, Adjacent d p q := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  by_cases hi : i.val + 1 < n
  · refine ⟨r.cell ⟨k + i.val + 2, by omega⟩, ?_, ?_⟩
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨⟨i.val + 1, hi⟩, Finset.mem_univ _, by congr 1⟩)
    · exact r.adjacent ⟨k + i.val + 1, by omega⟩
  · obtain ⟨q, hq, ha⟩ := r.exists_stopper hn ht
    have he : (⟨k + i.val + 1, by omega⟩ : Fin (n + k + 1)) =
        ⟨n + k, by omega⟩ := Fin.ext (by change k + i.val + 1 = n + k; omega)
    refine ⟨q, Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hq, ?_⟩), by rwa [he]⟩
    intro hqbefore
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hqbefore
    have hp := ha.position
    have h1 := r.position ⟨n + k, by omega⟩
    have h2 := r.position ⟨j.val + 1, by omega⟩
    rw [hj] at h2
    dsimp only at h1 h2
    omega

/-- An original box on the finite swept ray belongs to its occupied prefix. -/
theorem before_of_between (r : Slide d s n k) {q : Cell w h} (hq : q ∈ s.boxes)
    (hl : d.lane q = d.lane s.player) (hlo : d.position s.player < d.position q)
    (hhi : d.position q ≤ d.position s.player + n + k) : q ∈ r.before := by
  let j : ℕ := (d.position q - d.position s.player - 1).toNat
  have hj : j < n + k := by dsimp only [j]; omega
  have he : r.cell ⟨j + 1, by omega⟩ = q := by
    apply d.cell_ext ((r.lane _).trans hl.symm)
    rw [r.position]
    dsimp only [j]
    omega
  by_cases hjn : j < n
  · exact Finset.mem_image.mpr ⟨⟨j, hjn⟩, Finset.mem_univ _, he⟩
  · have hje : (⟨n + (j - n) + 1, by omega⟩ : Fin (n + k + 1)) =
        ⟨j + 1, by omega⟩ := Fin.ext (by change n + (j - n) + 1 = j + 1; omega)
    exact False.elim (r.clear ⟨j - n, by omega⟩ (by rw [hje, he]; exact hq))

theorem horizontal_before_not_rack (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hd : d = .east ∨ d = .west) (hs : Supported .east P s)
    (ht : ∀ p ∈ r.boxes, ¬ Boundary p)
    (hrack : line .south P r.boxes = line .south P s.boxes)
    {p : Cell w h} (hp : p ∈ r.before) : p.1.val ≠ P := by
  intro hx
  have hsrc : Direction.south.position p ∈ line .south P s.boxes :=
    mem_line.mpr ⟨p, r.before_subset hp, hx, rfl⟩
  rw [← hrack, r.horizontal_column hn hk hd hs ht] at hsrc
  exact (Finset.mem_sdiff.mp hsrc).2 (mem_line.mpr ⟨p, hp, hx, rfl⟩)

/-- A rack hole prevents every horizontal slide from depositing immediately to its west. -/
theorem horizontal_after_not_divider (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hd : d = .east ∨ d = .west) (hs : Supported .east P s)
    (ht : ∀ p ∈ r.boxes, ¬ Boundary p) {p e : Cell w h}
    (he : Adjacent .east p e) (hx : e.1.val = P) (hemp : e ∉ s.boxes) : p ∉ r.after := by
  intro hp
  obtain ⟨i, _, hpi⟩ := Finset.mem_image.mp hp
  have hpcoord := r.position ⟨k + i.val + 1, by omega⟩
  have hplane := r.lane ⟨k + i.val + 1, by omega⟩
  rw [hpi] at hpcoord hplane
  have hex := he.position
  have hey := he.lane
  rcases hd with rfl | rfl
  · obtain ⟨q, hq, hqa⟩ := r.exists_stopper hn ht
    have hqs := hs q hq
    have hqp := hqa.position
    have hql := hqa.lane
    have hlast := r.position ⟨n + k, by omega⟩
    have hlastl := r.lane ⟨n + k, by omega⟩
    simp only [Direction.position, Direction.lane] at hpcoord hplane hex hey hqs hqp hql hlast hlastl
    have hqe : q = e := by
      apply Prod.ext <;> apply Fin.ext <;> omega
    exact hemp (hqe ▸ hq)
  · have hq := r.occupied i
    have hqs := hs _ hq
    have hqp := r.position ⟨i.val + 1, by omega⟩
    have hql := r.lane ⟨i.val + 1, by omega⟩
    simp only [Direction.position, Direction.lane] at hpcoord hplane hex hey hqs hqp hql
    have hqe : r.cell ⟨i.val + 1, by omega⟩ = e := by
      apply Prod.ext <;> apply Fin.ext <;> omega
    exact hemp (hqe ▸ hq)

end Slide

/-- One occupied divider cell with both vertical neighbors empty. -/
def VerticallyIsolated (s : State w h) (p : Cell w h) : Prop :=
  p ∈ s.boxes ∧ ∀ q, Adjacent .north p q ∨ Adjacent .south p q → q ∉ s.boxes

/-- The rack is hollow opposite the divider and full opposite its vertical neighbors. -/
structure DividerGuard (P : ℕ) (s : State w h) (p : Cell w h) : Prop where
  /-- The rack hole directly east of the divider. -/
  hole : ∃ e, Adjacent .east p e ∧ e.1.val = P ∧ e ∉ s.boxes
  /-- The rack supports both neighboring rows. -/
  beside : ∀ q, Adjacent .north p q ∨ Adjacent .south p q →
    ∃ e, Adjacent .east q e ∧ e.1.val = P ∧ e ∈ s.boxes

theorem rack_mem_iff {p : Cell w h} (hp : p.1.val = P)
    (he : line .south P t.boxes = line .south P s.boxes) :
    p ∈ t.boxes ↔ p ∈ s.boxes := by
  have hmem (B : Finset (Cell w h)) :
      p ∈ B ↔ Direction.south.position p ∈ line .south P B := by
    constructor
    · intro hb
      exact mem_line.mpr ⟨p, hb, hp, rfl⟩
    · intro hb
      obtain ⟨q, hq, hl, hz⟩ := mem_line.mp hb
      have hqp : q = p := Direction.south.cell_ext (hl.trans hp.symm) hz
      exact hqp ▸ hq
  rw [hmem t.boxes, hmem s.boxes, he]

theorem DividerGuard.congr {p : Cell w h} (hg : DividerGuard P s p)
    (hrack : line .south P t.boxes = line .south P s.boxes) : DividerGuard P t p := by
  constructor
  · obtain ⟨e, he, hx, hee⟩ := hg.hole
    exact ⟨e, he, hx, fun ht => hee ((rack_mem_iff hx hrack).mp ht)⟩
  · intro q hq
    obtain ⟨e, he, hx, heb⟩ := hg.beside q hq
    exact ⟨e, he, hx, (rack_mem_iff hx hrack).mpr heb⟩

theorem Move.divider_isolated_source (hm : Move d s t) (hs : Supported .east P s)
    (ht : Interior t) (hrack : line .south P t.boxes = line .south P s.boxes)
    {p : Cell w h} (hg : DividerGuard P s p) (hp : VerticallyIsolated t p) :
    VerticallyIsolated s p := by
  cases hm with
  | walk _ _ _ hb => simpa only [VerticallyIsolated, hb] using hp
  | push hv hn hk r _ hb =>
    have hti : ∀ q ∈ r.boxes, ¬ Boundary q := by simpa only [Interior, hb] using ht
    have hp' : VerticallyIsolated (State.mk t.player r.boxes) p := by
      simpa only [VerticallyIsolated, hb] using hp
    have hpa : p ∉ r.after := by
      by_cases hd : d = .east ∨ d = .west
      · obtain ⟨e, he, hx, hem⟩ := hg.hole
        exact r.horizontal_after_not_divider hn hk hd hs hti he hx hem
      · intro hpa
        obtain ⟨q, hq, ha⟩ := r.after_neighbor hn hti hpa
        have hd : Adjacent .north p q ∨ Adjacent .south p q := by
          cases d <;> simp_all
        exact hp'.2 q hd hq
    have hps : p ∈ s.boxes ∧ p ∉ r.before :=
      Finset.mem_sdiff.mp ((Finset.mem_union.mp hp'.1).resolve_right hpa)
    refine ⟨hps.1, ?_⟩
    intro q hq hqb
    have hqbefore : q ∉ r.before := by
      intro hqb'
      by_cases hd : d = .east ∨ d = .west
      · obtain ⟨e, he, hx, heb⟩ := hg.beside q hq
        have hea : Adjacent d q e ∨ Adjacent d e q := by
          rcases hd with rfl | rfl
          · exact Or.inl he
          · exact Or.inr he.reverse
        have hebefore := r.before_adjacent hk hv hqb' heb hea
        exact r.horizontal_before_not_rack hn hk hd hs hti (by simpa only [hb] using hrack)
          hebefore hx
      · have hdv : d = .north ∨ d = .south := by cases d <;> simp_all
        have hpa : Adjacent d q p ∨ Adjacent d p q := by
          rcases hdv with rfl | rfl
          · rcases hq with hq | hq
            · exact Or.inr hq
            · exact Or.inl hq.reverse
          · rcases hq with hq | hq
            · exact Or.inl hq.reverse
            · exact Or.inr hq
        exact hps.2 (r.before_adjacent hk hv hqb' hps.1 hpa)
    exact hp'.2 q hq (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hqb, hqbefore⟩))

/-- The final isolated divider shape holds at the start of every successful trajectory. -/
private theorem Reachable.divider_isolated_source (hr : Reachable s t) (hs : Supported .east P s)
    (ht : Interior t) (hrack : line .south P t.boxes = line .south P s.boxes)
    {p : Cell w h} (hg : DividerGuard P s p) (hp : VerticallyIsolated t p) :
    VerticallyIsolated s p := by
  induction hr with
  | refl => exact hp
  | @tail v t hr hm ih =>
    have hv := hm.choose_spec.interior_source ht
    have hvrack := Reachable.rack_frozen hr (Relation.ReflTransGen.single hm) hs ht hrack
    have hvg := hg.congr hvrack
    have hvp := hm.choose_spec.divider_isolated_source (Reachable.supported hr hv hs) ht
      (hrack.trans hvrack.symm) hvg hp
    exact ih hv hvrack hvp

/-- A restored rack and final isolated divider fix the divider and both neighboring holes
at every intermediate state. -/
theorem Reachable.divider_frozen (hprefix : Reachable s u) (hsuffix : Reachable u t)
    (hs : Supported .east P s) (ht : Interior t)
    (hrack : line .south P t.boxes = line .south P s.boxes)
    {p : Cell w h} (hg : DividerGuard P s p) (hp : VerticallyIsolated t p) :
    VerticallyIsolated u p := by
  have hu := hsuffix.interior_source ht
  have hurack := hprefix.rack_frozen hsuffix hs ht hrack
  exact hsuffix.divider_isolated_source (hprefix.supported hu hs) ht
    (hrack.trans hurack.symm) (hg.congr hurack) hp

end PushPuzzle.PushPush
