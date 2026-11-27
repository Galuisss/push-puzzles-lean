/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.ReadFootprint

/-! Exact whole-component reads of one source column. -/

@[expose] public section
namespace PushPuzzle.PushPush.Reader

open PushFS (Cell State Adjacent)

variable {w h : ℕ}

/-- Delete a southern prefix of source holes, ending between consecutive hole runs. -/
structure ExactNorthRead (E F : Finset (Cell w h)) : Prop where
  /-- The read only deletes holes. -/
  subset : F ⊆ E
  /-- Every deleted hole lies strictly south of every retained hole. -/
  front : ∀ p ∈ E \ F, ∀ q ∈ F, q.2.val < p.2.val
  /-- The cut never divides two consecutive source holes. -/
  no_split : ∀ p ∈ E \ F, ∀ q ∈ F, ¬ Adjacent .north p q

theorem ExactNorthRead.refl (E : Finset (Cell w h)) : ExactNorthRead E E where
  subset := fun _ hp => hp
  front := by simp
  no_split := by simp

theorem ExactNorthRead.trans {E F G : Finset (Cell w h)} (hEF : ExactNorthRead E F)
    (hFG : ExactNorthRead F G) : ExactNorthRead E G where
  subset := hFG.subset.trans hEF.subset
  front := by
    intro p hp q hq
    obtain ⟨hpE, hpG⟩ := Finset.mem_sdiff.mp hp
    by_cases hpF : p ∈ F
    · exact hFG.front p (Finset.mem_sdiff.mpr ⟨hpF, hpG⟩) q hq
    · exact hEF.front p (Finset.mem_sdiff.mpr ⟨hpE, hpF⟩) q (hFG.subset hq)
  no_split := by
    intro p hp q hq ha
    obtain ⟨hpE, hpG⟩ := Finset.mem_sdiff.mp hp
    by_cases hpF : p ∈ F
    · exact hFG.no_split p (Finset.mem_sdiff.mpr ⟨hpF, hpG⟩) q hq ha
    · exact hEF.no_split p (Finset.mem_sdiff.mpr ⟨hpE, hpF⟩) q (hFG.subset hq) ha

private theorem ExactNorthRead.gap_subset {s : State w h} {cutoff : ℕ} {F : Finset (Cell w h)}
    (H : ExactNorthRead (northData s cutoff) F)
    (hne : (northData s cutoff \ F).Nonempty) (R : NorthRun s cutoff)
    (hspace : cutoff + (northData s cutoff).card < s.player.2.val)
    (hgap : ∀ q : Cell w h, q.1 = s.player.1 → cutoff ≤ q.2.val →
      q.2.val < s.player.2.val → q ∈ s.boxes) :
    (R.toSlide hspace hgap).gap ⊆ northData s cutoff \ F := by
  let r := R.toSlide hspace hgap
  have hlen : R.length = R.bottom.2.val - R.top.2.val + 1 := rfl
  have hbottom : R.bottom ∈ northData s cutoff \ F := by
    apply Finset.mem_sdiff.mpr
    refine ⟨R.bottom_mem, ?_⟩
    intro hb
    obtain ⟨p, hp⟩ := hne
    have hpE := (Finset.mem_sdiff.mp hp).1
    have := H.front p hp R.bottom hb
    have := R.nearest p hpE
    omega
  have hi (i : Fin R.length) : r.cell ⟨R.train + i.val + 1, by omega⟩ ∈ northData s cutoff \ F := by
    induction i using Fin.induction with
    | zero =>
      change r.cell ⟨R.train + 1, by have := R.length_pos; omega⟩ ∈ _
      rw [show r.cell ⟨R.train + 1, by have := R.length_pos; omega⟩ = R.bottom from
        R.gap_bottom hspace hgap]
      exact hbottom
    | succ i ih =>
      have he : r.cell ⟨R.train + (i.val + 1) + 1, by have := i.isLt; omega⟩ ∈ northData s cutoff := by
        apply R.gap_subset hspace hgap
        exact Finset.mem_image.mpr ⟨i.succ, Finset.mem_univ _, rfl⟩
      apply Finset.mem_sdiff.mpr
      refine ⟨he, ?_⟩
      intro hf
      apply H.no_split _ ih _ hf
      exact r.adjacent ⟨R.train + i.val + 1, by have := i.isLt; omega⟩
  intro p hp
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  exact hi i

private theorem ExactNorthRead.remove {E F G : Finset (Cell w h)} (H : ExactNorthRead E F)
    (hG : G ⊆ E \ F) : ExactNorthRead (E \ G) F where
  subset := by
    intro p hp
    apply Finset.mem_sdiff.mpr
    refine ⟨H.subset hp, ?_⟩
    intro hg
    exact (Finset.mem_sdiff.mp (hG hg)).2 hp
  front := by
    intro p hp q hq
    have hp := Finset.mem_sdiff.mp hp
    exact H.front p (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hp.1).1, hp.2⟩) q hq
  no_split := by
    intro p hp q hq
    have hp := Finset.mem_sdiff.mp hp
    exact H.no_split p (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hp.1).1, hp.2⟩) q hq

/-- Every exact whole-run source read has a genuine maximum-sliding execution. -/
theorem read_north_exact_path (q : ℕ) (s : State w h) (cutoff : ℕ) (F : Finset (Cell w h))
    (H : ExactNorthRead (northData s cutoff) F)
    (hq : q = (northData s cutoff \ F).card) (hv : s.player ∉ s.boxes)
    (hspace : cutoff + (northData s cutoff).card < s.player.2.val)
    (hgap : ∀ p : Cell w h, p.1 = s.player.1 → cutoff ≤ p.2.val →
      p.2.val < s.player.2.val → p ∈ s.boxes) :
    ∃ t : State w h, ReadPath s t ∧ t.player.1 = s.player.1 ∧
      t.player.2.val + q = s.player.2.val ∧ northData t cutoff = F ∧
      (∀ p : Cell w h, p.1 ≠ s.player.1 → (p ∈ t.boxes ↔ p ∈ s.boxes)) ∧
      t.boxesᶜ = (s.boxesᶜ \ (northData s cutoff \ F)) ∪ northTrail s q := by
  induction q using Nat.strong_induction_on generalizing s with
  | ind q ih =>
    by_cases hz : q = 0
    · have hEF : northData s cutoff = F := by
        apply Finset.Subset.antisymm _ H.subset
        intro p hp
        by_contra hn
        have hc := Finset.card_pos.mpr ⟨p, Finset.mem_sdiff.mpr ⟨hp, hn⟩⟩
        omega
      exact ⟨s, .refl, rfl, by omega, hEF, (fun _ _ => Iff.rfl), by simp [hz, hEF]⟩
    · have hne : (northData s cutoff \ F).Nonempty := Finset.card_pos.mp (by omega)
      have hdata : (northData s cutoff).Nonempty :=
        hne.mono (Finset.sdiff_subset)
      obtain ⟨R⟩ := exists_northRun s cutoff hdata
      have hs : cutoff + (northData s cutoff).card < s.player.2.val := by omega
      let g := (R.toSlide hs hgap).gap
      let u := R.target hs hgap
      have hg : g ⊆ northData s cutoff \ F := H.gap_subset hne R hs hgap
      have hk : 0 < R.length := R.length_pos
      have hkg : g.card = R.length := Slide.gap_card _
      have hkq : R.length ≤ q := by
        have hc := Finset.card_le_card hg
        rw [hkg, ← hq] at hc
        exact hc
      have hu : northData u cutoff = northData s cutoff \ g := R.target_data hs hgap hv
      have hread : ExactNorthRead (northData u cutoff) F := by
        rw [hu]
        exact H.remove hg
      have hquot : q - R.length = (northData u cutoff \ F).card := by
        rw [hu]
        have he : (northData s cutoff \ g) \ F = (northData s cutoff \ F) \ g := by
          ext p
          simp only [Finset.mem_sdiff]
          tauto
        rw [he, Finset.card_sdiff_of_subset hg, hkg, ← hq]
      have hr : ReadPath s u := R.target_readPath hs hgap hv
      have hux : u.player.1 = s.player.1 := R.target_column hs hgap
      have huy : u.player.2.val + R.length = s.player.2.val := R.target_row hs hgap
      have huc : (northData u cutoff).card + R.length = (northData s cutoff).card :=
        R.target_data_card hs hgap hv
      obtain ⟨t, ht, htx, hty, htf, hframe, hholes⟩ := ih (q - R.length) (by omega) u hread hquot
        (hr.valid hv) (by omega) (R.target_gap hs hgap hv)
      refine ⟨t, hr.trans ht, htx.trans hux, by omega, htf, ?_, ?_⟩
      · intro p hp
        exact (hframe p (by rwa [hux])).trans (R.target_off_column hs hgap hp)
      · have hdis : Disjoint (northTrail s R.length) (northData s cutoff \ F) := by
          apply Finset.disjoint_left.mpr
          intro p hp hD
          have hlo := (Finset.mem_filter.mp hp).2.2.1
          have hhi := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hD).1).2.2
          omega
        have he : northData u cutoff \ F = (northData s cutoff \ F) \ g := by
          rw [hu]
          ext p
          simp only [Finset.mem_sdiff]
          tauto
        rw [hholes, R.target_holes hs hgap hv, he,
          erase_source_runs _ _ g _ hg hdis, Finset.union_assoc,
          northTrail_append s u R.length (q - R.length) hux huy,
          Nat.add_sub_of_le hkq]

end PushPuzzle.PushPush.Reader
