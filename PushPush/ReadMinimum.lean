/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.ReadExact

/-! A read quota is paid by complete maximum slides, with possible last-run overpayment. -/

@[expose] public section
namespace PushPuzzle.PushPush.Reader

open PushFS (Cell State Direction)

variable {w h : ℕ}

private theorem NorthRun.first_read {s : State w h} {cutoff : ℕ} (R : NorthRun s cutoff)
    (hspace : cutoff + (northData s cutoff).card < s.player.2.val)
    (hgap : ∀ q : Cell w h, q.1 = s.player.1 → cutoff ≤ q.2.val →
      q.2.val < s.player.2.val → q ∈ s.boxes) :
    ExactNorthRead (northData s cutoff) (northData s cutoff \ (R.toSlide hspace hgap).gap) := by
  refine ⟨Finset.sdiff_subset, ?_, ?_⟩
  · intro p hp q hq
    obtain ⟨hpE, hnot⟩ := Finset.mem_sdiff.mp hp
    have hpg : p ∈ (R.toSlide hspace hgap).gap := by
      by_contra hn
      exact hnot (Finset.mem_sdiff.mpr ⟨hpE, hn⟩)
    obtain ⟨_, hpl, _⟩ := (R.mem_gap hspace hgap p).mp hpg
    obtain ⟨hqE, hqnot⟩ := Finset.mem_sdiff.mp hq
    have hqx := (Finset.mem_filter.mp hqE).2.1
    have hqb := R.nearest q hqE
    have hqt : q.2.val < R.top.2.val := by
      by_contra hn
      exact hqnot ((R.mem_gap hspace hgap q).mpr ⟨hqx, by omega, hqb⟩)
    omega
  · intro p hp q hq ha
    obtain ⟨hpE, hnot⟩ := Finset.mem_sdiff.mp hp
    have hpg : p ∈ (R.toSlide hspace hgap).gap := by
      by_contra hn
      exact hnot (Finset.mem_sdiff.mpr ⟨hpE, hn⟩)
    obtain ⟨hqE, hqnot⟩ := Finset.mem_sdiff.mp hq
    exact hqnot ((R.toSlide hspace hgap).gap_closed (R.train_pos hspace) hpg
      (Finset.mem_compl.mp (Finset.mem_filter.mp hqE).1) (Or.inl ha))

/-- Reading enough source holes is possible even when the last whole run overpays the quota. -/
theorem read_north_at_least (q : ℕ) (s : State w h) (cutoff : ℕ)
    (hv : s.player ∉ s.boxes) (hcount : q ≤ (northData s cutoff).card)
    (hspace : cutoff + q + (northData s cutoff).card < s.player.2.val)
    (hgap : ∀ p : Cell w h, p.1 = s.player.1 → cutoff ≤ p.2.val →
      p.2.val < s.player.2.val → p ∈ s.boxes) :
    ∃ t : State w h, Reachable s t ∧ t.player.1 = s.player.1 ∧
      t.player.2.val + q = s.player.2.val ∧ ExactNorthRead (northData s cutoff) (northData t cutoff) ∧
      q ≤ (northData s cutoff \ northData t cutoff).card ∧
      ∀ p : Cell w h, p.1 ≠ s.player.1 → (p ∈ t.boxes ↔ p ∈ s.boxes) := by
  induction q using Nat.strong_induction_on generalizing s with
  | ind q ih =>
    by_cases hz : q = 0
    · exact ⟨s, .refl, rfl, by omega, .refl _, by simp [hz], fun _ _ => Iff.rfl⟩
    · have hne : (northData s cutoff).Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨R⟩ := exists_northRun s cutoff hne
      have hs : cutoff + (northData s cutoff).card < s.player.2.val := by omega
      let ray := R.toSlide hs hgap
      have hn := R.train_pos hs
      have hk := R.length_pos
      by_cases hqk : q ≤ R.length
      · let i : Fin (R.length + 1) := ⟨q, by omega⟩
        let t := ray.returnState i
        have hr : Reachable s t := ray.advance_reachable hn hk hv i (by dsimp [i]; omega)
        have htx : t.player.1 = s.player.1 := Fin.ext (ray.lane ⟨q, by omega⟩)
        have hty : t.player.2.val + q = s.player.2.val := by
          have hy := ray.position ⟨q, by omega⟩
          change -(t.player.2.val : ℤ) = -(s.player.2.val : ℤ) + (q : ℕ) at hy
          omega
        have he : northData t cutoff = northData s cutoff \ ray.gap := by
          have hsame : northData t cutoff = northData (R.target hs hgap) cutoff := by
            simp only [northData, htx, R.target_column]
            rfl
          exact hsame.trans (R.target_data hs hgap hv)
        refine ⟨t, hr, htx, hty, ?_, ?_, ?_⟩
        · rw [he]
          exact R.first_read hs hgap
        · rw [he]
          have hdel : northData s cutoff \ (northData s cutoff \ ray.gap) = ray.gap := by
            ext p
            have hp : p ∈ ray.gap → p ∈ northData s cutoff := fun hp => R.gap_subset hs hgap hp
            simp only [Finset.mem_sdiff]
            tauto
          rw [hdel, Slide.gap_card]
          exact hqk
        · intro p hp
          exact ray.off_lane_boxes (by intro he; exact hp (Fin.ext he))
      · let u := R.target hs hgap
        have hr : Reachable s u := R.target_reachable hs hgap hv
        have hux : u.player.1 = s.player.1 := R.target_column hs hgap
        have huy : u.player.2.val + R.length = s.player.2.val := R.target_row hs hgap
        have huc : (northData u cutoff).card + R.length = (northData s cutoff).card :=
          R.target_data_card hs hgap hv
        obtain ⟨t, ht, htx, hty, H2, hq2, hf⟩ := ih (q - R.length) (by omega) u (hr.valid hv)
          (by omega) (by omega) (R.target_gap hs hgap hv)
        have H0 : ExactNorthRead (northData s cutoff) (northData u cutoff) := by
          rw [R.target_data hs hgap hv]
          exact R.first_read hs hgap
        refine ⟨t, hr.trans ht, htx.trans hux, by omega, H0.trans H2, ?_, ?_⟩
        · have hsub := H2.subset.trans H0.subset
          have hle := Finset.card_le_card H2.subset
          rw [Finset.card_sdiff_of_subset H2.subset] at hq2
          rw [Finset.card_sdiff_of_subset hsub]
          omega
        · intro p hp
          exact (hf p (by rwa [hux])).trans (R.target_off_column hs hgap hp)

end PushPuzzle.PushPush.Reader
