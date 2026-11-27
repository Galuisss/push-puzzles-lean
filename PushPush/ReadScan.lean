/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.ReadExact
public import Push.ScanEmbedding

/-! Connect whole-run reads to the existing static scan compiler. -/

@[expose] public section
namespace PushPuzzle.PushPush.Reader

open PushFS (Cell State)

private theorem consume_result {α : Type} [DecidableEq α] (key : α → ℤ)
    (cells : List α) (q : ℕ) (E F : Finset α)
    (horder : cells.Pairwise (fun a b => key b < key a))
    (hcover : ∀ p ∈ E, p ∈ cells) (hr : Push.Scan.consume cells q E = some F) :
    F ⊆ E ∧ F.card + q = E.card ∧ ∀ p ∈ E \ F, ∀ a ∈ F, key a < key p := by
  induction cells generalizing q E with
  | nil =>
    cases q with
    | zero =>
      simp only [Push.Scan.consume, Option.some.injEq] at hr
      subst F
      exact ⟨fun _ hp => hp, by omega, by simp⟩
    | succ q => simp [Push.Scan.consume] at hr
  | cons b cells ih =>
    cases q with
    | zero =>
      simp only [Push.Scan.consume, Option.some.injEq] at hr
      subst F
      exact ⟨fun _ hp => hp, by omega, by simp⟩
    | succ q =>
      have hord := List.pairwise_cons.mp horder
      by_cases hb : b ∈ E
      · rw [Push.Scan.consume, ite_eq_left hb] at hr
        have hc : ∀ p ∈ E.erase b, p ∈ cells := by
          intro p hp
          obtain ⟨hne, hp⟩ := Finset.mem_erase.mp hp
          exact (List.mem_cons.mp (hcover p hp)).resolve_left hne
        obtain ⟨hf, hcount, hfront⟩ := ih q (E.erase b) hord.2 hc hr
        refine ⟨hf.trans (Finset.erase_subset _ _), ?_, ?_⟩
        · have := Finset.card_erase_add_one hb
          omega
        · intro p hp a ha
          by_cases hpb : p = b
          · subst p
            have hac := hc a (hf ha)
            exact hord.1 a hac
          · have hp := Finset.mem_sdiff.mp hp
            exact hfront p (Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨hpb, hp.1⟩, hp.2⟩) a ha
      · rw [Push.Scan.consume, ite_eq_right hb] at hr
        have hc : ∀ p ∈ E, p ∈ cells := by
          intro p hp
          exact (List.mem_cons.mp (hcover p hp)).resolve_left (fun he => hb (he ▸ hp))
        exact ih (q + 1) E hord.2 hc hr

private theorem consume_of_front {α : Type} [DecidableEq α] (key : α → ℤ)
    (cells : List α) (E F : Finset α) (horder : cells.Pairwise (fun a b => key b < key a))
    (hcover : ∀ p ∈ E, p ∈ cells) (hsub : F ⊆ E)
    (hfront : ∀ p ∈ E \ F, ∀ q ∈ F, key q < key p) :
    Push.Scan.consume cells (E \ F).card E = some F := by
  induction cells generalizing E F with
  | nil =>
    have he : E = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact List.not_mem_nil (hcover p hp)
    have hf : F = ∅ := Finset.Subset.antisymm (he ▸ hsub) (Finset.empty_subset _)
    simp [he, hf, Push.Scan.consume]
  | cons a cells ih =>
    have hord := List.pairwise_cons.mp horder
    by_cases hz : (E \ F).card = 0
    · have he : E = F := by
        apply Finset.Subset.antisymm _ hsub
        intro p hp
        by_contra hn
        have hc := Finset.card_pos.mpr ⟨p, Finset.mem_sdiff.mpr ⟨hp, hn⟩⟩
        omega
      simp [he, Push.Scan.consume]
    · by_cases ha : a ∈ E
      · have haf : a ∉ F := by
          intro haf
          obtain ⟨p, hp⟩ := Finset.card_pos.mp (by omega : 0 < (E \ F).card)
          have hpe := (Finset.mem_sdiff.mp hp).1
          have hne : p ≠ a := fun he => (Finset.mem_sdiff.mp hp).2 (he ▸ haf)
          have hpc : p ∈ cells := (List.mem_cons.mp (hcover p hpe)).resolve_left hne
          have := hord.1 p hpc
          have := hfront p hp a haf
          omega
        have hfs : F ⊆ E.erase a := by
          intro p hp
          exact Finset.mem_erase.mpr ⟨fun he => haf (he ▸ hp), hsub hp⟩
        have hc : ∀ p ∈ E.erase a, p ∈ cells := by
          intro p hp
          obtain ⟨hne, hp⟩ := Finset.mem_erase.mp hp
          exact (List.mem_cons.mp (hcover p hp)).resolve_left hne
        have hf : ∀ p ∈ E.erase a \ F, ∀ q ∈ F, key q < key p := by
          intro p hp q hq
          have hp := Finset.mem_sdiff.mp hp
          exact hfront p (Finset.mem_sdiff.mpr ⟨Finset.mem_of_mem_erase hp.1, hp.2⟩) q hq
        have hd : E.erase a \ F = (E \ F).erase a := by
          ext p
          simp only [Finset.mem_sdiff, Finset.mem_erase]
          tauto
        have hcard : (E \ F).card = (E.erase a \ F).card + 1 := by
          rw [hd]
          exact (Finset.card_erase_add_one (Finset.mem_sdiff.mpr ⟨ha, haf⟩)).symm
        rw [hcard, Push.Scan.consume, ite_eq_left ha]
        exact ih (E.erase a) F hord.2 hc hfs hf
      · have hc : ∀ p ∈ E, p ∈ cells := by
          intro p hp
          exact (List.mem_cons.mp (hcover p hp)).resolve_left (fun he => ha (he ▸ hp))
        have hcard : ∃ n, (E \ F).card = n + 1 := Nat.exists_eq_succ_of_ne_zero hz
        obtain ⟨n, hn⟩ := hcard
        rw [hn, Push.Scan.consume, ite_eq_right ha, ← hn]
        exact ih E F hord.2 hc hsub hfront

end PushPuzzle.PushPush.Reader
