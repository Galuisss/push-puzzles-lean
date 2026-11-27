/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.LineWalking
public import Mathlib.Data.Finset.Max
import all PushS.LinePush

/-! A genuine eastward walk/push sweep turns a row prefix into holes using its eastern inventory. -/

public section
namespace PushPuzzle.Push.CornerDock.Backup

open PushFS PushS

variable {w h : ℕ}

/-- Available holes beyond a fixed cut in the player's current row. -/
@[expose] def inventory (s : HoleState w h) (cut : ℕ) : Finset (Cell w h) :=
  s.empty.filter fun q => q.2 = s.player.2 ∧ cut ≤ q.1.val

private theorem east_step (s : HoleState w h)
    (hne : (s.empty.filter fun q => q.2 = s.player.2 ∧ s.player.1.val < q.1.val).Nonempty)
    (B : Board w h) (hB : B.walls = ∅) :
    ∃ (t : HoleState w h) (b : Cell w h), Move B none .east s.toState t.toState ∧
      b ∈ s.empty ∧ b.2 = s.player.2 ∧ s.player.1.val < b.1.val ∧
      t.player.2 = s.player.2 ∧ t.player.1.val = s.player.1.val + 1 ∧
      t.empty = insert t.player (s.empty.erase b) := by
  obtain ⟨b, hb, hmin⟩ :=
    (s.empty.filter fun q => q.2 = s.player.2 ∧ s.player.1.val < q.1.val).exists_min_image
      (fun q => q.1.val) hne
  obtain ⟨hbE, hby, hbx⟩ := Finset.mem_filter.mp hb
  let p : Cell w h := (⟨s.player.1.val + 1, by have := b.1.isLt; omega⟩, s.player.2)
  let t : HoleState w h := ⟨p, insert p (s.empty.erase b), Finset.mem_insert_self _ _⟩
  refine ⟨t, b, ?_, hbE, hby, hbx, rfl, rfl, rfl⟩
  by_cases hpb : p = b
  · refine Move.walk (s.valid B hB) ⟨rfl, rfl⟩ (by simp [hB]) ?_ ?_
    · change p ∉ s.emptyᶜ
      exact Finset.notMem_compl.mpr (hpb.symm ▸ hbE)
    · change (insert p (s.empty.erase b))ᶜ = s.emptyᶜ
      rw [hpb, Finset.insert_erase hbE]
  · have hfar : s.player.1.val + 1 < b.1.val := by
      by_contra hn
      have hp : p = b := Prod.ext (Fin.ext (by dsimp [p]; omega)) hby.symm
      exact hpb hp
    apply HoleState.move_to_first_hole s t .east b (b.1.val - s.player.1.val - 1)
      (by omega) (congrArg Fin.val hby) ?_ ?_ hbE ⟨rfl, rfl⟩ rfl B hB
    · change (b.1.val : ℤ) = (s.player.1.val : ℤ) + (b.1.val - s.player.1.val - 1 : ℕ) + 1
      omega
    · intro q hl hlo hhi hq
      have hqE : q ∈ s.empty.filter (fun q => q.2 = s.player.2 ∧ s.player.1.val < q.1.val) :=
        Finset.mem_filter.mpr ⟨hq, Fin.ext hl, by change (s.player.1.val : ℤ) < q.1.val at hlo; omega⟩
      have hm := hmin q hqE
      change (q.1.val : ℤ) < b.1.val at hhi
      omega

private theorem transport_frame (s t : HoleState w h) (b : Cell w h)
    (hby : b.2 = s.player.2) (hbx : s.player.1.val < b.1.val)
    (hty : t.player.2 = s.player.2) (htx : t.player.1.val = s.player.1.val + 1)
    (he : t.empty = insert t.player (s.empty.erase b)) :
    ∀ q : Cell w h, q.2 ≠ s.player.2 ∨ q.1.val ≤ s.player.1.val →
      (q ∈ t.empty ↔ q ∈ s.empty) := by
  intro q hq
  have hqp : q ≠ t.player := by
    intro hq'; subst q
    rcases hq with hq | hq
    · exact hq hty
    · omega
  have hqb : q ≠ b := by
    intro hq'; subst q
    rcases hq with hq | hq
    · exact hq hby
    · omega
  rw [he]
  constructor
  · intro hh
    rcases Finset.mem_insert.mp hh with hh | hh
    · exact False.elim (hqp hh)
    · exact (Finset.mem_erase.mp hh).2
  · intro hh
    exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨hqb, hh⟩))

private theorem inventory_transport (s t : HoleState w h) (b : Cell w h) (cut : ℕ)
    (hty : t.player.2 = s.player.2) (htx : t.player.1.val < cut)
    (he : t.empty = insert t.player (s.empty.erase b)) :
    inventory t cut = (inventory s cut).erase b := by
  ext q
  simp only [inventory, he, hty, Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
  by_cases hq : q = t.player
  · subst q; simp only [true_or, true_and]; omega
  · simp only [hq, false_or]; tauto

private theorem inventory_one_loss (s t : HoleState w h) (b : Cell w h) (cut : ℕ)
    (hty : t.player.2 = s.player.2) (htx : t.player.1.val < cut)
    (he : t.empty = insert t.player (s.empty.erase b)) :
    (inventory s cut).card ≤ (inventory t cut).card + 1 := by
  rw [inventory_transport s t b cut hty htx he]
  by_cases hb : b ∈ inventory s cut
  · exact (Finset.card_erase_add_one hb).ge
  · rw [Finset.erase_eq_of_notMem hb]
    omega

/-- Advance across a whole row prefix with genuine walks or complete pushes, keeping a prescribed reserve. -/
private theorem fill_east (s : HoleState w h) (n cut keep : ℕ)
    (hcut : s.player.1.val + n < cut) (hcount : n + keep ≤ (inventory s cut).card)
    (B : Board w h) (hB : B.walls = ∅) :
    ∃ t : HoleState w h, Reachable B none s.toState t.toState ∧
      t.player.2 = s.player.2 ∧ t.player.1.val = s.player.1.val + n ∧
      (∀ q : Cell w h, q.2 = s.player.2 → s.player.1.val ≤ q.1.val →
        q.1.val ≤ s.player.1.val + n → q ∈ t.empty) ∧
      (∀ q : Cell w h, q.2 ≠ s.player.2 ∨ q.1.val ≤ s.player.1.val →
        (q ∈ t.empty ↔ q ∈ s.empty)) ∧ keep ≤ (inventory t cut).card := by
  induction n generalizing s with
  | zero =>
    refine ⟨s, .refl, rfl, by omega, ?_, fun _ _ => Iff.rfl, by omega⟩
    intro q hy hlo hhi
    have he : q = s.player := Prod.ext (Fin.ext (by omega)) hy
    exact he ▸ s.player_empty
  | succ n ih =>
    have hne : (inventory s cut).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨q, hq⟩ := hne
    obtain ⟨hqE, hqy, hqx⟩ := Finset.mem_filter.mp hq
    have hne' : (s.empty.filter fun q => q.2 = s.player.2 ∧ s.player.1.val < q.1.val).Nonempty :=
      ⟨q, Finset.mem_filter.mpr ⟨hqE, hqy, by omega⟩⟩
    obtain ⟨t, b, hm, _, hby, hbx, hty, htx, he⟩ := east_step s hne' B hB
    have hloss := inventory_one_loss s t b cut hty (by omega) he
    obtain ⟨u, hu, huy, hux, hprefix, hframe, hreserve⟩ := ih t (by omega) (by omega)
    have hframe' := transport_frame s t b hby hbx hty htx he
    refine ⟨u, (Relation.ReflTransGen.single ⟨.east, hm⟩).trans hu,
      huy.trans hty, by omega, ?_, ?_, hreserve⟩
    · intro p hpy hlo hhi
      by_cases hpx : p.1.val ≤ s.player.1.val
      · exact (hframe p (Or.inr (by omega))).mpr ((hframe' p (Or.inr hpx)).mpr
          ((Prod.ext (Fin.ext (by omega)) hpy : p = s.player) ▸ s.player_empty))
      · exact hprefix p (hpy.trans hty.symm) (by omega) (by omega)
    · intro p hp
      apply (hframe p ?_).trans (hframe' p hp)
      rcases hp with hp | hp
      · exact Or.inl (by rwa [hty])
      · exact Or.inr (by omega)

/-- Sweep a row and walk back through the new holes, preserving all other rows and the western corridor. -/
theorem fill_east_return (s : HoleState w h) (n cut keep : ℕ)
    (hcut : s.player.1.val + n < cut) (hcount : n + keep ≤ (inventory s cut).card)
    (B : Board w h) (hB : B.walls = ∅) :
    ∃ t : HoleState w h, Reachable B none s.toState t.toState ∧ t.player = s.player ∧
      (∀ q : Cell w h, q.2 = s.player.2 → s.player.1.val ≤ q.1.val →
        q.1.val ≤ s.player.1.val + n → q ∈ t.empty) ∧
      (∀ q : Cell w h, q.2 ≠ s.player.2 ∨ q.1.val ≤ s.player.1.val →
        (q ∈ t.empty ↔ q ∈ s.empty)) ∧ keep ≤ (inventory t cut).card := by
  obtain ⟨t, ht, hty, htx, hpref, hframe, hreserve⟩ := fill_east s n cut keep hcut hcount B hB
  have hp : s.player ∈ t.empty := hpref _ rfl le_rfl (by omega)
  have hback := (t.walk_horizontal s.player hp hty.symm (by
    intro q hqy hlo hhi
    apply hpref q (hqy.trans hty)
    · omega
    · omega) B hB none).1
  refine ⟨t.walk s.player hp, ht.trans hback, rfl, hpref, hframe, ?_⟩
  have he : inventory (t.walk s.player hp) cut = inventory t cut := by
    ext q
    simp only [inventory, HoleState.walk, hty]
    rfl
  rwa [he]

end PushPuzzle.Push.CornerDock.Backup
