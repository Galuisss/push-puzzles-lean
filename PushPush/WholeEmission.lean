/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.WholeDenormalize
public import Push.AcceptanceProgramRounds

/-! Repeated equal-span probes emit at most one positive quota on each lane. -/

@[expose] public section
namespace PushPuzzle.PushPush.WholeScan

open PushFS (Cell Direction)
open Push.AcceptanceProgram

variable {w h : ℕ}

private theorem emitReads_zero_on_prefix (side : Direction) (requests : List (ℕ × ℕ))
    (E : Finset (Cell w h)) (lane span : ℕ)
    (hspan : ∀ a ∈ requests, a.1 = lane → a.2 = span)
    (hempty : ∀ p ∈ E, p ∈ (Push.Scan.lineCells side lane).take span → False) :
    ∀ a ∈ (emitReads side requests E).quotas, a.1 = lane → a.2 = 0 := by
  induction requests generalizing E with
  | nil => simp [emitReads]
  | cons a rest ih =>
    intro b hb hblane
    change b ∈ (a.1, (E.filter fun p => p ∈ (Push.Scan.lineCells side a.1).take a.2).card) ::
      (emitReads side rest (E \ ((Push.Scan.lineCells side a.1).take a.2).toFinset)).quotas at hb
    rcases List.mem_cons.mp hb with he | hb
    · subst b
      have hs := hspan a (List.mem_cons_self ..) hblane
      change (E.filter fun p => p ∈ (Push.Scan.lineCells side a.1).take a.2).card = 0
      rw [hblane, hs]
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨hp, hprefix⟩ := Finset.mem_filter.mp hp
      exact hempty p hp hprefix
    · apply ih _ (fun a ha => hspan a (List.mem_cons_of_mem _ ha)) ?_ b hb hblane
      intro p hp hprefix
      exact hempty p (Finset.mem_sdiff.mp hp).1 hprefix

/-- Uniform probe spans on each lane ensure that repeated emitted quotas after
its first positive request are all zero. -/
private theorem emitReads_positive_nodup (side : Direction) (requests : List (ℕ × ℕ))
    (E : Finset (Cell w h))
    (hspan : ∀ a ∈ requests, ∀ b ∈ requests, a.1 = b.1 → a.2 = b.2) :
    (((emitReads side requests E).quotas.filter fun a => a.2 ≠ 0).map Prod.fst).Nodup := by
  induction requests generalizing E with
  | nil => exact List.nodup_nil
  | cons a rest ih =>
    let front := (Push.Scan.lineCells (w := w) (h := h) side a.1).take a.2
    let quota := (E.filter fun p => p ∈ front).card
    have ht := ih (E \ front.toFinset)
      (fun b hb c hc => hspan b (List.mem_cons_of_mem _ hb) c (List.mem_cons_of_mem _ hc))
    change (((a.1, quota) :: (emitReads side rest (E \ front.toFinset)).quotas).filter
      fun a => a.2 ≠ 0).map Prod.fst |>.Nodup
    by_cases hz : quota = 0
    · simpa only [List.filter_cons, hz, ne_eq, not_true_eq_false, decide_false,
        Bool.false_eq_true, ite_false] using ht
    · simp only [List.filter_cons, hz, ne_eq, not_false_eq_true, decide_true, ite_true, List.map_cons]
      apply List.nodup_cons.mpr ⟨?_, ht⟩
      intro hm
      obtain ⟨b, hb, hblane⟩ := List.mem_map.mp hm
      obtain ⟨hb, hbpos⟩ := List.mem_filter.mp hb
      have hbpos : b.2 ≠ 0 := of_decide_eq_true hbpos
      apply hbpos
      apply emitReads_zero_on_prefix side rest (E \ front.toFinset) a.1 a.2 ?_ ?_ b hb hblane
      · intro c hc he
        exact hspan c (List.mem_cons_of_mem _ hc) a (List.mem_cons_self ..) he
      · intro p hp hprefix
        exact (Finset.mem_sdiff.mp hp).2 (List.mem_toFinset.mpr hprefix)

private theorem emitReads_lanes (side : Direction) (requests : List (ℕ × ℕ))
    (E : Finset (Cell w h)) : (emitReads side requests E).quotas.map Prod.fst = requests.map Prod.fst := by
  induction requests generalizing E with
  | nil => rfl
  | cons a rest ih => exact congrArg (a.1 :: ·) (ih _)

theorem emit_rounds_positive_nodup (templates : List Template) (E : Finset (Cell w h))
    (hspan : ∀ side requests, Template.read side requests ∈ templates →
      ∀ a ∈ requests, ∀ b ∈ requests, a.1 = b.1 → a.2 = b.2) :
    ∀ side requests, Round.read side requests ∈ (emit templates E).rounds →
      ((requests.filter fun a => a.2 ≠ 0).map Prod.fst).Nodup := by
  induction templates generalizing E with
  | nil => simp [emit]
  | cons template templates ih =>
    intro side requests hm
    cases template with
    | read d fronts =>
      change Round.read side requests ∈ .read d (emitReads d fronts E).quotas :: _ at hm
      rcases List.mem_cons.mp hm with he | hm
      · cases he
        exact emitReads_positive_nodup _ _ _ (hspan side fronts (List.mem_cons_self ..))
      · exact ih _ (fun d rs hr => hspan d rs (List.mem_cons_of_mem _ hr)) side requests hm
    | clear d lanes =>
      change Round.read side requests ∈ .clear d lanes :: _ at hm
      rcases List.mem_cons.mp hm with he | hm
      · cases he
      · exact ih _ (fun d rs hr => hspan d rs (List.mem_cons_of_mem _ hr)) side requests hm

theorem emit_rounds_read_bounded (templates : List Template) (E : Finset (Cell w h))
    (hbound : ∀ side requests, Template.read side requests ∈ templates →
      ∀ a ∈ requests, a.1 < Push.Scan.laneCount side w h) :
    ∀ side requests, Round.read side requests ∈ (emit templates E).rounds →
      ∀ a ∈ requests, a.1 < Push.Scan.laneCount side w h := by
  induction templates generalizing E with
  | nil => simp [emit]
  | cons template templates ih =>
    intro side requests hm
    cases template with
    | read d fronts =>
      change Round.read side requests ∈ .read d (emitReads d fronts E).quotas :: _ at hm
      rcases List.mem_cons.mp hm with he | hm
      · cases he
        intro a ha
        have hlane : a.1 ∈ fronts.map Prod.fst := by
          rw [← emitReads_lanes side fronts E]
          exact List.mem_map.mpr ⟨a, ha, rfl⟩
        obtain ⟨b, hb, he⟩ := List.mem_map.mp hlane
        rw [← he]
        exact hbound side fronts (List.mem_cons_self ..) b hb
      · exact ih _ (fun d rs hr => hbound d rs (List.mem_cons_of_mem _ hr)) side requests hm
    | clear d lanes =>
      change Round.read side requests ∈ .clear d lanes :: _ at hm
      rcases List.mem_cons.mp hm with he | hm
      · cases he
      · exact ih _ (fun d rs hr => hbound d rs (List.mem_cons_of_mem _ hr)) side requests hm

end PushPuzzle.PushPush.WholeScan
