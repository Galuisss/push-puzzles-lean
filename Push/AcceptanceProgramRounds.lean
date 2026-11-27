/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.Scan

/-! Compact same-direction reader blocks and exact target-front quota emission. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS

/-- One whole same-direction read round, or one family of simultaneous parallel clears. -/
inductive Round
  | read (side : Direction) (quotas : List (ℕ × ℕ))
  | clear (side : Direction) (lanes : Finset ℕ)

/-- Expand lines only when interpreting a compact round. -/
def Round.instructions {w h : ℕ} : Round → List (Scan.Instruction w h)
  | .read side quotas => quotas.map fun (lane, q) => .read side lane q
  | .clear side lanes => [.clear side lanes]

/-- The actual instruction list, retaining the separate outer round list as its size parameter. -/
def instructions {w h : ℕ} (rounds : List Round) : List (Scan.Instruction w h) :=
  rounds.flatMap Round.instructions

/-- A read request specifies a line and the length of its coordinate front from the stated side. -/
inductive Template
  | read (side : Direction) (prefixes : List (ℕ × ℕ))
  | clear (side : Direction) (lanes : Finset ℕ)

private theorem consume_skip {α : Type*} [DecidableEq α] {a : α} {cells : List α}
    {E : Finset α} (ha : a ∉ E) (q : ℕ) :
    Scan.consume (a :: cells) q E = Scan.consume cells q E := by
  cases q <;> simp only [Scan.consume, ite_eq_right ha]

/-- Consuming every current hole of a literal line front leaves exactly its complement. -/
theorem consume_prefix {α : Type*} [DecidableEq α] (front suffix : List α) (E : Finset α) :
    Scan.consume (front ++ suffix) (E.filter fun a => a ∈ front).card E =
      some (E \ front.toFinset) := by
  induction front generalizing E with
  | nil => simp only [List.nil_append, List.not_mem_nil, Finset.filter_false, Finset.card_empty,
      Scan.consume, List.toFinset_nil, Finset.sdiff_empty]
  | cons a front ih =>
    by_cases ha : a ∈ E
    · have he : (E.erase a).filter (fun b => b ∈ front) =
          (E.filter (fun b => b ∈ a :: front)).erase a := by
        ext b
        simp only [Finset.mem_filter, Finset.mem_erase, List.mem_cons]
        tauto
      have hc := Finset.card_erase_add_one
        (s := E.filter (fun b => b ∈ a :: front)) (a := a) (by simp [ha])
      rw [← he] at hc
      rw [← hc]
      simp only [List.cons_append, Scan.consume, ite_eq_left ha, ih]
      congr 1
      ext b
      simp only [Finset.mem_sdiff, Finset.mem_erase, List.toFinset_cons,
        Finset.mem_insert, List.mem_toFinset]
      tauto
    · have he : E.filter (fun b => b ∈ a :: front) = E.filter (fun b => b ∈ front) := by
        ext b
        simp only [Finset.mem_filter, List.mem_cons]
        constructor
        · rintro ⟨hb, hba | hbp⟩
          · exact False.elim (ha (hba ▸ hb))
          · exact ⟨hb, hbp⟩
        · exact fun ⟨hb, hbp⟩ => ⟨hb, Or.inr hbp⟩
      rw [he, List.cons_append, consume_skip ha, ih]
      congr 1
      ext b
      simp only [Finset.mem_sdiff, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset]
      by_cases hb : b = a <;> simp_all

private theorem prefix_card {α : Type*} [DecidableEq α] (front : List α) (E : Finset α) :
    (E \ front.toFinset).card + (E.filter fun a => a ∈ front).card = E.card := by
  have he : E \ front.toFinset = E.filter (fun a => a ∉ front) := by
    ext a
    simp only [Finset.mem_sdiff, List.mem_toFinset, Finset.mem_filter]
  rw [he, Nat.add_comm]
  exact Finset.card_filter_add_card_filter_not _

/-- A single emitted same-direction round and its exact target remainder. -/
structure ReadEmission (w h : ℕ) where
  quotas : List (ℕ × ℕ)
  remaining : Finset (Cell w h)

/-- Each quota counts holes in the literal target front, after earlier requests in this round. -/
def emitReads {w h : ℕ} (side : Direction) :
    List (ℕ × ℕ) → Finset (Cell w h) → ReadEmission w h
  | [], E => ⟨[], E⟩
  | (lane, span) :: requests, E =>
      let front := (Scan.lineCells side lane).take span
      let q := (E.filter fun a => a ∈ front).card
      let tail := emitReads side requests (E \ front.toFinset)
      ⟨(lane, q) :: tail.quotas, tail.remaining⟩

private theorem read_prefix {w h : ℕ} (side : Direction) (lane span : ℕ) (E : Finset (Cell w h)) :
    (Scan.Instruction.read side lane (E.filter fun a => a ∈
      (Scan.lineCells side lane).take span).card).eval E =
      some (E \ ((Scan.lineCells side lane).take span).toFinset) := by
  have hh := consume_prefix ((Scan.lineCells side lane).take span)
    ((Scan.lineCells side lane).drop span) E
  simpa only [List.take_append_drop, Scan.Instruction.eval] using hh

/-- Prefix quotas emitted from the actual target never short-read that target. -/
theorem emitReads_eval {w h : ℕ} (side : Direction) (requests : List (ℕ × ℕ))
    (E : Finset (Cell w h)) :
    Scan.eval ((Round.read side (emitReads side requests E).quotas).instructions)
      E = some (emitReads side requests E).remaining := by
  induction requests generalizing E with
  | nil => rfl
  | cons request requests ih =>
    rcases request with ⟨lane, span⟩
    simp only [emitReads, Round.instructions, List.map_cons, Scan.eval, read_prefix, Option.bind_some]
    exact ih _

/-- The emitted positive quotas account for precisely the removed target front holes. -/
private theorem emitReads_card {w h : ℕ} (side : Direction) (requests : List (ℕ × ℕ))
    (E : Finset (Cell w h)) :
    (emitReads side requests E).remaining.card +
      ((emitReads side requests E).quotas.map Prod.snd).sum = E.card := by
  induction requests generalizing E with
  | nil => simp only [emitReads, List.map_nil, List.sum_nil, Nat.add_zero]
  | cons request requests ih =>
    rcases request with ⟨lane, span⟩
    have hc := prefix_card ((Scan.lineCells side lane).take span) E
    have ht := ih (E \ ((Scan.lineCells side lane).take span).toFinset)
    simp only [emitReads, List.map_cons, List.sum_cons]
    omega

/-- A finite static reader, its target remainder, and the holes removed by its clear rounds. -/
structure Emission (w h : ℕ) where
  rounds : List Round
  remaining : Finset (Cell w h)
  discarded : ℕ

/-- Emit the compact same-direction blocks on one target, retaining every actual clear deletion. -/
def emit {w h : ℕ} : List Template → Finset (Cell w h) → Emission w h
  | [], E => ⟨[], E, 0⟩
  | .read side requests :: schedule, E =>
      let here := emitReads side requests E
      let tail := emit schedule here.remaining
      ⟨.read side here.quotas :: tail.rounds, tail.remaining, tail.discarded⟩
  | .clear side lanes :: schedule, E =>
      let tail := emit schedule (E.filter fun p => side.lane p ∉ lanes)
      ⟨.clear side lanes :: tail.rounds, tail.remaining,
        (E.filter fun p => side.lane p ∈ lanes).card + tail.discarded⟩

/-- Expanding an emitted schedule preserves exactly one outer block per requested round. -/
theorem emit_rounds_length {w h : ℕ} (schedule : List Template) (E : Finset (Cell w h)) :
    (emit schedule E).rounds.length = schedule.length := by
  induction schedule generalizing E with
  | nil => rfl
  | cons stage schedule ih => cases stage <;> simpa only [emit, List.length_cons] using congrArg Nat.succ (ih _)

private theorem eval_append {w h : ℕ} (left right : List (Scan.Instruction w h))
    (E : Finset (Cell w h)) : Scan.eval (left ++ right) E = (Scan.eval left E).bind (Scan.eval right) := by
  induction left generalizing E with
  | nil => rfl
  | cons i left ih => simp only [List.cons_append, Scan.eval, ih, Option.bind_assoc]

/-- The emitted static word accepts the target from which all its line quotas were computed. -/
theorem emit_eval {w h : ℕ} (schedule : List Template) (E : Finset (Cell w h)) :
    Scan.eval (instructions (emit schedule E).rounds) E = some (emit schedule E).remaining := by
  induction schedule generalizing E with
  | nil => rfl
  | cons stage schedule ih =>
    cases stage with
    | read side requests =>
      simp only [emit, instructions, List.flatMap_cons, eval_append, emitReads_eval, Option.bind_some]
      exact ih _
    | clear side lanes =>
      simp only [emit, instructions, List.flatMap_cons, Round.instructions, List.singleton_append,
        Scan.eval, Scan.Instruction.eval, Option.bind_some]
      exact ih _

/-- Total positive payment of a whole round. -/
def Round.quota : Round → ℕ
  | .read _ quotas => (quotas.map Prod.snd).sum
  | .clear _ _ => 0

private theorem round_quota {w h : ℕ} (round : Round) :
    Scan.quota (round.instructions (w := w) (h := h)) = round.quota := by
  cases round <;> simp only [Round.instructions, Round.quota, Scan.quota,
    List.map_map, Function.comp_def, Scan.Instruction.quota, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, Nat.add_zero]

/-- Flattening lines does not change any quota payment. -/
theorem quota_instructions {w h : ℕ} (rounds : List Round) :
    Scan.quota (instructions (w := w) (h := h) rounds) = (rounds.map Round.quota).sum := by
  induction rounds with
  | nil => rfl
  | cons round rounds ih =>
    simp only [instructions, List.flatMap_cons, Scan.quota, List.map_append, List.sum_append,
      List.map_cons, List.sum_cons]
    exact congrArg₂ Nat.add (round_quota round) ih

/-- Quotas, final residual, and actual clear deletions partition the original target holes. -/
theorem emit_accounting {w h : ℕ} (schedule : List Template) (E : Finset (Cell w h)) :
    (emit schedule E).remaining.card + ((emit schedule E).rounds.map Round.quota).sum +
      (emit schedule E).discarded = E.card := by
  induction schedule generalizing E with
  | nil => simp only [emit, List.map_nil, List.sum_nil, Nat.add_zero]
  | cons stage schedule ih =>
    cases stage with
    | read side requests =>
      have hh := emitReads_card side requests E
      have ht := ih (emitReads side requests E).remaining
      simp only [emit, List.map_cons, List.sum_cons, Round.quota]
      omega
    | clear side lanes =>
      have hh := Finset.card_filter_add_card_filter_not (s := E) (fun p => side.lane p ∈ lanes)
      have ht := ih (E.filter fun p => side.lane p ∉ lanes)
      simp only [emit, List.map_cons, List.sum_cons, Round.quota, Nat.zero_add]
      omega

/-- Target-prefix reads only remove holes. -/
theorem emitReads_remaining_subset {w h : ℕ} (side : Direction) (requests : List (ℕ × ℕ))
    (E : Finset (Cell w h)) : (emitReads side requests E).remaining ⊆ E := by
  induction requests generalizing E with
  | nil => exact Finset.Subset.refl _
  | cons request requests ih =>
    rcases request with ⟨lane, span⟩
    exact (ih _).trans (Finset.sdiff_subset)

/-- Every later target remainder is a subset of its input hole set. -/
theorem emit_remaining_subset {w h : ℕ} (schedule : List Template) (E : Finset (Cell w h)) :
    (emit schedule E).remaining ⊆ E := by
  induction schedule generalizing E with
  | nil => exact Finset.Subset.refl _
  | cons stage schedule ih =>
    cases stage with
    | read side requests => exact (ih _).trans (emitReads_remaining_subset side requests E)
    | clear side lanes => exact (ih _).trans (Finset.filter_subset _ _)

/-- A hole surviving the entire program avoids every line cleared anywhere in the schedule. -/
theorem emit_clear_excluded {w h : ℕ} {schedule : List Template} {E : Finset (Cell w h)}
    {side : Direction} {lanes : Finset ℕ} (hclear : Template.clear side lanes ∈ schedule)
    {q : Cell w h} (hq : q ∈ (emit schedule E).remaining) : side.lane q ∉ lanes := by
  induction schedule generalizing E with
  | nil => simp only [List.not_mem_nil] at hclear
  | cons stage schedule ih =>
    rcases List.mem_cons.mp hclear with he | ht
    · subst stage
      have hh := emit_remaining_subset schedule (E.filter fun p => side.lane p ∉ lanes) hq
      exact (Finset.mem_filter.mp hh).2
    · cases stage with
      | read orientation requests => exact ih ht hq
      | clear orientation lines => exact ih ht hq

/-- Concatenating compact schedules passes the exact target remainder to the following blocks. -/
theorem emit_remaining_append {w h : ℕ} (left right : List Template) (E : Finset (Cell w h)) :
    (emit (left ++ right) E).remaining = (emit right (emit left E).remaining).remaining := by
  induction left generalizing E with
  | nil => rfl
  | cons stage left ih => cases stage <;> exact ih _

/-- Clear losses add over consecutive target schedules. -/
theorem emit_discarded_append {w h : ℕ} (left right : List Template) (E : Finset (Cell w h)) :
    (emit (left ++ right) E).discarded = (emit left E).discarded +
      (emit right (emit left E).remaining).discarded := by
  induction left generalizing E with
  | nil => exact (Nat.zero_add _).symm
  | cons stage left ih =>
    cases stage with
    | read side requests => exact ih _
    | clear side lanes => simp only [List.cons_append, emit, ih, Nat.add_assoc]

/-- A list of literal read blocks has zero clear loss on every stock. -/
theorem emit_discarded_reads {w h : ℕ} (schedule : List Template) (E : Finset (Cell w h))
    (hread : ∀ t ∈ schedule, ∃ side requests, t = .read side requests) :
    (emit schedule E).discarded = 0 := by
  induction schedule generalizing E with
  | nil => rfl
  | cons stage schedule ih =>
    obtain ⟨side, requests, rfl⟩ := hread stage (List.mem_cons_self ..)
    exact ih _ (fun t ht => hread t (List.mem_cons_of_mem _ ht))

end PushPuzzle.Push.AcceptanceProgram
