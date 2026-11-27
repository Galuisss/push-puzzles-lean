/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramInterlevelStockPrefix
import all Push.AcceptanceProgramInterlevelStockPrefix
import all Push.AcceptanceProgramLayout

/-! Literal positions of every deleting read in the actual lower and upper page checks. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS PushS.PortLayout

private theorem split_append {α : Type*} (A B before after : List α) (a : α)
    (hs : A ++ B = before ++ a :: after) :
    (∃ pre post, A = pre ++ a :: post ∧ before = pre) ∨
      (∃ pre post, B = pre ++ a :: post ∧ before = A ++ pre) := by
  induction A generalizing before with
  | nil => exact Or.inr ⟨before, after, hs, rfl⟩
  | cons b A ih =>
    cases before with
    | nil =>
      have he : b = a := (List.cons.inj hs).1
      exact Or.inl ⟨[], A, by simp only [List.nil_append, he], rfl⟩
    | cons c before =>
      obtain ⟨he, hrest⟩ := List.cons.inj hs
      subst c
      rcases ih before hrest with ⟨pre, post, hA, hpre⟩ | ⟨pre, post, hB, hpre⟩
      · exact Or.inl ⟨b :: pre, post, by simp only [List.cons_append, hA], by rw [hpre]⟩
      · exact Or.inr ⟨pre, post, hB, by simp only [List.cons_append, hpre]⟩

private theorem row_read_lane (p : Scales.Parameters) (row : ℕ) (side : Direction)
    (requests : List (ℕ × ℕ)) (q : Cell (p.W + 1) (p.H + 1))
    (he : readRows p .west {row} = .read side requests)
    (hline : ∃ a ∈ requests, side.lane q = a.1) : q.2.val = row := by
  have hs := (Template.read.inj he).1
  subst side
  obtain ⟨a, ha, hx⟩ := hline
  have hr := (Template.read.inj he).2
  rw [← hr] at ha
  have hlane := ((mem_prefixRequests _ _ a.1 a.2).mp ha).1
  exact hx.trans (Finset.mem_singleton.mp hlane)

private theorem pair_read_location (l : PortLayout) (p : Scales.Parameters) (page : Side)
    (start n : ℕ) (before after : List Template) (side : Direction)
    (requests : List (ℕ × ℕ)) (q : Cell (p.W + 1) (p.H + 1))
    (hs : (List.range' start n).flatMap (checkPair l p page) = before ++ .read side requests :: after)
    (hn : side ≠ .south) (hline : ∃ a ∈ requests, side.lane q = a.1) :
    ∃ j, start + 1 ≤ j ∧ j ≤ start + n ∧ q.2.val = interlevelRow p page j ∧
      before.length = 2 * (j - start - 1) := by
  induction n generalizing start before with
  | zero => simp only [List.range'_zero, List.flatMap_nil] at hs; cases before <;> cases hs
  | succ n ih =>
    rw [List.range'_succ, List.flatMap_cons] at hs
    cases before with
    | nil =>
      have he := (List.cons.inj hs).1
      exact ⟨start + 1, le_rfl, by omega, row_read_lane p _ side requests q he hline, by simp⟩
    | cons b before =>
      have hs := (List.cons.inj hs).2
      cases before with
      | nil =>
        have he := (List.cons.inj hs).1
        cases page with
        | upper => cases he
        | lower => exact False.elim (hn (Template.read.inj he).1.symm)
      | cons c before =>
        have hs := (List.cons.inj hs).2
        obtain ⟨j, hj0, hjn, hrow, hlen⟩ := ih (start + 1) before hs
        refine ⟨j, by omega, by omega, hrow, ?_⟩
        simp only [List.length_cons]
        omega

private theorem page_read_position (l : PortLayout) (p : Scales.Parameters) (page : Side)
    (before after : List Template) (side : Direction) (requests : List (ℕ × ℕ))
    (q : Cell (p.W + 1) (p.H + 1))
    (hs : pageChecks l p page = before ++ .read side requests :: after)
    (hn : side ≠ .south) (hline : ∃ a ∈ requests, side.lane q = a.1) :
    (page = .lower ∧ q.2.val = p.H - p.Y 1 / 2 ∧ before.length = 1) ∨
      ∃ j, 1 ≤ j ∧ j < p.levels ∧ q.2.val = interlevelRow p page j ∧
        before.length = (checkHead l p page).length + 2 * (j - 1) := by
  rw [pageChecks_eq] at hs
  rcases split_append _ _ before after _ hs with ⟨pre, post, hhead, hpre⟩ | ⟨pre, post, hpairs, hpre⟩
  · cases page with
    | upper =>
      cases pre with
      | nil => simp only [checkHead] at hhead; cases (List.cons.inj hhead).1
      | cons b pre =>
        simp only [checkHead] at hhead
        have he := (List.cons.inj hhead).2
        cases pre <;> cases he
    | lower =>
      cases pre with
      | nil =>
        have he := (List.cons.inj hhead).1
        exact False.elim (hn (Template.read.inj he).1.symm)
      | cons b pre =>
        have hhead := (List.cons.inj hhead).2
        cases pre with
        | nil =>
          have he := (List.cons.inj hhead).1
          exact Or.inl ⟨rfl, row_read_lane p _ side requests q he hline, by rw [hpre]; rfl⟩
        | cons c pre =>
          have he := (List.cons.inj hhead).2
          cases pre with
          | nil => cases (List.cons.inj he).1
          | cons d pre => have he := (List.cons.inj he).2; cases pre <;> cases he
  · have hpairs' : (List.range' 0 (p.levels - 1)).flatMap (checkPair l p page) =
        pre ++ .read side requests :: post := by simpa only [List.range_eq_range'] using hpairs
    obtain ⟨j, hj0, hjn, hrow, hlen⟩ := pair_read_location l p page 0 _ pre post side requests q hpairs' hn hline
    refine Or.inr ⟨j, by omega, by omega, hrow, ?_⟩
    rw [hpre, List.length_append, hlen]
    simp only [Nat.sub_zero]

/-- Every page-check deleting read is a south column read or the uniquely positioned matching row read. -/
theorem page_read_location (l : PortLayout) (p : Scales.Parameters)
    (before after : List Template) (side : Direction) (requests : List (ℕ × ℕ))
    (q : Cell (p.W + 1) (p.H + 1))
    (hs : pageChecks l p .lower ++ pageChecks l p .upper = before ++ .read side requests :: after)
    (hline : ∃ a ∈ requests, side.lane q = a.1) :
    side = .south ∨
      (q.2.val = p.H - p.Y 1 / 2 ∧ before = (pageChecks l p .lower ++ pageChecks l p .upper).take 1) ∨
      ∃ page j, 1 ≤ j ∧ j < p.levels ∧ q.2.val = interlevelRow p page j ∧
        before = interlevelPrefix l p page j := by
  by_cases hn : side = .south
  · exact Or.inl hn
  right
  have hbefore : before = (pageChecks l p .lower ++ pageChecks l p .upper).take before.length := by
    rw [hs, List.take_left]
  rcases split_append _ _ before after _ hs with ⟨pre, post, hp, hb⟩ | ⟨pre, post, hp, hb⟩
  · rcases page_read_position l p .lower pre post side requests q hp hn hline with
      ⟨_, hrow, hlen⟩ | ⟨j, hj0, hjm, hrow, hlen⟩
    · apply Or.inl
      refine ⟨hrow, ?_⟩
      have he : before.length = 1 := by rw [hb, hlen]
      simpa only [he] using hbefore
    · apply Or.inr
      refine ⟨.lower, j, hj0, hjm, hrow, ?_⟩
      have he : before.length = interlevelIndex l p .lower j := by
        rw [hb, hlen]
        simp only [checkHead, ite_true, interlevelIndex, List.length_cons, List.length_nil]
        omega
      simpa only [he, interlevelPrefix] using hbefore
  · rcases page_read_position l p .upper pre post side requests q hp hn hline with
      ⟨he, _, _⟩ | ⟨j, hj0, hjm, hrow, hlen⟩
    · cases he
    · apply Or.inr
      refine ⟨.upper, j, hj0, hjm, hrow, ?_⟩
      have he : before.length = interlevelIndex l p .upper j := by
        rw [hb, List.length_append, hlen]
        simp only [checkHead, reduceCtorEq, ite_false, interlevelIndex, List.length_cons, List.length_nil]
        omega
      simpa only [he, interlevelPrefix] using hbefore

/-- A valid matching interlevel prefix has exactly its literal page-check index. -/
theorem interlevelPrefix_length (l : PortLayout) (p : Scales.Parameters) (page : Side) {j : ℕ}
    (hj : 1 ≤ j) (hjm : j < p.levels) :
    (interlevelPrefix l p page j).length = interlevelIndex l p page j := by
  rw [interlevelPrefix_eq l p page hj hjm]
  exact beforeChecks_length l p page hj

/-- The half-depth row is preceded by the one literal initial lower-finish block. -/
theorem halfPrefix_length (l : PortLayout) (p : Scales.Parameters) :
    ((pageChecks l p .lower ++ pageChecks l p .upper).take 1).length = 1 := by
  rw [List.length_take, List.length_append, pageChecks_length, pageChecks_length]
  simp only [ite_true, reduceCtorEq, ite_false]
  omega

end PushPuzzle.Push.AcceptanceProgram
