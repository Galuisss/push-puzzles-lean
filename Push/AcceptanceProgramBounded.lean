/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramSkeleton
public import Push.CyclicTurnProgram
public import Push.ScanComposition

/-! Canonical actual-lane normalization preserves every program that accepts its reference target. -/

@[expose] public section
namespace PushPuzzle.Push.Scan

open PushFS

/-- Requests outside the rectangle are zero; a clear may freely name empty exterior lanes. -/
def Instruction.LaneSafe {w h : ℕ} : Instruction w h → Prop
  | .read side lane quota => lane < laneCount side w h ∨ quota = 0
  | .clear .. => True

private theorem instruction_laneSafe {w h : ℕ} {i : Instruction w h} {E F : Finset (Cell w h)}
    (he : i.eval E = some F) : i.LaneSafe := by
  cases i with
  | clear => trivial
  | read side lane quota =>
    by_cases hb : lane < laneCount side w h
    · exact Or.inl hb
    · right
      have hq := (Instruction.read_accepts_iff side lane quota E).mp ⟨F, he⟩
      have hf : E.filter (fun q => side.lane q = lane) = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro q hq
        exact hb ((Finset.mem_filter.mp hq).2 ▸ lane_lt_count side q)
      rw [hf, Finset.card_empty] at hq
      omega

/-- Any successful reference execution certifies every exterior read as zero. -/
private theorem eval_laneSafe {w h : ℕ} {program : List (Instruction w h)} {E F : Finset (Cell w h)}
    (he : eval program E = some F) : ∀ i ∈ program, i.LaneSafe := by
  induction program generalizing E with
  | nil => simp
  | cons i program ih =>
    obtain ⟨G, hi, ht⟩ := Option.bind_eq_some_iff.mp he
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact instruction_laneSafe hi
    · exact ih ht j hj

end PushPuzzle.Push.Scan
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS

/-- Restrict a compact block to the actual finite rows or columns of the rectangle. -/
def Round.bounded (w h : ℕ) : Round → Round
  | .read side requests => .read side (requests.filter fun a => a.1 < Scan.laneCount side w h)
  | .clear side lanes => .clear side (lanes.filter fun lane => lane < Scan.laneCount side w h)

/-- Keep the complete block skeleton while naming only actual rectangle lanes. -/
def boundedRounds (w h : ℕ) (rounds : List Round) : List Round := rounds.map (Round.bounded w h)

private theorem bounded_read_eval {w h : ℕ} (side : Direction) (requests : List (ℕ × ℕ))
    (hs : ∀ a ∈ requests, a.1 < Scan.laneCount side w h ∨ a.2 = 0) (E : Finset (Cell w h)) :
    Scan.eval (Scan.lines side (requests.filter fun a => a.1 < Scan.laneCount side w h)) E =
      Scan.eval (Scan.lines side requests) E := by
  induction requests generalizing E with
  | nil => rfl
  | cons a rest ih =>
    by_cases hb : a.1 < Scan.laneCount side w h
    · simp only [List.filter_cons, decide_eq_true hb, ↓reduceIte,
        Scan.lines, List.map_cons, Scan.eval]
      apply congrArg ((Scan.Instruction.read side a.1 a.2).eval E).bind
      funext F
      exact ih (fun b hb => hs b (List.mem_cons_of_mem a hb)) F
    · have hz := (hs a (List.mem_cons_self ..)).resolve_left hb
      simp only [List.filter_cons, decide_eq_false hb, Bool.false_eq_true, ↓reduceIte,
        Scan.lines, List.map_cons, Scan.eval, hz, Scan.Instruction.eval, Scan.consume, Option.bind_some]
      exact ih (fun b hb => hs b (List.mem_cons_of_mem a hb)) E

private theorem bounded_round_eval {w h : ℕ} (block : Round)
    (hs : ∀ i ∈ block.instructions (w := w) (h := h), i.LaneSafe) (E : Finset (Cell w h)) :
    Scan.eval ((block.bounded w h).instructions) E = Scan.eval block.instructions E := by
  cases block with
  | read side requests =>
    exact bounded_read_eval side requests (fun a ha => hs _ (List.mem_map.mpr ⟨a, ha, rfl⟩)) E
  | clear side lanes =>
    change some (E.filter _) = some (E.filter _)
    congr 1
    apply Finset.filter_congr
    intro q _
    simp only [Finset.mem_filter, not_and]
    exact ⟨fun h hq => h hq (Scan.lane_lt_count side q), fun h hq _ => h hq⟩

/-- Every bounded block expands to actual finite lanes. -/
theorem boundedRounds_bounded (w h : ℕ) (rounds : List Round) :
    Scan.Bounded (instructions (w := w) (h := h) (boundedRounds w h rounds)) := by
  intro i hi
  obtain ⟨block, hb, hi⟩ := List.mem_flatMap.mp hi
  obtain ⟨old, _, rfl⟩ := List.mem_map.mp hb
  cases old with
  | read side requests =>
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hi
    rcases a with ⟨lane, quota⟩
    change lane < Scan.laneCount side w h
    exact of_decide_eq_true (List.mem_filter.mp ha).2
  | clear side lanes =>
    have he : i = Scan.Instruction.clear side (lanes.filter fun lane => lane < Scan.laneCount side w h) :=
      List.mem_singleton.mp hi
    subst i
    exact fun lane hl => (Finset.mem_filter.mp hl).2

/-- Normalization leaves every block tag and physical side unchanged. -/
theorem boundedRounds_shapes (w h : ℕ) (rounds : List Round) :
    (boundedRounds w h rounds).map Round.shape = rounds.map Round.shape := by
  induction rounds with
  | nil => rfl
  | cons block rest ih => cases block <;> simp only [boundedRounds, List.map_cons, Round.bounded,
      Round.shape] at ih ⊢ <;> exact congrArg (List.cons _) ih

/-- A reference-accepted program and its finite-lane normalization execute identically on every bitmap. -/
theorem boundedRounds_eval {w h : ℕ} (rounds : List Round)
    {reference result : Finset (Cell w h)}
    (he : Scan.eval (instructions rounds) reference = some result) (E : Finset (Cell w h)) :
    Scan.eval (instructions (boundedRounds w h rounds)) E = Scan.eval (instructions rounds) E := by
  have hs := Scan.eval_laneSafe he
  suffices hh : ∀ (rounds : List Round),
      (∀ i ∈ instructions (w := w) (h := h) rounds, i.LaneSafe) → ∀ E,
      Scan.eval (instructions (boundedRounds w h rounds)) E = Scan.eval (instructions rounds) E from hh rounds hs E
  intro rounds
  induction rounds with
  | nil => intro _ E; rfl
  | cons block rest ih =>
    intro hs E
    change Scan.eval ((block.bounded w h).instructions ++ instructions (boundedRounds w h rest)) E =
      Scan.eval (block.instructions ++ instructions rest) E
    rw [Scan.eval_append, Scan.eval_append, bounded_round_eval block
      (fun i hi => hs i (List.mem_append_left _ hi))]
    cases hh : Scan.eval block.instructions E with
    | none => rfl
    | some F => exact ih (fun i hi => hs i (List.mem_append_right _ hi)) F

private theorem bounded_requests_sum (w h : ℕ) (side : Direction) (requests : List (ℕ × ℕ))
    (hs : ∀ a ∈ requests, a.1 < Scan.laneCount side w h ∨ a.2 = 0) :
    ((requests.filter fun a => a.1 < Scan.laneCount side w h).map Prod.snd).sum =
      (requests.map Prod.snd).sum := by
  induction requests with
  | nil => rfl
  | cons a rest ih =>
    have ht := ih (fun b hb => hs b (List.mem_cons_of_mem a hb))
    by_cases hb : a.1 < Scan.laneCount side w h
    · simp only [List.filter_cons, decide_eq_true hb, ↓reduceIte, List.map_cons, List.sum_cons, ht]
    · have hz := (hs a (List.mem_cons_self ..)).resolve_left hb
      simp only [List.filter_cons, decide_eq_false hb, Bool.false_eq_true, ↓reduceIte,
        List.map_cons, List.sum_cons, hz, Nat.zero_add, ht]

/-- Exterior zero reads contribute no positive quota, so normalization preserves the complete budget. -/
theorem boundedRounds_quota {w h : ℕ} (rounds : List Round)
    {reference result : Finset (Cell w h)}
    (he : Scan.eval (instructions rounds) reference = some result) :
    Scan.quota (instructions (w := w) (h := h) (boundedRounds w h rounds)) =
      Scan.quota (instructions (w := w) (h := h) rounds) := by
  have hs := Scan.eval_laneSafe he
  rw [quota_instructions, quota_instructions]
  apply congrArg List.sum
  simp only [boundedRounds, List.map_map]
  apply List.map_congr_left
  intro block hb
  cases block with
  | clear side lanes => rfl
  | read side requests =>
    apply bounded_requests_sum
    intro a ha
    exact hs _ (List.mem_flatMap.mpr ⟨_, hb, List.mem_map.mpr ⟨a, ha, rfl⟩⟩)

end PushPuzzle.Push.AcceptanceProgram
