/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushFS.Grid
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.Finset.Card

/-! Destructive line scans and the full-quota accounting certificate. -/

@[expose] public section
namespace PushPuzzle.Push.Scan

open PushFS

variable {α : Type*} [DecidableEq α]

/-- Consume the first `q` holes encountered along the given ordered cells. -/
def consume : List α → ℕ → Finset α → Option (Finset α)
  | _, 0, E => some E
  | [], _ + 1, _ => none
  | a :: cells, q + 1, E =>
      if a ∈ E then consume cells q (E.erase a) else consume cells (q + 1) E

private theorem consume_subset {cells : List α} {q : ℕ} {E F : Finset α}
    (h : consume cells q E = some F) : F ⊆ E := by
  induction cells generalizing q E with
  | nil => cases q <;> simp_all [consume]
  | cons a cells ih =>
    cases q with
    | zero =>
      simp only [consume, Option.some.injEq] at h
      exact h ▸ Finset.Subset.refl E
    | succ q =>
      simp only [consume] at h
      split at h
      · exact (ih h).trans (Finset.erase_subset a E)
      · exact ih h

private theorem consume_card {cells : List α} {q : ℕ} {E F : Finset α}
    (h : consume cells q E = some F) : F.card + q = E.card := by
  induction cells generalizing q E with
  | nil => cases q <;> simp_all [consume]
  | cons a cells ih =>
    cases q with
    | zero => simp_all [consume]
    | succ q =>
      simp only [consume] at h
      split at h
      · have hc := ih h
        have he := Finset.card_erase_add_one ‹a ∈ E›
        omega
      · exact ih h

private theorem consume_skip {a : α} {cells : List α} {E : Finset α}
    (ha : a ∉ E) (q : ℕ) : consume (a :: cells) q E = consume cells q E := by
  cases q <;> simp only [consume, ite_eq_right ha]

/-- Consecutive reads from the same end consume exactly the sum of their quotas. -/
theorem consume_add (cells : List α) (q r : ℕ) (E : Finset α) :
    consume cells (q + r) E = (consume cells q E).bind (consume cells r) := by
  induction cells generalizing q r E with
  | nil => cases q <;> simp [Nat.succ_add, consume]
  | cons a cells ih =>
    cases q with
    | zero => simp only [Nat.zero_add, consume, Option.bind_some]
    | succ q =>
      by_cases ha : a ∈ E
      · simp only [Nat.succ_add, consume, ite_eq_left ha]
        rw [ih q r (E.erase a)]
        cases hh : consume cells q (E.erase a) with
        | none => simp only [Option.bind_none]
        | some F =>
          have hnot : a ∉ F := fun h => (Finset.mem_erase.mp (consume_subset hh h)).1 rfl
          simp only [Option.bind_some, consume_skip hnot]
      · simp only [Nat.succ_add, consume, ite_eq_right ha]
        rw [show q + r + 1 = (q + 1) + r by omega, ih (q + 1) r E]
        cases hh : consume cells (q + 1) E with
        | none => simp only [Option.bind_none]
        | some F =>
          have hnot : a ∉ F := fun h => ha (consume_subset hh h)
          simp only [Option.bind_some, consume_skip hnot]

/-- Additional holes and a smaller quota preserve successful consumption and its remainder. -/
private theorem consume_mono {cells : List α} {q r : ℕ} {E F E' : Finset α}
    (hEF : E ⊆ F) (hrq : r ≤ q) (h : consume cells q E = some E') :
    ∃ F', consume cells r F = some F' ∧ E' ⊆ F' := by
  induction cells generalizing q r E F with
  | nil =>
    cases q with
    | zero =>
      have hr : r = 0 := by omega
      subst r
      simp only [consume, Option.some.injEq] at h
      exact ⟨F, rfl, h ▸ hEF⟩
    | succ q => simp [consume] at h
  | cons a cells ih =>
    cases r with
    | zero => exact ⟨F, rfl, (consume_subset h).trans hEF⟩
    | succ r =>
      cases q with
      | zero => omega
      | succ q =>
        by_cases ha : a ∈ E
        · have haF := hEF ha
          simp only [consume, ite_eq_left ha] at h
          obtain ⟨F', hh, hs⟩ := ih (r := r) (Finset.erase_subset_erase a hEF) (by omega) h
          exact ⟨F', by simpa only [consume, ite_eq_left haF] using hh, hs⟩
        · simp only [consume, ite_eq_right ha] at h
          by_cases haF : a ∈ F
          · have hEF' : E ⊆ F.erase a := by
              intro b hb
              exact Finset.mem_erase.mpr ⟨fun he => ha (he ▸ hb), hEF hb⟩
            obtain ⟨F', hh, hs⟩ := ih (r := r) hEF' (by omega) h
            exact ⟨F', by simpa only [consume, ite_eq_left haF] using hh, hs⟩
          · obtain ⟨F', hh, hs⟩ := ih hEF hrq h
            exact ⟨F', by simpa only [consume, ite_eq_right haF] using hh, hs⟩

/-- Exactly the holes outside the traversed cells remain untouched. -/
theorem consume_outside {cells : List α} {q : ℕ} {E F : Finset α}
    (hh : consume cells q E = some F) {a : α} (ha : a ∉ cells) : a ∈ F ↔ a ∈ E := by
  induction cells generalizing q E with
  | nil => cases q <;> simp_all [consume]
  | cons b cells ih =>
    cases q with
    | zero => simp_all [consume]
    | succ q =>
      simp only [List.mem_cons, not_or] at ha
      simp only [consume] at hh
      split at hh
      · rw [ih hh ha.2]
        simp [ha.1]
      · exact ih hh ha.2

/-- A short read is the only reason consumption rejects. -/
private theorem consume_accepts_iff (cells : List α) (q : ℕ) (E : Finset α) :
    (∃ F, consume cells q E = some F) ↔ q ≤ (E.filter fun a => a ∈ cells).card := by
  induction cells generalizing q E with
  | nil => cases q <;> simp [consume]
  | cons a cells ih =>
    cases q with
    | zero => simp [consume]
    | succ q =>
      by_cases ha : a ∈ E
      · have he : (E.erase a).filter (fun b => b ∈ cells) =
            (E.filter (fun b => b ∈ a :: cells)).erase a := by
          ext b
          simp only [Finset.mem_filter, Finset.mem_erase, List.mem_cons]
          tauto
        have hc := Finset.card_erase_add_one
          (s := E.filter (fun b => b ∈ a :: cells)) (a := a) (by simp [ha])
        rw [← he] at hc
        simp only [consume, ite_eq_left ha, ih]
        omega
      · have he : E.filter (fun b => b ∈ a :: cells) = E.filter (fun b => b ∈ cells) := by
          ext b
          simp only [Finset.mem_filter, List.mem_cons]
          constructor
          · rintro ⟨hb, hba | hbc⟩
            · exact False.elim (ha (hba ▸ hb))
            · exact ⟨hb, hbc⟩
          · exact fun ⟨hb, hbc⟩ => ⟨hb, Or.inr hbc⟩
        simp only [consume, ite_eq_right ha, ih, he]

variable {w h : ℕ}

/-- All cells in a line, starting at the specified side of the rectangle. -/
def lineCells (side : Direction) (lane : ℕ) : List (Cell w h) :=
  match side with
  | .north => if hx : lane < w then List.ofFn (fun y => (⟨lane, hx⟩, y)) else []
  | .south => if hx : lane < w then (List.ofFn (fun y => (⟨lane, hx⟩, y))).reverse else []
  | .west => if hy : lane < h then List.ofFn (fun x => (x, ⟨lane, hy⟩)) else []
  | .east => if hy : lane < h then (List.ofFn (fun x => (x, ⟨lane, hy⟩))).reverse else []

/-- The ordered list enumerates exactly its selected row or column. -/
@[simp] theorem mem_lineCells (side : Direction) (lane : ℕ) (p : Cell w h) :
    p ∈ lineCells side lane ↔ side.lane p = lane := by
  cases side <;> simp only [lineCells, Direction.lane]
  all_goals
    split
    next hb =>
      simp only [List.mem_reverse, List.mem_ofFn]
      constructor
      · rintro ⟨i, hi⟩
        cases hi
        rfl
      · intro he
        cases p with
        | mk x y =>
          first
          | exact ⟨y, by apply Prod.ext <;> simp_all [Fin.ext_iff]⟩
          | exact ⟨x, by apply Prod.ext <;> simp_all [Fin.ext_iff]⟩
    next hb =>
      simp only [List.not_mem_nil, false_iff]
      intro he
      exact hb (he ▸ (by first | exact p.1.isLt | exact p.2.isLt))

/-- Each selected cell is inspected once. -/
theorem lineCells_nodup (side : Direction) (lane : ℕ) :
    (lineCells (w := w) (h := h) side lane).Nodup := by
  cases side <;> simp only [lineCells]
  all_goals
    split
    next hb =>
      simp only [List.nodup_reverse, List.nodup_ofFn]
      intro i j hij
      first | exact congrArg Prod.fst hij | exact congrArg Prod.snd hij
    next hb => exact List.nodup_nil

/-- One static read or an entire family of parallel line clears. -/
inductive Instruction (w h : ℕ)
  | read (side : Direction) (lane quota : ℕ)
  | clear (side : Direction) (lanes : Finset ℕ)

/-- The number of holes charged by a positive read. Clears charge zero. -/
def Instruction.quota : Instruction w h → ℕ
  | .read _ _ q => q
  | .clear _ _ => 0

/-- Execute one instruction on its current finite hole set. -/
def Instruction.eval : Instruction w h → Finset (Cell w h) → Option (Finset (Cell w h))
  | .read side lane q, E => consume (lineCells side lane) q E
  | .clear side lanes, E => some (E.filter fun p => side.lane p ∉ lanes)

/-- A clear encounters empty lines; reads impose no additional condition here. -/
def Instruction.ClearEmpty : Instruction w h → Finset (Cell w h) → Prop
  | .read _ _ _, _ => True
  | .clear side lanes, E => ∀ p ∈ E, side.lane p ∉ lanes

private theorem Instruction.eval_subset {i : Instruction w h} {E F : Finset (Cell w h)}
    (hi : i.eval E = some F) : F ⊆ E := by
  cases i with
  | read side lane q => exact consume_subset hi
  | clear side lanes =>
    simp only [eval, Option.some.injEq] at hi
    exact hi ▸ Finset.filter_subset _ _

private theorem Instruction.eval_card_le {i : Instruction w h} {E F : Finset (Cell w h)}
    (hi : i.eval E = some F) : F.card + i.quota ≤ E.card := by
  cases i with
  | read side lane q => exact (consume_card hi).le
  | clear side lanes => simpa [quota] using Finset.card_le_card (eval_subset hi)

private theorem Instruction.clearEmpty_of_card {i : Instruction w h} {E F : Finset (Cell w h)}
    (hi : i.eval E = some F) (hc : F.card + i.quota = E.card) : i.ClearEmpty E := by
  cases i with
  | read => trivial
  | clear side lanes =>
    have he : F = E := Finset.eq_of_subset_of_card_le (eval_subset hi) (by simpa [quota] using hc.ge)
    simp only [eval, Option.some.injEq] at hi
    intro p hp
    have : p ∈ E.filter (fun p => side.lane p ∉ lanes) := by simpa [hi, he] using hp
    exact (Finset.mem_filter.mp this).2

/-- Reading a whole line succeeds exactly when that line contains the quota. -/
theorem Instruction.read_accepts_iff (side : Direction) (lane q : ℕ) (E : Finset (Cell w h)) :
    (∃ F, (Instruction.read side lane q).eval E = some F) ↔
      q ≤ (E.filter fun p => side.lane p = lane).card := by
  simpa only [eval, mem_lineCells] using consume_accepts_iff (lineCells side lane) q E

/-- Reading a line leaves every other line cell unchanged. -/
theorem Instruction.read_outside {side : Direction} {lane q : ℕ} {E F : Finset (Cell w h)}
    (hh : (Instruction.read side lane q).eval E = some F) {p : Cell w h}
    (hp : side.lane p ≠ lane) : p ∈ F ↔ p ∈ E :=
  consume_outside hh (fun h => hp ((mem_lineCells side lane p).mp h))

/-- The selected line loses exactly its fixed quota. -/
theorem Instruction.read_line_card {side : Direction} {lane q : ℕ} {E F : Finset (Cell w h)}
    (hh : (Instruction.read side lane q).eval E = some F) :
    (F.filter fun p => side.lane p = lane).card + q = (E.filter fun p => side.lane p = lane).card := by
  have hother : F.filter (fun p => side.lane p ≠ lane) = E.filter (fun p => side.lane p ≠ lane) := by
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hp, hne⟩
      exact ⟨(Instruction.read_outside hh hne).mp hp, hne⟩
    · rintro ⟨hp, hne⟩
      exact ⟨(Instruction.read_outside hh hne).mpr hp, hne⟩
  have hcard := consume_card hh
  have hE : (E.filter fun p => side.lane p = lane).card +
      (E.filter fun p => side.lane p ≠ lane).card = E.card :=
    Finset.card_filter_add_card_filter_not (s := E) (fun p : Cell w h => side.lane p = lane)
  have hF : (F.filter fun p => side.lane p = lane).card +
      (F.filter fun p => side.lane p ≠ lane).card = F.card :=
    Finset.card_filter_add_card_filter_not (s := F) (fun p : Cell w h => side.lane p = lane)
  rw [hother] at hF
  omega

/-- Execute the fixed program, rejecting at its first short read. -/
def eval : List (Instruction w h) → Finset (Cell w h) → Option (Finset (Cell w h))
  | [], E => some E
  | i :: program, E => (i.eval E).bind (eval program)

/-- Total positive quota, fixed before the program runs. -/
def quota (program : List (Instruction w h)) : ℕ := (program.map Instruction.quota).sum

/-- Acceptance requires every read to be paid in order. -/
def Accepts (program : List (Instruction w h)) (E : Finset (Cell w h)) : Prop :=
  ∃ F, eval program E = some F

/-- Every clear in this execution encounters only empty lines. -/
def ClearsEmpty : List (Instruction w h) → Finset (Cell w h) → Prop
  | [], _ => True
  | i :: program, E => ∃ F, i.eval E = some F ∧ i.ClearEmpty E ∧ ClearsEmpty program F

private theorem eval_card_le {program : List (Instruction w h)} {E F : Finset (Cell w h)}
    (hp : eval program E = some F) : F.card + quota program ≤ E.card := by
  induction program generalizing E with
  | nil => simp_all [eval, quota]
  | cons i program ih =>
    simp only [eval, Option.bind_eq_some_iff] at hp
    obtain ⟨G, hi, hp⟩ := hp
    have hh := Instruction.eval_card_le hi
    have ht := ih hp
    simp only [quota, List.map_cons, List.sum_cons]
    change F.card + (i.quota + quota program) ≤ E.card
    omega

/-- Successful full payment exhausts the holes and makes every intervening clear delete zero. -/
theorem full_quota {program : List (Instruction w h)} {E F : Finset (Cell w h)}
    (hp : eval program E = some F) (hq : quota program = E.card) :
    F = ∅ ∧ ClearsEmpty program E := by
  induction program generalizing E with
  | nil =>
    simp only [eval, Option.some.injEq] at hp
    simp only [quota, List.map_nil, List.sum_nil] at hq
    subst F
    exact ⟨Finset.card_eq_zero.mp hq.symm, trivial⟩
  | cons i program ih =>
    simp only [eval, Option.bind_eq_some_iff] at hp
    obtain ⟨G, hi, hp⟩ := hp
    have hh := Instruction.eval_card_le hi
    have ht := eval_card_le hp
    simp only [quota, List.map_cons, List.sum_cons] at hq
    change i.quota + quota program = E.card at hq
    have hg : quota program = G.card := by omega
    obtain ⟨hF, hclear⟩ := ih hp hg
    exact ⟨hF, G, hi, Instruction.clearEmpty_of_card hi (by omega), hclear⟩

/-- Successful suffixes remain payable when the current hole set is enlarged. -/
private theorem eval_mono {program : List (Instruction w h)} {E G F : Finset (Cell w h)}
    (hEG : E ⊆ G) (hp : eval program E = some F) :
    ∃ G', eval program G = some G' ∧ F ⊆ G' := by
  induction program generalizing E G with
  | nil =>
    simp only [eval, Option.some.injEq] at hp
    exact ⟨G, rfl, hp ▸ hEG⟩
  | cons i program ih =>
    simp only [eval, Option.bind_eq_some_iff] at hp
    obtain ⟨E', hi, hp⟩ := hp
    have hm : ∃ G', i.eval G = some G' ∧ E' ⊆ G' := by
      cases i with
      | read side lane q => exact consume_mono hEG le_rfl hi
      | clear side lanes =>
        simp only [Instruction.eval, Option.some.injEq] at hi
        exact ⟨_, rfl, hi ▸ Finset.filter_subset_filter _ hEG⟩
    obtain ⟨G', hiG, hEG'⟩ := hm
    obtain ⟨G'', hpG, hFG⟩ := ih hEG' hp
    exact ⟨G'', by simp only [eval, hiG, Option.bind_some]; exact hpG, hFG⟩

theorem accepts_mono {program : List (Instruction w h)} {E F : Finset (Cell w h)}
    (hEF : E ⊆ F) (hp : Accepts program E) : Accepts program F := by
  obtain ⟨E', hp⟩ := hp
  obtain ⟨F', hh, _⟩ := eval_mono hEF hp
  exact ⟨F', hh⟩

end PushPuzzle.Push.Scan
