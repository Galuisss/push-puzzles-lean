/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Slide

/-! Expand a maximum slide into unit pushes and an empty-corridor return walk. -/

@[expose] public section
namespace PushPuzzle.PushPush

open PushFS (Cell Direction Adjacent State Board)

variable {w h n k : ℕ} {d : Direction} {s t : State w h}

namespace Slide

/-- The translating run after `j` unit pushes. -/
def segment (r : Slide d s n k) (j : Fin (k + 1)) : Finset (Cell w h) :=
  Finset.univ.image fun i : Fin n => r.cell ⟨j.val + i.val + 1, by omega⟩

/-- Intermediate inventory while the original run translates. -/
def stageBoxes (r : Slide d s n k) (j : Fin (k + 1)) : Finset (Cell w h) :=
  (s.boxes \ r.before) ∪ r.segment j

/-- During expansion the player follows the trailing box. -/
def stage (r : Slide d s n k) (j : Fin (k + 1)) : State w h :=
  ⟨r.cell ⟨j.val, by omega⟩, r.stageBoxes j⟩

private theorem stationary_off_ray (r : Slide d s n k) (hv : s.player ∉ s.boxes)
    (i : Fin (n + k + 1)) : r.cell i ∉ s.boxes \ r.before := by
  rintro hp
  obtain ⟨hp, hnot⟩ := Finset.mem_sdiff.mp hp
  by_cases hi : i.val = 0
  · have he : i = 0 := Fin.ext hi
    exact hv (by simpa only [he, r.start] using hp)
  · by_cases hin : i.val ≤ n
    · apply hnot
      refine Finset.mem_image.mpr ⟨⟨i.val - 1, by omega⟩, Finset.mem_univ _, ?_⟩
      congr 1
      apply Fin.ext
      change i.val - 1 + 1 = i.val
      omega
    · have he : (⟨n + (i.val - n - 1) + 1, by omega⟩ : Fin (n + k + 1)) = i := by
        apply Fin.ext
        change n + (i.val - n - 1) + 1 = i.val
        omega
      exact r.clear ⟨i.val - n - 1, by omega⟩ (he ▸ hp)

private theorem mem_segment (r : Slide d s n k) (j : Fin (k + 1))
    (i : Fin (n + k + 1)) :
    r.cell i ∈ r.segment j ↔ j.val < i.val ∧ i.val ≤ j.val + n := by
  constructor
  · intro hp
    obtain ⟨a, _, he⟩ := Finset.mem_image.mp hp
    have he := congrArg Fin.val (r.injective he)
    change j.val + a.val + 1 = i.val at he
    constructor <;> omega
  · intro hi
    refine Finset.mem_image.mpr ⟨⟨i.val - j.val - 1, by omega⟩, Finset.mem_univ _, ?_⟩
    congr 1
    apply Fin.ext
    change j.val + (i.val - j.val - 1) + 1 = i.val
    omega

theorem mem_stageBoxes (r : Slide d s n k) (hv : s.player ∉ s.boxes)
    (j : Fin (k + 1)) (i : Fin (n + k + 1)) :
    r.cell i ∈ r.stageBoxes j ↔ j.val < i.val ∧ i.val ≤ j.val + n := by
  simp only [stageBoxes, Finset.mem_union, r.stationary_off_ray hv i, false_or, r.mem_segment]

theorem stage_zero (r : Slide d s n k) : r.stage 0 = s := by
  apply State.ext
  · exact r.start
  · change (s.boxes \ r.before) ∪ r.segment 0 = s.boxes
    have he : r.segment 0 = r.before := by simp only [segment, before, Fin.val_zero, Nat.zero_add]
    rw [he]
    exact Finset.sdiff_union_of_subset r.before_subset

theorem stage_update (r : Slide d s n k) (hn : 0 < n) (hv : s.player ∉ s.boxes) (j : Fin k) :
    r.stageBoxes j.succ = insert (r.cell ⟨j.val + n + 1, by omega⟩)
      ((r.stageBoxes j.castSucc).erase (r.cell ⟨j.val + 1, by omega⟩)) := by
  ext p
  by_cases hp : ∃ i, r.cell i = p
  · obtain ⟨i, rfl⟩ := hp
    simp only [r.mem_stageBoxes hv, Finset.mem_insert, Finset.mem_erase]
    have h1 : r.cell i = r.cell ⟨j.val + n + 1, by omega⟩ ↔ i.val = j.val + n + 1 := by
      rw [r.injective.eq_iff, Fin.ext_iff]
    have h2 : r.cell i ≠ r.cell ⟨j.val + 1, by omega⟩ ↔ i.val ≠ j.val + 1 := by
      rw [r.injective.ne_iff]
      exact not_congr Fin.ext_iff
    rw [h1, h2]
    change (j.val + 1 < i.val ∧ i.val ≤ j.val + 1 + n) ↔
      i.val = j.val + n + 1 ∨ (i.val ≠ j.val + 1 ∧ j.val < i.val ∧ i.val ≤ j.val + n)
    omega
  · have hseg (a : Fin (k + 1)) : p ∉ r.segment a := by
      intro hm
      obtain ⟨i, _, he⟩ := Finset.mem_image.mp hm
      exact hp ⟨_, he⟩
    have h1 : p ≠ r.cell ⟨j.val + n + 1, by omega⟩ := fun he => hp ⟨_, he.symm⟩
    have h2 : p ≠ r.cell ⟨j.val + 1, by omega⟩ := fun he => hp ⟨_, he.symm⟩
    simp only [stageBoxes, Finset.mem_union, hseg, or_false, Finset.mem_insert,
      Finset.mem_erase, h1, false_or]
    exact (and_iff_right h2).symm

/-- The exact full run at one intermediate unit stage of a maximum slide. -/
def stageRun (r : Slide d s n k) (hv : s.player ∉ s.boxes)
    (j : Fin k) (goals : Finset (Cell w h)) :
    PushFS.Run (⟨∅, goals⟩ : Board w h) d (r.stage j.castSucc) n where
    cell := fun i => r.cell ⟨j.val + i.val, by omega⟩
    start := by simp only [stage, Fin.val_castSucc, Fin.val_zero, Nat.add_zero]
    adjacent := by intro i; exact r.adjacent ⟨j.val + i.val, by omega⟩
    occupied := by
      intro i
      apply (r.mem_stageBoxes hv j.castSucc _).mpr
      change j.val < j.val + (i.val + 1) ∧ j.val + (i.val + 1) ≤ j.val + n
      constructor <;> omega
    empty := by
      intro hp
      have hp := (r.mem_stageBoxes hv j.castSucc _).mp hp
      change j.val < j.val + (n + 1) ∧ j.val + (n + 1) ≤ j.val + n at hp
      omega
    floor := fun _ => Finset.notMem_empty _

/-- One stage of a slide is an actual complete-run unit push. -/
theorem stage_move (r : Slide d s n k) (hn : 0 < n) (hv : s.player ∉ s.boxes)
    (j : Fin k) (goals : Finset (Cell w h)) :
    PushFS.Move (⟨∅, goals⟩ : Board w h) none d (r.stage j.castSucc) (r.stage j.succ) := by
  apply PushFS.Move.push (n := n) (run := r.stageRun hv j goals)
  · refine ⟨Finset.notMem_empty _, Finset.disjoint_empty_right _, ?_⟩
    intro hp
    have hp := (r.mem_stageBoxes hv j.castSucc _).mp hp
    change j.val < j.val ∧ j.val ≤ j.val + n at hp
    omega
  · exact hn
  · trivial
  · rfl
  · simpa only [stage, stageRun, Nat.add_assoc, Fin.val_one] using r.stage_update hn hv j

/-- Follow the run for its full sliding distance using ordinary unit pushes. -/
theorem stage_reachable (r : Slide d s n k) (hn : 0 < n) (hv : s.player ∉ s.boxes)
    (goals : Finset (Cell w h)) (j : Fin (k + 1)) :
    PushFS.Reachable (⟨∅, goals⟩ : Board w h) none s (r.stage j) := by
  have hr : PushFS.Reachable (⟨∅, goals⟩ : Board w h) none (r.stage 0) (r.stage j) := by
    induction j using Fin.induction with
    | zero => exact .refl
    | succ j ih => exact ih.tail ⟨d, r.stage_move hn hv j goals⟩
  simpa only [r.stage_zero] using hr

/-- Any later unit stage is reachable from an earlier one with the same box identities. -/
private theorem stage_path (r : Slide d s n k) (hn : 0 < n) (hv : s.player ∉ s.boxes)
    (goals : Finset (Cell w h)) (i j : Fin (k + 1)) (hij : i.val ≤ j.val) :
    PushFS.Reachable (⟨∅, goals⟩ : Board w h) none (r.stage i) (r.stage j) := by
  induction j using Fin.induction with
  | zero =>
    have he : i = 0 := Fin.ext (by change i.val = 0; change i.val ≤ 0 at hij; omega)
    rw [he]
  | succ j ih =>
    by_cases he : i.val = j.val + 1
    · have he : i = j.succ := Fin.ext he
      rw [he]
    · exact (ih (by change i.val ≤ j.val; change i.val ≤ j.val + 1 at hij; omega)).tail
        ⟨d, r.stage_move hn hv j goals⟩

/-- Walk-back states retain the final translated box set. -/
def returnState (r : Slide d s n k) (i : Fin (k + 1)) : State w h :=
  ⟨r.cell ⟨i.val, by omega⟩, r.boxes⟩

theorem return_empty (r : Slide d s n k) (hv : s.player ∉ s.boxes)
    (i : Fin (k + 1)) : (r.returnState i).player ∉ r.boxes := by
  intro hp
  have hp := (r.mem_stageBoxes hv (Fin.last k) ⟨i.val, by omega⟩).mp hp
  change k < i.val ∧ i.val ≤ k + n at hp
  omega

/-- The cells vacated behind the translated run form an actual empty return corridor. -/
private theorem return_reachable (r : Slide d s n k) (_hk : 0 < k) (hv : s.player ∉ s.boxes)
    (goals : Finset (Cell w h)) (i : Fin (k + 1)) (hi : 0 < i.val) :
    PushFS.Reachable (⟨∅, goals⟩ : Board w h) none (r.returnState i)
      ⟨r.cell ⟨1, by omega⟩, r.boxes⟩ := by
  induction i using Fin.induction with
  | zero => simp at hi
  | succ i ih =>
    by_cases hz : i.val = 0
    · have he : (⟨i.succ.val, by omega⟩ : Fin (n + k + 1)) = ⟨1, by omega⟩ := by
        apply Fin.ext
        change i.val + 1 = 1
        omega
      change PushFS.Reachable _ none ⟨r.cell _, r.boxes⟩ _
      rw [he]
    · have hp := r.return_empty hv i.succ
      have hq := r.return_empty hv i.castSucc
      have hm : PushFS.Move (⟨∅, goals⟩ : Board w h) none d.opposite
          (r.returnState i.succ) (r.returnState i.castSucc) :=
        .walk ⟨Finset.notMem_empty _, Finset.disjoint_empty_right _, hp⟩
          (r.adjacent ⟨i.val, by omega⟩).reverse (Finset.notMem_empty _) hq rfl
      exact (Relation.ReflTransGen.single ⟨d.opposite, hm⟩).trans (ih (by change 0 < i.val; omega))

/-- A maximum slide expands into unit pushes followed by the precise player return. -/
theorem unit_expansion (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hv : s.player ∉ s.boxes) (goals : Finset (Cell w h)) :
    PushFS.Reachable (⟨∅, goals⟩ : Board w h) none s
      ⟨r.cell ⟨1, by omega⟩, r.boxes⟩ :=
  (r.stage_reachable hn hv goals (Fin.last k)).trans
    (r.return_reachable hk hv goals (Fin.last k) hk)

/-- Every intermediate unit stage can finish the slide and restore the original player advance. -/
theorem stage_finish (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hv : s.player ∉ s.boxes) (goals : Finset (Cell w h)) (j : Fin (k + 1)) :
    PushFS.Reachable (⟨∅, goals⟩ : Board w h) none (r.stage j)
      ⟨r.cell ⟨1, by omega⟩, r.boxes⟩ :=
  (r.stage_path hn hv goals j (Fin.last k) (by change j.val ≤ k; have := j.isLt; omega)).trans
    (r.return_reachable hk hv goals (Fin.last k) hk)

/-- The canonical unit expansion retains every player predicate valid on its complete ray. -/
theorem unit_expansion_player_prefix (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hv : s.player ∉ s.boxes) (goals : Finset (Cell w h)) (P : Cell w h → Prop)
    (hP : ∀ i : Fin (k + 1), P (r.cell ⟨i.val, by omega⟩)) :
    Relation.ReflTransGen
      (fun u v : State w h => PushFS.Step (⟨∅, goals⟩ : Board w h) none u v ∧ P v.player)
      s ⟨r.cell ⟨1, by omega⟩, r.boxes⟩ := by
  let R := fun u v : State w h => PushFS.Step (⟨∅, goals⟩ : Board w h) none u v ∧ P v.player
  have hstage (j : Fin (k + 1)) : Relation.ReflTransGen R (r.stage 0) (r.stage j) := by
    induction j using Fin.induction with
    | zero => exact .refl
    | succ j ih => exact ih.tail ⟨⟨d, r.stage_move hn hv j goals⟩, hP j.succ⟩
  have hreturn (i : Fin (k + 1)) (hi : 0 < i.val) :
      Relation.ReflTransGen R (r.returnState i) ⟨r.cell ⟨1, by omega⟩, r.boxes⟩ := by
    induction i using Fin.induction with
    | zero => simp at hi
    | succ i ih =>
      by_cases hz : i.val = 0
      · have he : (⟨i.succ.val, by omega⟩ : Fin (n + k + 1)) = ⟨1, by omega⟩ := by
          apply Fin.ext
          change i.val + 1 = 1
          omega
        change Relation.ReflTransGen R ⟨r.cell _, r.boxes⟩ _
        rw [he]
      · have hm : PushFS.Move (⟨∅, goals⟩ : Board w h) none d.opposite
            (r.returnState i.succ) (r.returnState i.castSucc) :=
          .walk ⟨Finset.notMem_empty _, Finset.disjoint_empty_right _, r.return_empty hv i.succ⟩
            (r.adjacent ⟨i.val, by omega⟩).reverse (Finset.notMem_empty _)
            (r.return_empty hv i.castSucc) rfl
        exact (Relation.ReflTransGen.single ⟨⟨d.opposite, hm⟩, hP i.castSucc⟩).trans
          (ih (by change 0 < i.val; omega))
  have hr := (hstage (Fin.last k)).trans (hreturn (Fin.last k) hk)
  simpa only [r.stage_zero] using hr

/-- Every player predicate valid on the entire ray is retained by the unit expansion. -/
theorem unit_expansion_player (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hv : s.player ∉ s.boxes) (goals : Finset (Cell w h)) (P : Cell w h → Prop)
    (hP : ∀ i, P (r.cell i)) :
    Relation.ReflTransGen
      (fun u v : State w h => PushFS.Step (⟨∅, goals⟩ : Board w h) none u v ∧ P v.player)
      s ⟨r.cell ⟨1, by omega⟩, r.boxes⟩ :=
  r.unit_expansion_player_prefix hn hk hv goals P (fun _ => hP _)

/-- After the maximum slide, walk forward through any prefix of its vacated corridor. -/
theorem advance_reachable (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hv : s.player ∉ s.boxes) (i : Fin (k + 1)) (hi : 0 < i.val) :
    Reachable s (r.returnState i) := by
  induction i using Fin.induction with
  | zero => simp at hi
  | succ i ih =>
    by_cases hz : i.val = 0
    · have he : (⟨i.succ.val, by omega⟩ : Fin (n + k + 1)) = ⟨1, by omega⟩ := by
        apply Fin.ext
        change i.val + 1 = 1
        omega
      exact Relation.ReflTransGen.single ⟨d, Move.push hv hn hk r
        (by change r.cell _ = _; rw [he]) rfl⟩
    · have hp := r.return_empty hv i.castSucc
      have hq := r.return_empty hv i.succ
      apply (ih (by change 0 < i.val; omega)).tail
      exact ⟨d, Move.walk hp (r.adjacent ⟨i.val, by omega⟩) hq rfl⟩

end Slide

/-- Every maximum-sliding action is a finite ordinary-pushing trajectory. -/
theorem Move.unit_expansion (hm : Move d s t) (B : Board w h) (hw : B.walls = ∅) :
    PushFS.Reachable B none s t := by
  have he : B = ⟨∅, B.goals⟩ := PushFS.Board.ext hw rfl
  rw [he]
  cases hm with
  | walk hv ha he hb =>
    exact Relation.ReflTransGen.single ⟨d, .walk
      ⟨Finset.notMem_empty _, Finset.disjoint_empty_right _, hv⟩ ha (Finset.notMem_empty _) he hb⟩
  | push hv hn hk r hp hb =>
    have hr := r.unit_expansion hn hk hv B.goals
    have ht : t = ⟨r.cell ⟨1, by omega⟩, r.boxes⟩ := State.ext hp hb
    exact ht ▸ hr

/-- Expansion retains every actual maximum-slide endpoint and its exact player. -/
theorem Reachable.unit_expansion (hr : Reachable s t) (B : Board w h) (hw : B.walls = ∅) :
    PushFS.Reachable B none s t := by
  induction hr with
  | refl => exact .refl
  | tail _ hm ih => exact ih.trans (hm.choose_spec.unit_expansion B hw)

/-- An ordinary step preserving the complete box set is a legal maximum-game walk. -/
private theorem Move.of_unit_boxes {B : Board w h} {cap : Option ℕ}
    (hm : PushFS.Move B cap d s t) (hb : t.boxes = s.boxes) : Move d s t := by
  cases hm with
  | walk hv ha _ he hbox => exact .walk hv.2.2 ha he hbox
  | push _ hn _ run _ hbox =>
    have hs := run.first_occupied hn
    have ht : run.cell 1 ∈ t.boxes := hb ▸ hs
    rw [hbox, Finset.mem_insert, Finset.mem_erase] at ht
    rcases ht with he | ⟨he, _⟩
    · have he := congrArg Fin.val (run.injective he)
      change (1 : Fin (_ + 2)).val = _ at he
      simp only [Fin.val_one] at he
      omega
    · exact False.elim (he rfl)

theorem Step.of_unit_boxes {B : Board w h} {cap : Option ℕ}
    (hm : PushFS.Step B cap s t) (hb : t.boxes = s.boxes) : Step s t :=
  ⟨hm.choose, Move.of_unit_boxes hm.choose_spec hb⟩

end PushPuzzle.PushPush
