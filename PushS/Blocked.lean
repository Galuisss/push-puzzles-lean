/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.Holes

/-! Unvisited permanent holes can become walls or ordinary boxes without changing moves. -/

@[expose] public section
namespace PushPuzzle.PushS.Blocked

open PushFS

variable {w h n : ℕ} {B : Board w h} {cap : Option ℕ}
  {G : Finset (Cell w h)} {d : Direction} {s t : State w h}

/-- Add inaccessible cells while retaining the same target set. -/
def block (B : Board w h) (G : Finset (Cell w h)) : Board w h :=
  ⟨B.walls ∪ G, B.goals⟩

/-- The specified cells are holes and the player is outside them. -/
structure Excluded (G : Finset (Cell w h)) (s : State w h) : Prop where
  empty : G ⊆ holes s
  player : s.player ∉ G

private theorem valid_block (hs : s.Valid B) (hG : Excluded G s) :
    s.Valid (block B G) := by
  refine ⟨?_, ?_, hs.2.2⟩
  · exact fun hp => (Finset.mem_union.mp hp).elim hs.1 hG.player
  · exact Finset.disjoint_union_right.mpr ⟨hs.2.1,
      Finset.disjoint_left.mpr fun p hp hpg => (mem_holes p).mp (hG.empty hpg) hp⟩

/-- No cell of a push run can lie in a permanently empty, unvisited region. -/
theorem run_avoids (r : Run B d s n) (hs : Excluded G s) (ht : Excluded G t)
    (hb : t.boxes = insert (r.cell ⟨n + 1, by omega⟩) (s.boxes.erase (r.cell 1)))
    (i : Fin (n + 2)) : r.cell i ∉ G := by
  intro hg
  by_cases hi : i.val = 0
  · have he : i = 0 := Fin.ext hi
    subst i
    exact hs.player (r.start ▸ hg)
  · by_cases hin : i.val ≤ n
    · exact (mem_holes _).mp (hs.empty hg) (r.occupied_at i (by omega) hin)
    · have he : i = (⟨n + 1, Nat.lt_succ_self (n + 1)⟩ : Fin (n + 2)) := by
        apply Fin.ext
        change i.val = n + 1
        omega
      rw [he] at hg
      have hp : r.cell ⟨n + 1, by omega⟩ ∈ t.boxes := by
        rw [hb]
        exact Finset.mem_insert_self _ _
      exact (mem_holes _).mp (ht.empty hg) hp

private def blockedRun (r : Run B d s n) (hs : Excluded G s) (ht : Excluded G t)
    (hb : t.boxes = insert (r.cell ⟨n + 1, by omega⟩) (s.boxes.erase (r.cell 1))) :
    Run (block B G) d s n where
  cell := r.cell
  start := r.start
  adjacent := r.adjacent
  occupied := r.occupied
  empty := r.empty
  floor i := fun hp => (Finset.mem_union.mp hp).elim (r.floor i) (run_avoids r hs ht hb i)

/-- The identical move remains legal after excluding its permanently empty cells. -/
private theorem move_block (hm : Move B cap d s t) (hs : Excluded G s) (ht : Excluded G t) :
    Move (block B G) cap d s t := by
  cases hm with
  | walk hv ha hf he hb =>
    exact .walk (valid_block hv hs) ha
      (fun hp => (Finset.mem_union.mp hp).elim hf ht.player) he hb
  | push hv hn hc r hp hb =>
    exact .push (valid_block hv hs) hn hc (blockedRun r hs ht hb) hp hb

private theorem step_block (hm : Step B cap s t) (hs : Excluded G s) (ht : Excluded G t) :
    Step (block B G) cap s t :=
  ⟨hm.choose, move_block hm.choose_spec hs ht⟩

/-- A legal step retaining the excluded empty region at both endpoints. -/
def ExcludingStep (B : Board w h) (cap : Option ℕ) (G : Finset (Cell w h))
    (s t : State w h) : Prop :=
  Step B cap s t ∧ Excluded G s ∧ Excluded G t

/-- A constrained trajectory runs unchanged on the board with added walls. -/
private theorem reachable_block (hr : Relation.ReflTransGen (ExcludingStep B cap G) s t) :
    Reachable (block B G) cap s t := by
  induction hr with
  | refl => exact .refl
  | tail _ hm ih => exact ih.tail (step_block hm.1 hm.2.1 hm.2.2)

private theorem excluding_of_invariant {R : State w h → State w h → Prop}
    (hR : ∀ ⦃u v⦄, R u v → Step B cap u v)
    (hr : Relation.ReflTransGen R s t) :
    (∀ u, Relation.ReflTransGen R s u → Relation.ReflTransGen R u t → Excluded G u) →
      Relation.ReflTransGen (ExcludingStep B cap G) s t := by
  induction hr with
  | refl => exact fun _ => .refl
  | @tail u v hsu huv ih =>
    intro hG
    have hu := hG u hsu (.single huv)
    have hv := hG v (hsu.tail huv) .refl
    exact (ih fun x hsx hxu => hG x hsx (hxu.tail huv)).tail ⟨hR huv, hu, hv⟩

/-- Prefix/suffix invariants on any chosen step relation suffice to add the walls. -/
theorem reachable_block_of_invariant {R : State w h → State w h → Prop}
    (hR : ∀ ⦃u v⦄, R u v → Step B cap u v)
    (hr : Relation.ReflTransGen R s t)
    (hG : ∀ u, Relation.ReflTransGen R s u → Relation.ReflTransGen R u t → Excluded G u) :
    Reachable (block B G) cap s t :=
  reachable_block (excluding_of_invariant hR hr hG)

/-- Fill the specified cells with ordinary boxes while retaining the exact player. -/
def fill (s : State w h) (G : Finset (Cell w h)) : State w h :=
  ⟨s.player, s.boxes ∪ G⟩

private theorem valid_fill (hs : s.Valid B) (hG : Excluded G s)
    (hfloor : Disjoint G B.walls) : (fill s G).Valid B := by
  exact ⟨hs.1, Finset.disjoint_union_left.mpr ⟨hs.2.1, hfloor⟩,
    fun hp => (Finset.mem_union.mp hp).elim hs.2.2 hG.player⟩

private def filledRun (r : Run B d s n) (hs : Excluded G s) (ht : Excluded G t)
    (hb : t.boxes = insert (r.cell ⟨n + 1, by omega⟩) (s.boxes.erase (r.cell 1))) :
    Run B d (fill s G) n where
  cell := r.cell
  start := r.start
  adjacent := r.adjacent
  occupied i := Finset.mem_union_left G (r.occupied i)
  empty hp := (Finset.mem_union.mp hp).elim r.empty (run_avoids r hs ht hb _)
  floor := r.floor

/-- Filling excluded floor holes preserves the same move on the original board. -/
private theorem move_fill (hm : Move B cap d s t) (hs : Excluded G s) (ht : Excluded G t)
    (hfloor : Disjoint G B.walls) : Move B cap d (fill s G) (fill t G) := by
  cases hm with
  | walk hv ha hf he hb =>
    exact .walk (valid_fill hv hs hfloor) ha hf
      (fun hp => (Finset.mem_union.mp hp).elim he ht.player) (congrArg (· ∪ G) hb)
  | push hv hn hc r hp hb =>
    refine .push (valid_fill hv hs hfloor) hn hc (filledRun r hs ht hb) hp ?_
    change t.boxes ∪ G = insert (r.cell _) ((s.boxes ∪ G).erase (r.cell 1))
    rw [hb, Finset.erase_union_distrib,
      Finset.erase_eq_of_notMem (run_avoids r hs ht hb 1), Finset.insert_union]

private theorem step_fill (hm : Step B cap s t) (hs : Excluded G s) (ht : Excluded G t)
    (hfloor : Disjoint G B.walls) : Step B cap (fill s G) (fill t G) :=
  ⟨hm.choose, move_fill hm.choose_spec hs ht hfloor⟩

/-- A constrained trajectory survives filling its excluded holes with ordinary boxes. -/
private theorem reachable_fill (hr : Relation.ReflTransGen (ExcludingStep B cap G) s t)
    (hfloor : Disjoint G B.walls) : Reachable B cap (fill s G) (fill t G) := by
  induction hr with
  | refl => exact .refl
  | tail _ hm ih => exact ih.tail (step_fill hm.1 hm.2.1 hm.2.2 hfloor)

/-- Prefix/suffix exclusion invariants also preserve the exact filled trajectory. -/
theorem reachable_fill_of_invariant {R : State w h → State w h → Prop}
    (hR : ∀ ⦃u v⦄, R u v → Step B cap u v)
    (hr : Relation.ReflTransGen R s t)
    (hG : ∀ u, Relation.ReflTransGen R s u → Relation.ReflTransGen R u t → Excluded G u)
    (hfloor : Disjoint G B.walls) : Reachable B cap (fill s G) (fill t G) :=
  reachable_fill (excluding_of_invariant hR hr hG) hfloor

end PushPuzzle.PushS.Blocked
