/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.Blocked

/-! First-motion closure of full segments attached to an established blocker. -/

@[expose] public section
namespace PushPuzzle.PushS.Freeze

open PushFS

variable {w h : ℕ}

/-- A straight chain through the full region ends at a known blocker. -/
inductive Ray (S G : Finset (Cell w h)) (d : Direction) : Cell w h → Prop
  | hit {p q} (adjacent : Adjacent d p q) (blocked : q ∈ G) : Ray S G d p
  | extend {p q} (adjacent : Adjacent d p q) (full : q ∈ S)
      (rest : Ray S G d q) : Ray S G d p

/-- Each horizontal and vertical component of the full region has a blocked end. -/
def Anchored (S G : Finset (Cell w h)) : Prop :=
  ∀ d p, p ∈ S → Ray S G d p ∨ Ray S G d.opposite p

private theorem ray_hits_path {S G : Finset (Cell w h)} {d : Direction} {p : Cell w h}
    (ray : Ray S G d p) {n : ℕ} (f : Fin (n + 2) → Cell w h)
    (ha : ∀ i : Fin (n + 1), Adjacent d (f i.castSucc) (f i.succ))
    (hend : f ⟨n + 1, by omega⟩ ∉ S) (hG : ∀ i, f i ∉ G)
    (i : Fin (n + 2)) (hi : f i = p) (hp : p ∈ S) : False := by
  induction ray generalizing i with
  | @hit p q hadj hblock =>
    have hin : i.val < n + 1 := by
      by_contra hn
      have he : i = ⟨n + 1, by omega⟩ := by
        apply Fin.ext
        change i.val = n + 1
        have := i.isLt
        omega
      exact hend (he ▸ hi ▸ hp)
    let j : Fin (n + 1) := ⟨i.val, hin⟩
    have hj : j.castSucc = i := Fin.ext rfl
    have hq : f j.succ = q := (ha j).functional (by simpa only [hj, hi] using hadj)
    exact hG j.succ (hq ▸ hblock)
  | @extend p q hadj hfull rest ih =>
    have hin : i.val < n + 1 := by
      by_contra hn
      have he : i = ⟨n + 1, by omega⟩ := by
        apply Fin.ext
        change i.val = n + 1
        have := i.isLt
        omega
      exact hend (he ▸ hi ▸ hp)
    let j : Fin (n + 1) := ⟨i.val, hin⟩
    have hj : j.castSucc = i := Fin.ext rfl
    have hq : f j.succ = q := (ha j).functional (by simpa only [hj, hi] using hadj)
    exact ih j.succ hq hfull

/-- A legal push cannot touch an anchored full region while avoiding its blockers. -/
theorem run_avoids {S G : Finset (Cell w h)} (hanchor : Anchored S G)
    {B : Board w h} {d : Direction} {s : State w h} {n : ℕ}
    (hs : s.Valid B) (hfull : S ⊆ s.boxes) (run : Run B d s n)
    (hG : ∀ i, run.cell i ∉ G) (i : Fin (n + 2)) : run.cell i ∉ S := by
  intro hi
  have hstart : run.cell 0 ∉ S := fun h => hs.2.2 (run.start ▸ hfull h)
  have hend : run.cell ⟨n + 1, by omega⟩ ∉ S := fun h => run.empty (hfull h)
  rcases hanchor d (run.cell i) hi with ray | ray
  · exact ray_hits_path ray run.cell run.adjacent hend hG i rfl hi
  · have ha : ∀ j : Fin (n + 1),
        Adjacent d.opposite (run.cell j.castSucc.rev) (run.cell j.succ.rev) := by
      intro j
      simpa only [Fin.rev_castSucc, Fin.rev_succ] using (run.adjacent j.rev).reverse
    have he : (fun j : Fin (n + 2) => run.cell j.rev) ⟨n + 1, by omega⟩ ∉ S := by
      simpa only [show (⟨n + 1, by omega⟩ : Fin (n + 2)) = Fin.last (n + 1) from rfl,
        Fin.rev_last] using hstart
    exact ray_hits_path ray (fun j => run.cell j.rev) ha he (fun j => hG j.rev)
      i.rev (by simp only [Fin.rev_rev]) hi

end PushPuzzle.PushS.Freeze
