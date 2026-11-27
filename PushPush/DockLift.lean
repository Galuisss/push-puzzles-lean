/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.DockFrame
public import PushPush.ReadPath
import all Push.CornerDockLift
import all Push.CornerDockReverse

/-! Lift maximum rays into the dock while preserving their stopping cells. -/

@[expose] public section
namespace PushPuzzle.PushPush.CornerDock

open PushFS (Cell State Direction Adjacent)

variable (r : Push.CornerDock.Input)

theorem outside_neighbor_full (s : State r.width r.height) {p : Cell r.width r.height}
    {q : Cell r.outputWidth r.outputHeight} {d : Direction}
    (hsafe : d = .west → p ≠ r.sourceGoal)
    (ha : Adjacent d (r.embed p) q) (hout : ¬(2 ≤ q.1.val ∧ q.2.val < r.height)) :
    q ∈ (r.liftState s).boxes := by
  apply Finset.mem_union_right
  apply Finset.mem_compl.mpr
  intro hh
  rcases Finset.mem_union.mp hh with hh | hh
  · obtain ⟨a, _, he⟩ := Finset.mem_image.mp hh
    apply hout
    rw [← he]
    exact ⟨by change 2 ≤ a.1.val + 2; omega, a.2.isLt⟩
  · have hpx := p.1.isLt
    have hpy := p.2.isLt
    cases d with
    | north =>
      simp only [Adjacent, Push.CornerDock.Input.embed, Fin.ext_iff] at ha
      exact hout ⟨by omega, by omega⟩
    | east =>
      simp only [Adjacent, Push.CornerDock.Input.embed, Fin.ext_iff] at ha
      exact hout ⟨by omega, by omega⟩
    | south =>
      have hx : q.1.val < 2 := by
        rcases Finset.mem_insert.mp hh with he | he
        · rw [he]; change 1 < 2; omega
        · exact (Finset.mem_filter.mp he).2.1
      simp only [Adjacent, Push.CornerDock.Input.embed, Fin.ext_iff] at ha
      omega
    | west =>
      have hqy : q.2.val < r.height := by
        have := congrArg Fin.val ha.2
        change q.2.val = p.2.val at this
        omega
      have he := r.auxiliary_on_source_row q hh hqy
      apply hsafe rfl
      apply Prod.ext <;> apply Fin.ext
      · have hx := ha.1
        rw [he] at hx
        change 1 + 1 = p.1.val + 2 at hx
        change p.1.val = 0
        omega
      · exact (congrArg Fin.val ha.2).symm.trans (congrArg (fun z => z.2.val) he)

variable {s t : State r.width r.height} {d : Direction} {n k : ℕ}

def liftSlide (slide : Slide d s n k)
    (hsafe : d = .west → slide.cell ⟨n + k, by omega⟩ ≠ r.sourceGoal) :
    Slide d (r.liftState s) n k where
  cell i := r.embed (slide.cell i)
  start := congrArg r.embed slide.start
  adjacent i := (embed_adjacent r d _ _).mpr (slide.adjacent i)
  occupied i := (liftState_mem_boxes r s _).mpr (slide.occupied i)
  clear i hi := slide.clear i ((liftState_mem_boxes r s _).mp hi)
  stopped q hq := by
    by_cases hi : 2 ≤ q.1.val ∧ q.2.val < r.height
    · let p := cropCell r q hi
      have he : r.embed p = q := embed_cropCell r q hi
      have ha := (embed_adjacent r d _ _).mp (he ▸ hq)
      exact he ▸ (liftState_mem_boxes r s p).mpr (slide.stopped p ha)
    · exact outside_neighbor_full r s hsafe hq hi

private theorem liftSlide_before (slide : Slide d s n k)
    (hsafe : d = .west → slide.cell ⟨n + k, by omega⟩ ≠ r.sourceGoal) :
    (liftSlide r slide hsafe).before = slide.before.image r.embed := by
  simp only [Slide.before, liftSlide, Finset.image_image, Function.comp_def]

private theorem liftSlide_after (slide : Slide d s n k)
    (hsafe : d = .west → slide.cell ⟨n + k, by omega⟩ ≠ r.sourceGoal) :
    (liftSlide r slide hsafe).after = slide.after.image r.embed := by
  simp only [Slide.after, liftSlide, Finset.image_image, Function.comp_def]

theorem liftSlide_boxes (slide : Slide d s n k)
    (hsafe : d = .west → slide.cell ⟨n + k, by omega⟩ ≠ r.sourceGoal)
    (hb : t.boxes = slide.boxes) : (r.liftState t).boxes = (liftSlide r slide hsafe).boxes := by
  ext q
  by_cases hi : 2 ≤ q.1.val ∧ q.2.val < r.height
  · let p := cropCell r q hi
    have he : r.embed p = q := embed_cropCell r q hi
    rw [← he]
    simp only [liftState_mem_boxes r, Slide.boxes, Finset.mem_union, Finset.mem_sdiff,
      liftSlide_before, liftSlide_after, Finset.mem_image, r.embed_injective.eq_iff, exists_eq_right, hb]
  · have hoff (S : Finset (Cell r.width r.height)) : q ∉ S.image r.embed := by
      intro hh
      obtain ⟨p, _, he⟩ := Finset.mem_image.mp hh
      apply hi
      rw [← he]
      exact ⟨by change 2 ≤ p.1.val + 2; omega, p.2.isLt⟩
    simp only [Slide.boxes, Finset.mem_union, Finset.mem_sdiff, liftSlide_before,
      liftSlide_after, hoff, not_false_eq_true, and_true, or_false]
    exact liftState_outside r t s q hi

/-- Every committed north-reading path lifts into the dock with the same maximum distances. -/
theorem lift_readPath (hr : ReadPath s t) : Reachable (r.liftState s) (r.liftState t) := by
  apply hr.lift r.liftState
  intro a b hm
  obtain ⟨d, hm, hd⟩ := hm
  cases hm with
  | walk hv ha he hb =>
    exact ⟨d, .walk (fun hh => hv ((liftState_mem_boxes r a _).mp hh))
      ((embed_adjacent r d _ _).mpr ha)
      (fun hh => he ((liftState_mem_boxes r a _).mp hh)) (by
        simp only [Push.CornerDock.Input.liftState, PushFS.GridEmbedding.extend, hb])⟩
  | push hv hn hk slide hp hb =>
    have hd : d = .north := hd.resolve_right (by
      intro heq
      have hh := slide.occupied ⟨0, hn⟩
      exact slide.player_empty hn hk (by simpa only [← hb, heq] using hh))
    subst d
    have hsafe : Direction.north = .west → slide.cell (Fin.last _) ≠ r.sourceGoal := by intro h; cases h
    exact ⟨.north, .push (fun hh => hv ((liftState_mem_boxes r a _).mp hh)) hn hk
      (liftSlide r slide hsafe) (congrArg r.embed hp) (liftSlide_boxes r slide hsafe hb)⟩

end PushPuzzle.PushPush.CornerDock
