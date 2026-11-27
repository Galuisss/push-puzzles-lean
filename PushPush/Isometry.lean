/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Slide
public import PushFS.Isometry

/-! Maximum-slide semantics are invariant under every rectangular grid isometry. -/

@[expose] public section
namespace PushPuzzle.PushPush

open PushFS (Cell State Direction GridIsometry)

variable {w h W H n k : ℕ} {s t : State w h} {d : Direction}

theorem reorient_holes (e : GridIsometry w h W H) (s : State w h) :
    (e.state s).boxesᶜ = s.boxesᶜ.map e.cells.toEmbedding := by
  ext q
  obtain ⟨p, rfl⟩ := e.cells.surjective q
  simp only [Finset.mem_compl, GridIsometry.mem_boxes, Finset.mem_map,
    Equiv.toEmbedding_apply, e.cells.injective.eq_iff, exists_eq_right]

/-- Reorient the entire clear ray, including its true maximum stopping condition. -/
def Slide.reorient (r : Slide d s n k) (e : GridIsometry w h W H) :
    Slide (e.directions d) (e.state s) n k where
  cell i := e.cells (r.cell i)
  start := congrArg e.cells r.start
  adjacent i := (e.adjacent _ _ _).mpr (r.adjacent i)
  occupied i := (e.mem_boxes _ _).mpr (r.occupied i)
  clear i hi := r.clear i ((e.mem_boxes _ _).mp hi)
  stopped q hq := by
    have ha : PushFS.Adjacent d (r.cell ⟨n + k, by omega⟩) (e.cells.symm q) :=
      (e.adjacent _ _ _).mp (by simpa only [Equiv.apply_symm_apply] using hq)
    have hb := (e.mem_boxes s (e.cells.symm q)).mpr (r.stopped _ ha)
    simpa only [Equiv.apply_symm_apply] using hb

private theorem Slide.reorient_boxes (r : Slide d s n k) (e : GridIsometry w h W H) :
    (r.reorient e).boxes = r.boxes.map e.cells.toEmbedding := by
  ext q
  obtain ⟨p, rfl⟩ := e.cells.surjective q
  simp [Slide.boxes, Slide.before, Slide.after, Slide.reorient, GridIsometry.state]

/-- Reorientation retains the original run length, sliding distance, and exact player. -/
private theorem Move.reorient (hm : Move d s t) (e : GridIsometry w h W H) :
    Move (e.directions d) (e.state s) (e.state t) := by
  cases hm with
  | walk hv ha he hb =>
    exact .walk (fun hp => hv ((e.mem_boxes s _).mp hp)) ((e.adjacent _ _ _).mpr ha)
      (fun hp => he ((e.mem_boxes s _).mp hp)) (by simp only [GridIsometry.state, hb])
  | push hv hn hk r hp hb =>
    apply Move.push (fun hp => hv ((e.mem_boxes s _).mp hp)) hn hk (r.reorient e)
    · exact congrArg e.cells hp
    · change t.boxes.map _ = _
      rw [hb, r.reorient_boxes]

theorem Reachable.reorient (hr : Reachable s t) (e : GridIsometry w h W H) :
    Reachable (e.state s) (e.state t) :=
  hr.lift e.state (fun _ _ hm => ⟨e.directions hm.choose, hm.choose_spec.reorient e⟩)

end PushPuzzle.PushPush
