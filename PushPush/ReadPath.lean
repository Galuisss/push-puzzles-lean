/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.UnitExpansion

/-! The committed reader uses only walks and northward maximum slides. -/

@[expose] public section
namespace PushPuzzle.PushPush

open PushFS (Cell State Direction Adjacent)

variable {w h : ℕ} {s t : State w h}

/-- A northward push or a walk in any direction. -/
def ReadStep (s t : State w h) : Prop :=
  ∃ d, Move d s t ∧ (d = .north ∨ t.boxes = s.boxes)

abbrev ReadPath (s t : State w h) := Relation.ReflTransGen ReadStep s t

theorem ReadPath.reachable (hr : ReadPath s t) : Reachable s t :=
  Relation.ReflTransGen.mono (fun _ _ h => ⟨h.choose, h.choose_spec.1⟩) _ _ hr

theorem ReadPath.valid (hr : ReadPath s t) (hs : s.player ∉ s.boxes) : t.player ∉ t.boxes :=
  hr.reachable.valid hs

private theorem ReadPath.walk {d : Direction} (hv : s.player ∉ s.boxes)
    (ha : Adjacent d s.player t.player) (he : t.player ∉ s.boxes) (hb : t.boxes = s.boxes) :
    ReadPath s t := .single ⟨d, .walk hv ha he hb, Or.inr hb⟩

theorem Slide.advance_readPath {n k : ℕ} (r : Slide .north s n k)
    (hn : 0 < n) (hk : 0 < k) (hv : s.player ∉ s.boxes)
    (i : Fin (k + 1)) (hi : 0 < i.val) : ReadPath s (r.returnState i) := by
  induction i using Fin.induction with
  | zero => simp at hi
  | succ i ih =>
    by_cases hz : i.val = 0
    · have he : (⟨i.succ.val, by omega⟩ : Fin (n + k + 1)) = ⟨1, by omega⟩ := by
        apply Fin.ext
        change i.val + 1 = 1
        omega
      exact .single ⟨.north, Move.push hv hn hk r
        (by change r.cell _ = _; rw [he]) rfl, Or.inl rfl⟩
    · exact (ih (by change 0 < i.val; omega)).trans (ReadPath.walk
        (r.return_empty hv i.castSucc) (r.adjacent ⟨i.val, by omega⟩)
        (r.return_empty hv i.succ) rfl)

end PushPuzzle.PushPush
