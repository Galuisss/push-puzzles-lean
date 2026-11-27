/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.SourceRails

/-! Actual immobile walls bound physical source rails on any successful path. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog

open Soundness

variable {I : Instance} {L : Type} [Fintype L] {M : SlotMatching I L}

private theorem immobile_path_end {p q : PushFS.Cell I.width I.height}
    (hd : ∀q,¬Displacement I.board p q) (hr : StaticReach I.board p q) : q=p := by
  induction hr with
  | refl=>rfl
  | @tail u v hr hs ih=>exact False.elim (hd v (ih ▸ hs))

private theorem avoids_immobile {S final : LabelledState L I.width I.height}
    (h : Successful M S final)
    (i : L) (p : PushFS.Cell I.width I.height) (hd : ∀q,¬Displacement I.board p q)
    (hne : M.source i≠p) : S.position i≠p := by
  intro he
  have hc:=component_eq_iff.mp (h.component i)
  rw [he] at hc
  exact hne (immobile_path_end hd hc.2)

namespace SourceRail

variable {axis : Bool} {line : ℕ} (r : SourceRail M axis line)

/-- A label cannot cross a real immobile point on its actual source rail. -/
theorem above_immobile {S final : LabelledState L I.width I.height} (h : Successful M S final)
    (cert : Certificate I) (i : L)
    (hi : component I.board (M.source i)=component I.board (M.source r.anchor))
    (p : PushFS.Cell I.width I.height) (hcross : cross axis p=line)
    (hd : ∀q,¬Displacement I.board p q)
    (hstart : coord axis p<coord axis (M.source i)) : coord axis p<coord axis (S.position i) := by
  obtain ⟨hb,ha,hsol⟩:=h
  induction hb with
  | refl=>exact hstart
  | @tail U V hr hs ih=>
    have hv : Successful M V final := ⟨hr.tail hs,ha,hsol⟩
    have hne : coord axis (V.position i)≠coord axis p := by
      intro he
      have ht:=(r.current_line hv cert i hi).trans hcross.symm
      have hecell : V.position i=p := by
        cases axis <;> simp only [coord,cross,Bool.false_eq_true,↓reduceIte] at he ht <;>
          exact Prod.ext (Fin.ext (by assumption)) (Fin.ext (by assumption))
      exact avoids_immobile hv i p hd (fun he=>by rw [he] at hstart; omega) hecell
    have hbound:=step_coord_bound hs axis i
    have hh:=ih (ha.head hs)
    omega

end SourceRail
end PushPuzzle.PushFS.Gadgets.Wires.Catalog
