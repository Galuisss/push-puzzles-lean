/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Gates.Soundness.Relay.Stencils

/-! Actual immobile corner stencils exclude entry by any noncorner physical identity on a successful trajectory. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Gates.Soundness.Relay


open Wires.Soundness

variable {w h : ℕ} {B : Board w h} {p q : Cell w h}

private theorem immobile_path_end (hd : ∀q, ¬Displacement B p q) (hr : StaticReach B p q) : q=p := by
  induction hr with
  | refl=>rfl
  | @tail u v hr hs ih=>exact False.elim (hd v (ih ▸ hs))

variable {I : Instance} {L : Type} [Fintype L] {M : SlotMatching I L}
    {S final : LabelledState L I.width I.height}

/-- SCC conservation excludes every physical source distinct from an actual immobile cell. -/
private theorem avoids_immobile (h : Successful M S final) (i : L) (p : Cell I.width I.height)
    (hd : ∀q,¬Displacement I.board p q) (hne : M.source i≠p) : S.position i≠p := by
  intro he
  have hc:=component_eq_iff.mp (h.component i)
  rw [he] at hc
  exact hne (immobile_path_end hd hc.2)

/-- An immobile cell on an actual label's rail is a genuine one-dimensional upper barrier. -/
theorem below_immobile (h : Successful M S final) (A : AxisTracks I) (axis : Bool) (line : ℕ)
    (i : L) (hi : A.name (M.source i)=lineTag axis line) (p : Cell I.width I.height)
    (hcross : cross axis p=line) (hd : ∀q,¬Displacement I.board p q)
    (hstart : coord axis (M.source i)<coord axis p) : coord axis (S.position i)<coord axis p := by
  obtain ⟨hb,ha,hsol⟩:=h
  induction hb with
  | refl=>exact hstart
  | @tail U V hr hs ih=>
    have hv : Successful M V final := ⟨hr.tail hs,ha,hsol⟩
    have hcoordne : coord axis (V.position i)≠coord axis p := by
      intro he
      have ht:=(hv.line A axis line i hi).trans hcross.symm
      have hecell : V.position i=p := by
        cases axis <;> simp only [coord,cross,Bool.false_eq_true,↓reduceIte] at he ht <;>
          exact Prod.ext (Fin.ext (by assumption)) (Fin.ext (by assumption))
      exact avoids_immobile hv i p hd (fun he=>by rw [he] at hstart; omega) hecell
    have hbound:=step_coord_bound hs axis i
    have hh:=ih (ha.head hs)
    omega

/-- The same actual immobile cell supplies the lower barrier on the opposite open arm. -/
theorem above_immobile (h : Successful M S final) (A : AxisTracks I) (axis : Bool) (line : ℕ)
    (i : L) (hi : A.name (M.source i)=lineTag axis line) (p : Cell I.width I.height)
    (hcross : cross axis p=line) (hd : ∀q,¬Displacement I.board p q)
    (hstart : coord axis p<coord axis (M.source i)) : coord axis p<coord axis (S.position i) := by
  obtain ⟨hb,ha,hsol⟩:=h
  induction hb with
  | refl=>exact hstart
  | @tail U V hr hs ih=>
    have hv : Successful M V final := ⟨hr.tail hs,ha,hsol⟩
    have hcoordne : coord axis (V.position i)≠coord axis p := by
      intro he
      have ht:=(hv.line A axis line i hi).trans hcross.symm
      have hecell : V.position i=p := by
        cases axis <;> simp only [coord,cross,Bool.false_eq_true,↓reduceIte] at he ht <;>
          exact Prod.ext (Fin.ext (by assumption)) (Fin.ext (by assumption))
      exact avoids_immobile hv i p hd (fun he=>by rw [he] at hstart; omega) hecell
    have hbound:=step_coord_bound hs axis i
    have hh:=ih (ha.head hs)
    omega

/-- The two true AND corners have no outgoing static edge in their full literal wall stencils. -/
private theorem corner_immobile (upper : Bool) (q : C) : ¬Displacement (board true ∅)
    (39,if upper then 29 else 90) q := by
  have check : ∀ (upper : Bool) (d : Direction), staticStep (wallTest true) d (39,if upper then 29 else 90)=none := by decide +kernel
  intro hd
  obtain ⟨d,hd⟩:=(displacement_iff_staticStep (wallTest_correct true ∅) _ _).mp hd
  rw [check] at hd
  contradiction

end PushPuzzle.PushFS.Gadgets.Gates.Soundness.Relay
namespace PushPuzzle.PushFS.Gadgets.Gates.Soundness.GateGlyph

open Relay

variable {I : Instance} {L : Type} [Fintype L] {M : SlotMatching I L} {A : AxisTracks I}
    (g : GateGlyph M A true)

/-- The complete local one-cell collar reflects any ambient displacement at either actual protected corner. -/
theorem immobile_corner (upper : Bool) (q : Cell I.width I.height) :
    ¬Displacement I.board ((GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells (39,if upper then 29 else 90)) q := by
  intro hd
  have hi : Interior ((39,if upper then 29 else 90) : C) := by cases upper <;> decide
  obtain ⟨q',_,hd'⟩:=GridEmbedding.displacement_preimage g.dx g.dy g.fit_x g.fit_y g.walls hi hd
  exact corner_immobile upper q' hd'

end PushPuzzle.PushFS.Gadgets.Gates.Soundness.GateGlyph
