/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceCodeOrder
public import PushS.FiniteSourcePathSelections
public import PushS.FiniteSourceTurnForward

/-! The real line/turn events and their dynamic preparation order along a source path. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting
open scoped Classical

attribute [local irreducible] codes width height inventory Line.width Line.height LineSite.atoms

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} {P : PathSpec}

/-- Every real instruction is a line or its following perpendicular turn. -/
inductive PathEvent (P : PathSpec)
  | line (i : Fin P.segments.length)
  | turn (i : Fin P.segments.length) (hasTurn : P.hasTurn i.val)
  deriving DecidableEq

namespace PathEvent

def rank : PathEvent P → ℕ
  | .line i => 2*i.val
  | .turn i _ => 2*i.val+1

def code : PathEvent P → PrimitiveCode
  | .line i => .line (P.line i.val)
  | .turn i _ => .turn (P.turn i.val)

theorem member (a : PathEvent P) : a.code ∈ P.codes := by
  cases a with
  | line i => exact P.line_mem_codes i.val i.isLt
  | turn i hi => exact P.turn_mem_codes i.val hi

private theorem ne_of_apart {c d : PrimitiveCode} (H : ActorsApart w hw c d) : c ≠ d := by
  intro he
  subst d
  exact H false (primitiveWitness c) (primitiveWitness c) rfl

/-- The complete geometry gives different literal instructions to different path events. -/
private theorem code_injective (hw : 2 ≤ w) (G : P.Geometry w) : Function.Injective (code
    (P := P)) := by
  intro a b hab
  cases a with
  | line i =>
    cases b with
    | line j =>
      have hij : i = j := by
        by_contra hn
        have hn' : i.val ≠ j.val := fun h => hn (Fin.ext h)
        rcases lt_or_gt_of_ne hn' with hlt | hlt
        · exact ne_of_apart (P.lines_actor_ne w hw G i.val j.val i.isLt j.isLt hlt) hab
        · exact ne_of_apart (P.lines_actor_ne w hw G j.val i.val j.isLt i.isLt hlt) hab.symm
      subst j
      rfl
    | turn _ _ => cases hab
  | turn i hi =>
    cases b with
    | line _ => cases hab
    | turn j hj =>
      have hij : i = j := by
        by_contra hn
        have hn' : i.val ≠ j.val := fun h => hn (Fin.ext h)
        rcases lt_or_gt_of_ne hn' with hlt | hlt
        · exact ne_of_apart (c := .turn (P.turn i.val)) (d := .turn (P.turn j.val)) (P.turns_actor_ne w hw G i.val j.val hi hj hlt) hab
        · exact ne_of_apart (c := .turn (P.turn j.val)) (d := .turn (P.turn i.val)) (P.turns_actor_ne w hw G j.val i.val hj hi hlt) hab.symm
      subst j
      rfl

theorem rank_injective : Function.Injective (rank (P := P)) := by
  intro a b he
  cases a with
  | line i =>
    cases b with
    | line j => have h : i = j := Fin.ext (by change 2*i.val = 2*j.val at he; omega); subst j; rfl
    | turn j hj => change 2*i.val = 2*j.val+1 at he; omega
  | turn i hi =>
    cases b with
    | line j => change 2*i.val+1 = 2*j.val at he; omega
    | turn j hj => have h : i = j := Fin.ext (by change 2*i.val+1 = 2*j.val+1 at he; omega); subst j; rfl

def owner (s : PathSite w hw v P) (a : PathEvent P) : Fin (codes w v).length :=
  s.index a.code a.member

theorem owner_injective (s : PathSite w hw v P) (G : P.Geometry w) : Function.Injective (owner s) := by
  intro a b he
  apply code_injective hw G
  have h := congrArg (fun i => (codes w v).get i) he
  unfold owner at h
  rw [s.get_index,s.get_index] at h
  exact congrArg Prod.snd h

/-- Before the selected event, the physical propagation front has prepared every event on the required side. -/
structure Frontier (s : PathSite w hw v P) (phase : Fin (codes w v).length → Bool) (a : PathEvent P) : Prop where
  owner_phase : ∀ b : PathEvent P, phase (b.owner s) =
    if P.initial then decide (b.rank < a.rank) else decide (a.rank < b.rank)

namespace Frontier

variable {s : PathSite w hw v P} {phase : Fin (codes w v).length → Bool} {a : PathEvent P}

private theorem fresh (H : Frontier s phase a) : phase (a.owner s) = false := by
  rw [H.owner_phase]
  cases P.initial <;> simp

private theorem before (H : Frontier s phase a) (b : PathEvent P) (hb : b.rank < a.rank) :
    phase (b.owner s) = P.initial := by
  rw [H.owner_phase]
  have hn : ¬a.rank < b.rank := by omega
  cases P.initial <;> simp [hb,hn]

theorem after (H : Frontier s phase a) (b : PathEvent P) (hb : a.rank < b.rank) :
    phase (b.owner s) = !P.initial := by
  rw [H.owner_phase]
  have hn : ¬b.rank < a.rank := by omega
  cases P.initial <;> simp [hb,hn]

end Frontier
end PathEvent

namespace PathSite

variable (s : PathSite w hw v P) (G : P.Geometry w)

/-- The complete selected first interface is its already identified actual neighbor. -/
private theorem selection_first (ha : (inventory w hw v).Admissible) (E : s.Endpoints)
    (i : Fin P.segments.length) :
    (s.selection G E i).labels (Line.cutFirstLabel w (s.line i).atoms) = s.firstOwner G E i := by
  apply ha.source_injective
  exact ((s.selection G E i).source _).trans (s.firstOwner_source G E i).symm

/-- An unowned final interface is its already identified actual neighbor. -/
private theorem selection_last (ha : (inventory w hw v).Admissible) (E : s.Endpoints)
    (i : Fin P.segments.length)
    (hl : (s.line i).code.last = false) :
    (s.selection G E i).labels (Line.cutLastLabel w (s.line i).atoms) = s.lastOwner G E i hl := by
  apply ha.source_injective
  exact ((s.selection G E i).source _).trans (s.lastOwner_source G E i hl).symm

/-- The propagation front automatically prepares every internal line interface. -/
theorem line_ready (ha : (inventory w hw v).Admissible) (E : s.Endpoints)
    (phase : Fin (codes w v).length → Bool) (i : Fin P.segments.length)
    (H : PathEvent.Frontier s phase (.line i))
    (hfirst : phase E.first.1 = P.initial)
    (hlast : ∀ h, phase (E.final h).1 = !P.initial) :
    (s.selection G E i).Ready (s.line i) phase := by
  refine ⟨H.fresh,?_,?_⟩
  · rw [s.selection_first G ha E i,s.line_initial]
    unfold firstOwner
    split
    next hz => exact hfirst
    next hz =>
      split
      next ht =>
        rw [show ((s.turn G ⟨i.val-1,by omega⟩ ht).label 1).1 =
            (PathEvent.turn ⟨i.val-1,by omega⟩ ht).owner s from primitiveLabel_owner w hw v _ _ _ _]
        exact H.before _ (by change 2*(i.val-1)+1 < 2*i.val; omega)
      next ht =>
        rw [show ((s.line ⟨i.val-1,by omega⟩).finalLabel _).1 =
            (PathEvent.line ⟨i.val-1,by omega⟩).owner s from primitiveLabel_owner w hw v _ _ _ _]
        exact H.before _ (by change 2*(i.val-1) < 2*i.val; omega)
  · intro hl
    rw [s.selection_last G ha E i hl,s.line_initial]
    unfold lastOwner
    split
    next ht =>
      rw [show ((s.turn G i ht).label 0).1 = (PathEvent.turn i ht).owner s from
        primitiveLabel_owner w hw v _ _ _ _]
      exact H.after _ (by change 2*i.val < 2*i.val+1; omega)
    next ht => exact hlast _

/-- The same physical wave automatically prepares a turn's two real neighboring fixtures. -/
theorem turn_ready (phase : Fin (codes w v).length → Bool) (i : Fin P.segments.length)
    (hi : P.hasTurn i.val) (H : PathEvent.Frontier s phase (.turn i hi)) :
    (TurnStep.mk s G i hi).Ready phase := by
  refine ⟨H.fresh,?_,?_⟩
  · exact H.before (.line i) (by change 2*i.val < 2*i.val+1; omega)
  · exact H.after (.line ⟨i.val+1,hi.1⟩) (by change 2*i.val+1 < 2*(i.val+1); omega)

end PathSite
end PushPuzzle.PushS.FiniteSourceInventory
