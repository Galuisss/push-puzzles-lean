/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourcePathSlots
public import PushS.FiniteSourceLineForward

/-! Complete actual line identities along an emitted path. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting
open scoped Classical

attribute [local irreducible] codes width height Line.width Line.height LineSite.atoms inventory Line.program Line.positions Line.ownedCount

namespace PathSite

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} {P : PathSpec}
variable (s : PathSite w hw v P) (G : P.Geometry w)

-- Complete endpoint fields compare dependent embeddings of the same path.
set_option maxHeartbeats 1000000 in
/-- The two exterior interfaces are actual neighboring compiler-owned identities. -/
structure Endpoints where
  first : (inventory w hw v).PhysicalLabel
  final : P.keepEndpoint = false → (inventory w hw v).PhysicalLabel
  source_first : ∀ h : 0 < P.segments.length,
    (inventory w hw v).source first = (s.line ⟨0,h⟩).actualEmbedding.cells
      (Line.cell w hw (s.line ⟨0,h⟩).atoms P.initial (Line.cutFirstLabel w (s.line ⟨0,h⟩).atoms))
  target_first : ∀ h : 0 < P.segments.length,
    (inventory w hw v).target first = (s.line ⟨0,h⟩).actualEmbedding.cells
      (Line.cell w hw (s.line ⟨0,h⟩).atoms P.target (Line.cutFirstLabel w (s.line ⟨0,h⟩).atoms))
  source_final : ∀ (h : P.keepEndpoint = false) (i : Fin P.segments.length),
    i.val+1 = P.segments.length → (inventory w hw v).source (final h) = (s.line i).actualEmbedding.cells
      (Line.cell w hw (s.line i).atoms P.initial (Line.cutLastLabel w (s.line i).atoms))
  target_final : ∀ (h : P.keepEndpoint = false) (i : Fin P.segments.length),
    i.val+1 = P.segments.length → (inventory w hw v).target (final h) = (s.line i).actualEmbedding.cells
      (Line.cell w hw (s.line i).atoms P.target (Line.cutLastLabel w (s.line i).atoms))

theorem line_first (i : Fin P.segments.length) : (s.line i).code.first = false := rfl

theorem line_last_unowned (i : Fin P.segments.length) (hl : (s.line i).code.last = false)
    (hn : ¬ P.hasTurn i.val) : i.val+1 = P.segments.length ∧ P.keepEndpoint = false := by
  have hi := i.isLt
  have hp : i.val+1 = P.segments.length := by
    by_contra he
    have hnext : i.val+1 < P.segments.length := by omega
    have hh := s.collinear_last_owned i hnext hn
    simp only [hh] at hl
    contradiction
  refine ⟨hp,?_⟩
  simpa only [line,PathSpec.line,lineCodeAt,ownsLast,hp,ite_true] using hl

/-- The real preceding turn or line supplies every internal first interface. -/
noncomputable def firstOwner (E : s.Endpoints) (i : Fin P.segments.length) :
    (inventory w hw v).PhysicalLabel :=
  if hz : i.val = 0 then E.first
  else if ht : P.hasTurn (i.val-1) then
    (s.turn G ⟨i.val-1,by omega⟩ ht).label 1
  else
    (s.line ⟨i.val-1,by omega⟩).finalLabel
      (s.collinear_last_owned ⟨i.val-1,by omega⟩ (by change i.val-1+1 < P.segments.length; omega) ht)

/-- An internal final interface is its literal turn F; an exterior one uses its neighboring endpoint owner. -/
noncomputable def lastOwner (E : s.Endpoints) (i : Fin P.segments.length)
    (hl : (s.line i).code.last = false) : (inventory w hw v).PhysicalLabel :=
  if ht : P.hasTurn i.val then (s.turn G i ht).label 0
  else E.final (s.line_last_unowned i hl ht).2

theorem line_initial (i : Fin P.segments.length) : (s.line i).code.initial = P.initial := rfl

theorem line_target (i : Fin P.segments.length) : (s.line i).code.target = P.target := rfl

attribute [local irreducible] line turn

-- Interface transport compares a dependent line index across the predecessor equation.
set_option maxHeartbeats 1000000 in
theorem firstOwner_source (E : s.Endpoints) (i : Fin P.segments.length) :
    (inventory w hw v).source (s.firstOwner G E i) = (s.line i).actualEmbedding.cells
      (Line.cell w hw (s.line i).atoms (s.line i).code.initial (Line.cutFirstLabel w (s.line i).atoms)) := by
  unfold firstOwner
  split
  next hz =>
    have hi : i = ⟨0,by omega⟩ := Fin.ext hz
    rw [hi]
    simpa only [line_initial] using E.source_first (by omega)
  next hz =>
    have hi : i.val-1+1 = i.val := by omega
    split
    next ht =>
      have he : (⟨i.val-1+1,ht.1⟩ : Fin P.segments.length) = i := Fin.ext hi
      exact (s.outgoing_source_owner G ⟨i.val-1,by omega⟩ ht).trans
        (congrArg (fun j : Fin P.segments.length => (s.line j).actualEmbedding.cells
          (Line.cell w hw (s.line j).atoms (s.line j).code.initial
            (Line.cutFirstLabel w (s.line j).atoms))) he)
    next ht =>
      have hn : i.val-1+1 < P.segments.length := by omega
      have he : (⟨i.val-1+1,hn⟩ : Fin P.segments.length) = i := Fin.ext hi
      exact (s.collinear_source_owner G ⟨i.val-1,by omega⟩ hn ht).trans
        (congrArg (fun j : Fin P.segments.length => (s.line j).actualEmbedding.cells
          (Line.cell w hw (s.line j).atoms (s.line j).code.initial
            (Line.cutFirstLabel w (s.line j).atoms))) he)

set_option maxHeartbeats 1000000 in
theorem firstOwner_target (E : s.Endpoints) (i : Fin P.segments.length) :
    (inventory w hw v).target (s.firstOwner G E i) = (s.line i).actualEmbedding.cells
      (Line.cell w hw (s.line i).atoms (s.line i).code.target (Line.cutFirstLabel w (s.line i).atoms)) := by
  unfold firstOwner
  split
  next hz =>
    have hi : i = ⟨0,by omega⟩ := Fin.ext hz
    rw [hi]
    simpa only [line_target] using E.target_first (by omega)
  next hz =>
    have hi : i.val-1+1 = i.val := by omega
    split
    next ht =>
      have he : (⟨i.val-1+1,ht.1⟩ : Fin P.segments.length) = i := Fin.ext hi
      exact (s.outgoing_target_owner G ⟨i.val-1,by omega⟩ ht).trans
        (congrArg (fun j : Fin P.segments.length => (s.line j).actualEmbedding.cells
          (Line.cell w hw (s.line j).atoms (s.line j).code.target
            (Line.cutFirstLabel w (s.line j).atoms))) he)
    next ht =>
      have hn : i.val-1+1 < P.segments.length := by omega
      have he : (⟨i.val-1+1,hn⟩ : Fin P.segments.length) = i := Fin.ext hi
      exact (s.collinear_target_owner G ⟨i.val-1,by omega⟩ hn ht).trans
        (congrArg (fun j : Fin P.segments.length => (s.line j).actualEmbedding.cells
          (Line.cell w hw (s.line j).atoms (s.line j).code.target
            (Line.cutFirstLabel w (s.line j).atoms))) he)

theorem lastOwner_source (E : s.Endpoints) (i : Fin P.segments.length)
    (hl : (s.line i).code.last = false) :
    (inventory w hw v).source (s.lastOwner G E i hl) = (s.line i).actualEmbedding.cells
      (Line.cell w hw (s.line i).atoms (s.line i).code.initial (Line.cutLastLabel w (s.line i).atoms)) := by
  unfold lastOwner
  split
  next ht => exact s.incoming_source_owner G i ht
  next ht => simpa only [line_initial] using E.source_final _ i (s.line_last_unowned i hl ht).1

theorem lastOwner_target (E : s.Endpoints) (i : Fin P.segments.length)
    (hl : (s.line i).code.last = false) :
    (inventory w hw v).target (s.lastOwner G E i hl) = (s.line i).actualEmbedding.cells
      (Line.cell w hw (s.line i).atoms (s.line i).code.target (Line.cutLastLabel w (s.line i).atoms)) := by
  unfold lastOwner
  split
  next ht => exact s.incoming_target_owner G i ht
  next ht => simpa only [line_target] using E.target_final _ i (s.line_last_unowned i hl ht).1

/-- Every line of the real path has a full selector built from its actual adjacent owners. -/
noncomputable def selection (E : s.Endpoints) (i : Fin P.segments.length) : (s.line i).Selection :=
  LineSite.Selection.of_slots (s.line i) (s.line_first i) (s.firstOwner G E i)
    (s.lastOwner G E i) (s.firstOwner_source G E i) (s.firstOwner_target G E i)
    (s.lastOwner_source G E i) (s.lastOwner_target G E i)

end PathSite
end PushPuzzle.PushS.FiniteSourceInventory
