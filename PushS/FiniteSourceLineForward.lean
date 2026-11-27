/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourcePrimitiveProfile
public import PushS.FiniteSourceLineGlyph
public import PushS.FiniteRoutingActionContract
public import PushS.FiniteRoutingPreparedSlots
public import PushS.FiniteSourceLegal

/-! Actual complete line selectors and prepared global primitive executions. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting
open scoped Classical

attribute [local irreducible] codes Raster.width Raster.height Line.width Line.height Line.program LineSite.atoms Line.positions Line.ownedPositions Line.ownedCount inventory

private theorem primitiveLabel_index (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (i : Fin (codes w v).length) (c : PrimitiveCode) (hc : ((codes w v).get i).2 = c) (l : c.Labels w) :
    (primitiveLabel w hw v i c hc l).1 = i := by
  subst c
  rfl

private theorem primitiveLabel_surjective (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (i : Fin (codes w v).length) (c : PrimitiveCode) (hc : ((codes w v).get i).2 = c)
    (l : (inventory w hw v).PhysicalLabel) (hi : l.1 = i) :
    ∃ q,primitiveLabel w hw v i c hc q = l := by
  subst c
  rcases l with ⟨j,l⟩
  dsimp at hi
  subst j
  exact ⟨l,rfl⟩

namespace LineSite

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (s : LineSite w hw v)

theorem source_owned_actual (hfirst : s.code.first = false) (l : Line.OwnedLabel w s.atoms false s.code.last) :
    (inventory w hw v).source (s.ownedLabel hfirst l) =
      s.actualEmbedding.cells (Line.ownedCell w hw s.atoms false s.code.last s.code.initial l) := by
  apply (s.orientation.inverse.axis (width w v) (height w v)).geometry.cells.injective
  rw [s.placed_normal]
  exact s.source_owned hfirst l

theorem target_owned_actual (hfirst : s.code.first = false) (l : Line.OwnedLabel w s.atoms false s.code.last) :
    (inventory w hw v).target (s.ownedLabel hfirst l) =
      s.actualEmbedding.cells (Line.ownedCell w hw s.atoms false s.code.last s.code.target l) := by
  apply (s.orientation.inverse.axis (width w v) (height w v)).geometry.cells.injective
  rw [s.placed_normal]
  exact s.target_owned hfirst l

theorem owned_index (hfirst : s.code.first = false) (l : Line.OwnedLabel w s.atoms false s.code.last) :
    (s.ownedLabel hfirst l).1 = s.index := primitiveLabel_index w hw v s.index (.line s.code) s.code_eq _

/-- The literal complete local line uses its real owned stock and its two actual neighboring interface owners. -/
structure Selection (s : LineSite w hw v) where
  first : s.code.first = false
  labels : Line.Label w s.atoms ↪ (inventory w hw v).PhysicalLabel
  source : ∀ l,(inventory w hw v).source (labels l) =
    s.actualEmbedding.cells (Line.cell w hw s.atoms s.code.initial l)
  target : ∀ l,(inventory w hw v).target (labels l) =
    s.actualEmbedding.cells (Line.cell w hw s.atoms s.code.target l)

-- Compare the full dependent selector at both literal endpoint configurations.
set_option maxHeartbeats 1000000 in
/-- Actual endpoint owners and the emitted owned-selector construct the entire physical line selection. -/
def Selection.of_slots (hfirst : s.code.first = false)
    (first : (inventory w hw v).PhysicalLabel)
    (final : s.code.last = false → (inventory w hw v).PhysicalLabel)
    (hsf : (inventory w hw v).source first = s.actualEmbedding.cells
      (Line.cell w hw s.atoms s.code.initial (Line.cutFirstLabel w s.atoms)))
    (htf : (inventory w hw v).target first = s.actualEmbedding.cells
      (Line.cell w hw s.atoms s.code.target (Line.cutFirstLabel w s.atoms)))
    (hsl : ∀ h,(inventory w hw v).source (final h) = s.actualEmbedding.cells
      (Line.cell w hw s.atoms s.code.initial (Line.cutLastLabel w s.atoms)))
    (htl : ∀ h,(inventory w hw v).target (final h) = s.actualEmbedding.cells
      (Line.cell w hw s.atoms s.code.target (Line.cutLastLabel w s.atoms))) : s.Selection := by
  let f := Line.Readout.completeLabels w s.atoms s.code.last first final (s.ownedLabel hfirst)
  have hsource := Line.Readout.completeLabels_slots w hw s.atoms s.code.last s.code.initial
    first final (s.ownedLabel hfirst) s.actualEmbedding (inventory w hw v).source hsf hsl
    (s.source_owned_actual hfirst)
  have htarget := Line.Readout.completeLabels_slots w hw s.atoms s.code.last s.code.target
    first final (s.ownedLabel hfirst) s.actualEmbedding (inventory w hw v).target htf htl
    (s.target_owned_actual hfirst)
  have hinj : Function.Injective f := by
    intro l k he
    apply Line.cell_injective w hw s.atoms s.code.initial
    apply s.actualEmbedding.cells.injective
    exact (hsource l).symm.trans ((congrArg (inventory w hw v).source he).trans (hsource k))
  exact ⟨hfirst,⟨f,hinj⟩,hsource,htarget⟩

/-- Every actual owned label at this literal code index is selected by the emitted line label map. -/
private theorem owned_surjective (hfirst : s.code.first = false) (l :
    (inventory w hw v).PhysicalLabel)
    (hi : l.1 = s.index) : ∃ q : Line.OwnedLabel w s.atoms false s.code.last,s.ownedLabel hfirst q = l := by
  obtain ⟨q,hq⟩ := primitiveLabel_surjective w hw v s.index (.line s.code) s.code_eq l hi
  rcases q with ⟨j,hj⟩
  let q' : Line.OwnedLabel w s.atoms false s.code.last := by
    unfold atoms
    exact ⟨j,by simpa only [hfirst] using hj⟩
  exact ⟨q',by simpa only [ownedLabel,LineSite.label,q',atoms,id,Subtype.coe_mk] using hq⟩

/-- Every owned slot of a complete selector is exactly its actual compiler-owned physical identity. -/
private theorem Selection.owned_eq (H : s.Selection) (ha : (inventory w hw v).Admissible)
    (l : Line.OwnedLabel w s.atoms false s.code.last) : H.labels l.val = s.ownedLabel H.first l := by
  apply ha.source_injective
  exact (H.source l.val).trans (s.source_owned_actual H.first l).symm

/-- The complete selector includes the whole actual primitive owner and its external interface owners. -/
theorem Selection.cover (H : s.Selection) (ha : (inventory w hw v).Admissible) :
    (inventory w hw v).pieceLabels s.index ⊆ Finset.univ.map H.labels := by
  intro l hl
  obtain ⟨q,hq⟩ := s.owned_surjective H.first l ((inventory w hw v).mem_pieceLabels s.index l |>.mp hl)
  exact Finset.mem_map.mpr ⟨q.val,Finset.mem_univ _,(H.owned_eq s ha q).trans hq⟩

/-- The first interface is the literal preceding owner's box, rather than an extra owned line label. -/
private theorem Selection.first_foreign (H : s.Selection) (ha : (inventory w hw v).Admissible) :
    (H.labels (Line.cutFirstLabel w s.atoms)).1 ≠ s.index := by
  intro hi
  obtain ⟨q,hq⟩ := s.owned_surjective H.first _ hi
  have he := H.labels.injective ((H.owned_eq s ha q).trans hq)
  have he' : q.val.val = 0 := congrArg Fin.val he
  have hp : 0 < q.val.val := by simpa only [Bool.false_eq_true,false_or] using q.property.1
  omega

/-- An unowned last interface is its actual following owner's identity. -/
private theorem Selection.last_foreign (H : s.Selection) (ha : (inventory w hw v).Admissible)
    (hl : s.code.last = false) :
    (H.labels (Line.cutLastLabel w s.atoms)).1 ≠ s.index := by
  intro hi
  obtain ⟨q,hq⟩ := s.owned_surjective H.first _ hi
  have he := H.labels.injective ((H.owned_eq s ha q).trans hq)
  have he' : q.val.val = (Line.positions w false s.atoms).length-1 := congrArg Fin.val he
  have hp : q.val.val+1 < (Line.positions w false s.atoms).length := by
    simpa only [hl,Bool.false_eq_true,false_or] using q.property.2
  omega

/-- The finite actual owner-phase conditions needed by the prepared line macro. -/
structure Selection.Ready (H : s.Selection) (phase : Fin (codes w v).length → Bool) : Prop where
  fresh : phase s.index = false
  first_low : phase (H.labels (Line.cutFirstLabel w s.atoms)).1 = s.code.initial
  last_high : ∀ _h : s.code.last = false,
    phase (H.labels (Line.cutLastLabel w s.atoms)).1 = !s.code.initial

private theorem Selection.current_normal (H : s.Selection)
    (phase : Fin (codes w v).length → Bool) (l : Line.Label w s.atoms) :
    PrimitiveProfile.position w hw v phase (H.labels l) = s.actualEmbedding.cells
      (Line.cell w hw s.atoms (if phase (H.labels l).1 then s.code.target else s.code.initial) l) := by
  cases hp : phase (H.labels l).1 with
  | false => simpa only [PrimitiveProfile.position,hp,Bool.false_eq_true,ite_false] using H.source l
  | true => simpa only [PrimitiveProfile.position,hp,ite_true] using H.target l

/-- A normal-phase selector with its actual neighboring owners becomes the exact prepared full-label slot map. -/
private theorem Selection.current_slots (H : s.Selection) (ha : (inventory w hw v).Admissible)
    (phase : Fin (codes w v).length → Bool) (q : Bool) (hq : phase s.index = q)
    (hb : s.code.target = !s.code.initial)
    (hfirst : phase (H.labels (Line.cutFirstLabel w s.atoms)).1 = s.code.initial)
    (hlast : ∀ _h : s.code.last = false,
      phase (H.labels (Line.cutLastLabel w s.atoms)).1 = !s.code.initial) :
    ∀ l,PrimitiveProfile.position w hw v phase (H.labels l) = s.actualEmbedding.cells
      (Line.preparedCell w hw s.atoms s.code.last (if q then s.code.target else s.code.initial) l) := by
  have hcount : 0 < Line.ownedCount w s.atoms := by
    unfold atoms
    exact Line.program_ownedCount_pos _ _ _
  intro l
  by_cases h0 : l.val = 0
  · have he : l = Line.cutFirstLabel w s.atoms := Fin.ext h0
    subst l
    rw [Line.preparedCell_first w hw _ _ _ hcount]
    have hp := H.current_normal s phase (Line.cutFirstLabel w s.atoms)
    rw [hfirst] at hp
    have hh : (if s.code.initial then s.code.target else s.code.initial) = false := by
      rw [hb]
      cases s.code.initial <;> rfl
    simpa only [hh] using hp
  by_cases hl : s.code.last = false ∧ l = Line.cutLastLabel w s.atoms
  · rw [hl.2]
    have hprep := Line.preparedCell_last w hw s.atoms (if q then s.code.target else s.code.initial) hcount
    have hp := H.current_normal s phase (Line.cutLastLabel w s.atoms)
    rw [hlast hl.1] at hp
    have hh : (if !s.code.initial then s.code.target else s.code.initial) = true := by
      rw [hb]
      cases s.code.initial <;> rfl
    rw [hh] at hp
    simpa only [hl.1] using hp.trans (congrArg s.actualEmbedding.cells hprep.symm)
  · let owned := Line.Readout.ownedIndex w s.atoms s.code.last l h0 hl
    have hi : (H.labels l).1 = s.index := by
      change (H.labels owned.val).1 = s.index
      rw [H.owned_eq s ha owned]
      exact s.owned_index H.first owned
    have hp := H.current_normal s phase l
    rw [hi,hq] at hp
    have he := Line.preparedCell_owned w hw s.atoms s.code.last
      (if q then s.code.target else s.code.initial) owned
    exact hp.trans (congrArg s.actualEmbedding.cells he.symm)

/-- A concrete strict-footprint line program updates exactly its actual global owner, retaining both shared interfaces. -/
theorem Selection.run (H : s.Selection) (ha : (inventory w hw v).Admissible)
    (phase : Fin (codes w v).length → Bool) (R : H.Ready s phase)
    (hb : s.code.target = !s.code.initial)
    (B : Board (width w v) (height w v))
    (F : FiniteWireFrame.Frame (Line.Action.active w s.atoms s.code.above s.code.last) s.actualEmbedding B
      (PrimitiveProfile.outside w hw v phase (Finset.univ.map H.labels))) :
    Reachable B (some 1)
      (PrimitiveProfile.state w hw v phase (s.actualEmbedding.cells (Line.outerHub w s.atoms)))
      (PrimitiveProfile.state w hw v (Function.update phase s.index true)
        (s.actualEmbedding.cells (Line.outerHub w s.atoms))) := by
  have hsource := H.current_slots s ha phase false R.fresh hb R.first_low R.last_high
  have htarget := H.current_slots s ha (Function.update phase s.index true) true
    (Function.update_self _ _ _) hb (by
      rw [Function.update_of_ne (H.first_foreign s ha)]
      exact R.first_low) (by
      intro hl
      rw [Function.update_of_ne (H.last_foreign s ha hl)]
      exact R.last_high hl)
  apply PrimitiveProfile.selection_run phase s.index H.labels (H.cover s ha) s.actualEmbedding
    (Line.preparedCell w hw s.atoms s.code.last s.code.initial)
    (Line.preparedCell w hw s.atoms s.code.last s.code.target) hsource htarget B _ _
  exact Line.prepared_program_of_eq w hw s.atoms (segmentLength s.code.segment)
    (s.code.above != s.code.desiredSide) s.code.above s.code.last s.code.initial s.code.target
    (by unfold atoms; rfl) hb s.actualEmbedding F

end LineSite
end PushPuzzle.PushS.FiniteSourceInventory
