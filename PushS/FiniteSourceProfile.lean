/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceEdgeMetadata
public import PushFS.Reduction.InventorySplit
public import PushS.FiniteSourceOwnership
public import PushS.FiniteSourcePlayer

/-! Actual primitive-labelled intermediate inventories for a single source-edge traversal. -/

@[expose] public section
namespace PushPuzzle.PushFS

variable {W H : ℕ}

/-- The real move semantics depends only on the wall set. -/
private theorem Move.of_walls_eq {B B' : Board W H} (hw : B.walls = B'.walls)
    {cap : Option ℕ} {d : Direction} {s t : State W H} (h : Move B cap d s t) : Move B' cap d s t := by
  have hv (u : State W H) (hu : u.Valid B) : u.Valid B' := by
    simpa only [State.Valid,← hw] using hu
  cases h with
  | walk hs ha hf he hb => exact .walk (hv _ hs) ha (by simpa only [← hw] using hf) he hb
  | push hs hn hc run hp hb =>
    exact .push (hv _ hs) hn hc {
      cell := run.cell
      start := run.start
      adjacent := run.adjacent
      occupied := run.occupied
      empty := run.empty
      floor i := by simpa only [← hw] using run.floor i } hp hb

/-- Retargeting a fixed wall set retains every actual finite push execution. -/
theorem Reachable.of_walls_eq {B B' : Board W H} (hw : B.walls = B'.walls)
    {cap : Option ℕ} {s t : State W H} (h : Reachable B cap s t) : Reachable B' cap s t := by
  induction h with
  | refl => exact .refl
  | tail hr hs ih =>
    obtain ⟨d,hm⟩ := hs
    exact ih.tail ⟨d,hm.of_walls_eq hw⟩

end PushPuzzle.PushFS

namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting Gadgets.Wires
open Cslib.Complexity.NCL Plan SourceCanonical
open scoped Classical

attribute [local irreducible] codes Raster.width Raster.height

/-- The source cell owning this actual primitive and all its physical labels. -/
def ownerCell (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source) (l : (inventory w hw v).PhysicalLabel) : GridRouting.Point :=
  ((codes w v).get l.1).1

/-- Every physical identity occupies its literal source or target cell according to its source tile's phase. -/
def profilePosition (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (phase : GridRouting.Point → Bool) (l : (inventory w hw v).PhysicalLabel) : Cell (width w v) (height w v) :=
  if phase (ownerCell w hw v l) then (inventory w hw v).target l else (inventory w hw v).source l

/-- The complete intermediate physical stock of the actual emitted primitive table. -/
noncomputable def profileBoxes (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (phase : GridRouting.Point → Bool) : Finset (Cell (width w v) (height w v)) :=
  Finset.univ.image (profilePosition w hw v phase)

/-- Actual intermediate stock with the compiler's reserved external player cell. -/
noncomputable def profileState (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (phase : GridRouting.Point → Bool) : State (width w v) (height w v) :=
  ⟨(inventory w hw v).player,profileBoxes w hw v phase⟩

private theorem profile_initial (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source) :
    profileState w hw v (fun _ => false) = (inventory w hw v).initial := by
  apply State.ext
  · rfl
  · change Finset.univ.image (profilePosition w hw v (fun _ => false)) =
      Finset.univ.image (inventory w hw v).source
    rfl

private theorem profile_target (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source) :
    profileState w hw v (fun _ => true) = ⟨(inventory w hw v).player,(inventory w hw v).board.goals⟩ := by
  apply State.ext
  · rfl
  · change Finset.univ.image (profilePosition w hw v (fun _ => true)) =
      Finset.univ.image (inventory w hw v).target
    rfl

/-- Once the real edge support has advanced, every actual physical identity occupies its complete target cell. -/
theorem edge_profile_finished (w : ℕ) (hw : 2 ≤ w) (word : Word) (hG : word.compile.Valid)
    (hP : word.checkPlane = true) (hT : word.WellTyped [] [])
    (c : Fin word.compile.edgeCount → Bool) (e : Fin word.compile.edgeCount)
    (phase : GridRouting.Point → Bool)
    (hphase : ∀ p,HasPoint (Route.edgeSegments (refinedProgram word,e.val)) p → phase p = true) :
    profileState w hw (oneEdgeSource word c e) phase =
      profileState w hw (oneEdgeSource word c e) (fun _ => true) := by
  apply State.ext
  · rfl
  · change Finset.univ.image (profilePosition w hw (oneEdgeSource word c e) phase) =
      Finset.univ.image (profilePosition w hw (oneEdgeSource word c e) (fun _ => true))
    congr 1
    funext l
    change profilePosition _ _ _ phase l = profilePosition _ _ _ (fun _ => true) l
    unfold profilePosition
    simp only [ite_true]
    by_cases hp : HasPoint (Route.edgeSegments (refinedProgram word,e.val))
        (ownerCell w hw (oneEdgeSource word c e) l)
    · rw [hphase _ hp]
      rfl
    · have he := off_edge_source_eq_target w hw word hG hP hT c e l hp
      simp only [he,ite_self]

/-- The starting profile is the actual canonical state with the caller's fixed target. -/
theorem edge_profile_initial_canonical (w : ℕ) (hw : 2 ≤ w) (word : Word) (target : List Bool)
    (c : Fin word.compile.edgeCount → Bool) (e : Fin word.compile.edgeCount) :
    profileState w hw (oneEdgeSource word c e) (fun _ => false) =
      canonicalState w hw word target (configBits c) := by
  rw [profile_initial]
  apply State.ext
  · rfl
  · exact initials_rephase w hw word (configBits (reverse c e)) target (configBits c)

/-- The finished profile is the next actual canonical state on that same fixed target board. -/
theorem edge_profile_target_canonical (w : ℕ) (hw : 2 ≤ w) (word : Word) (target : List Bool)
    (c : Fin word.compile.edgeCount → Bool) (e : Fin word.compile.edgeCount) :
    profileState w hw (oneEdgeSource word c e) (fun _ => true) =
      canonicalState w hw word target (configBits (reverse c e)) := by
  rw [profile_target]
  apply State.ext
  · rfl
  · exact (targets_rephase w hw word (configBits c) (configBits (reverse c e)) (configBits (reverse c e))).trans
      ((initial_boxes_eq_targets w hw word (configBits (reverse c e))).symm.trans
        (initials_rephase w hw word (configBits (reverse c e)) target (configBits (reverse c e))))

end PushPuzzle.PushS.FiniteSourceInventory
