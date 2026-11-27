/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
public import PushFS.Reduction.PhysicalEdgeOrder
public import PushFS.Reduction.SourceCanonical
public import PushFS.Reduction.StorageIdle
public import Mathlib.Data.List.GetD

/-! Only tiles on the actual reversed source edge change their complete physical canonical inventories. -/

@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory

open Cslib.Complexity.NCL Plan PhysicalBitmap Gadgets Gadgets.Wires SourceCanonical
set_option maxRecDepth 65536
set_option maxHeartbeats 300000
attribute [local irreducible] Raster.width Raster.height StorageAtlas.initial StorageAtlas.board StorageAtlas.profileBoxes

def edgeSource (w : Word) (c : Fin w.compile.edgeCount→Bool) (e : Fin w.compile.edgeCount) : CellPlan.Source:=
  (w,(configBits c,configBits (reverse c e)))

private theorem reverse_other {n : ℕ} (c : Fin n→Bool) (e : Fin n) (i : ℕ) (he : i≠e.val) :
    (configBits (reverse c e)).getD i false=(configBits c).getD i false := by
  by_cases hi : i<n
  · rw [configBits_reverse_getD c e i hi,ite_eq_right he]
  · rw [List.getD_eq_default _ _ (by simpa only [configBits_length] using Nat.le_of_not_gt hi),
      List.getD_eq_default _ _ (by simpa only [configBits_length] using Nat.le_of_not_gt hi)]

private theorem wire_diagonal (k : Catalog.Kind) (a b : Bool) (he : a=b) :
    @Eq (Finset Catalog.Cell) (Catalog.puzzle k a b).initial.boxes (Catalog.puzzle k a b).board.goals := by
  subst b
  exact (Catalog.goals_canonical k a a).symm

theorem gate_diagonal (g : GateTileState) (he : g.core.initial=g.core.target) :
    @Eq (Finset GateTileRouting.C) (GateTileRouting.fullPuzzle g).initial.boxes (GateTileRouting.fullPuzzle g).board.goals := by
  have hh:=GateTileRouting.full_goals_canonical g g.core.initial g.core.initial
  have hg : GateTileRouting.withFlags g g.core.initial g.core.initial=g:=by
    cases g with | mk core incoming pattern rotation=>
      cases core with | mk kind a b=>
        change a=b at he
        subst b
        rfl
  rw [hg] at hh
  exact hh.symm

/-- A physical tile outside the reversed edge's genuine support retains exactly its goal inventory. -/
private theorem off_edge_diagonal (w : Word) (hw : (Word.compile w).Valid) (hP : w.checkPlane=true)
    (hT : w.WellTyped [] [])
    (c : Fin w.compile.edgeCount→Bool) (e : Fin w.compile.edgeCount) (i : Index (edgeSource w c e))
    (hp : ¬HasPoint (Route.edgeSegments (refinedProgram w,e.val)) (position i)) :
    (PhysicalTiles.piece (tile i)).initial.boxes=(PhysicalTiles.piece (tile i)).board.goals := by
  let v:=edgeSource w c e
  have hcode:=payload_eq v i
  have hkey:=payload_key v i
  cases hc : payload v i with
  | inl g=>
    rcases g with ⟨g,a⟩
    rw [hc] at hcode hkey
    obtain ⟨hv,ha⟩:=CellPlan.gate_sound hcode
    obtain ⟨hg,hpos⟩:=Raster.vertexAt_sound hv
    have hs : ∀r : Fin 3,(g.ports.port r).edge≠e.val:=by
      intro r he
      have ht:=vertexRecord_tangent hP hT hg r
      dsimp only at ht
      rw [he] at ht
      apply hp
      rw [←hpos]
      cases hd : (g.ports.port r).dir
      · simp only [hd,Bool.false_eq_true,ite_false] at ht
        exact ht.point
      · simp only [hd,ite_true] at ht
        exact ht.point
    have hf:=gate_unchanged w hw hP hT c e g hg hs
    have hdiag : a.core.initial=a.core.target:=by
      rw [ha]
      exact hf
    change .inl a=tile i at hkey
    rw [←hkey]
    exact gate_diagonal a hdiag
  | inr a=>
    rcases a with ⟨d,k,a,b⟩
    rw [hc] at hcode hkey
    obtain ⟨_,ho,_,ha,hb⟩:=CellPlan.wire_sound hcode
    have hde : d≠e.val:=by
      intro he
      subst d
      exact hp ((Route.edgeSegments_trace _ _ _).mpr (Raster.owner_sound ho))
    have hab : a=b:=ha.trans ((congrArg not (reverse_other c e d hde)).symm.trans hb.symm)
    change .inr (k,a,b)=tile i at hkey
    rw [←hkey]
    change (Catalog.puzzle k a b).initial.boxes=(Catalog.puzzle k a b).board.goals
    exact wire_diagonal k a b hab

/-- A completed traversal already has the whole target inventory; all other real tiles are diagonal. -/
theorem edge_profile_finished (w : Word) (hw : (Word.compile w).Valid) (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    (c : Fin w.compile.edgeCount→Bool) (e : Fin w.compile.edgeCount)
    (f : Fin (Fintype.card (Index (edgeSource w c e)))→Bool)
    (hdone : ∀i : Index (edgeSource w c e),HasPoint (Route.edgeSegments (refinedProgram w,e.val)) (position i)→
      f (numbering (edgeSource w c e) i)=true) :
    (atlas (edgeSource w c e) hP hT).profileBoxes f=(atlas (edgeSource w c e) hP hT).board.goals := by
  apply StorageAtlas.profile_target_of_unchanged
  intro j hj
  let i:=(numbering (edgeSource w c e)).symm j
  apply off_edge_diagonal w hw hP hT c e i
  intro hp
  have hh:=hdone i hp
  rw [Equiv.apply_symm_apply,hj] at hh
  cases hh

end PushPuzzle.PushFS.Reduction.PhysicalInventory
