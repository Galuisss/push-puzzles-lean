/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingPortClaim

public import PushS.FiniteSourceInitials
public import PushFS.Reduction.SourceCanonical
import Mathlib.Tactic.FinCases

/-! Pure source metadata for the changed support of the actual finite-force primitive inventory. -/

public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction Gadgets.Wires

theorem PrimitiveCode.matching_samePhase (w : ℕ) (hw : 2 ≤ w) (c : PrimitiveCode) (hc : c.SamePhase)
    (l : c.Labels w) : (c.matching w hw).source l = (c.matching w hw).target l := by
  cases c with
  | core g =>
    rcases g with ⟨⟨kind,s,t⟩,incoming,pattern,rotation⟩
    change s = t at hc
    subst t
    cases kind <;> rfl
  | line c =>
    rcases c with ⟨segment,above,first,last,a,b,desiredSide⟩
    change a = b at hc
    subst b
    rfl
  | turn c =>
    rcases c with ⟨incoming,outgoing,corner,a,b⟩
    change a = b at hc
    subst b
    rfl

end PushPuzzle.PushS.FiniteRouting

namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting Gadgets.Wires
open Cslib.Complexity.NCL Plan SourceCanonical

attribute [local irreducible] codes width height Raster.width Raster.height Raster.vertexAt Raster.owner Raster.wireAt

/-- The actual source table whose two endpoint inventories differ by one original NCL edge. -/
@[expose] def oneEdgeSource (word : Word) (c : Fin word.compile.edgeCount → Bool) (e : Fin word.compile.edgeCount) :
    CellPlan.Source := (word,(configBits c,configBits (reverse c e)))

/-- A literal emitted entry belongs to the instruction selected at its own exact source coordinate. -/
private theorem edge_code_local (w : ℕ) (v : CellPlan.Source) {q : GridRouting.Point × PrimitiveCode}
    (hq : q ∈ codes w v) : q.2 ∈ localCodes w (CellPlan.cell (v,q.1)) := by
  unfold codes at hq
  obtain ⟨entry,hentry,hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hq
  have he : entry.2 = CellPlan.cell (v,entry.1) := by
    simp only [CellPlan.cells,List.mem_flatMap,List.mem_map] at hentry
    obtain ⟨y,_,x,_,rfl⟩ := hentry
    rfl
  exact he ▸ hc

private theorem reverse_other {n : ℕ} (c : Fin n → Bool) (e : Fin n) (i : ℕ) (he : i ≠ e.val) :
    (configBits (reverse c e)).getD i false = (configBits c).getD i false := by
  by_cases hi : i < n
  · rw [configBits_reverse_getD c e i hi,ite_eq_right he]
  · rw [List.getD_eq_default _ _ (by simpa only [configBits_length] using Nat.le_of_not_gt hi),
      List.getD_eq_default _ _ (by simpa only [configBits_length] using Nat.le_of_not_gt hi)]

private theorem vertex_off_edge (word : Word) (hP : word.checkPlane = true) (hT : word.WellTyped [] [])
    (e : Fin word.compile.edgeCount) (g : VertexData) (hg : g ∈ vertexRecords word)
    (hp : ¬HasPoint (Route.edgeSegments (refinedProgram word,e.val)) (refinePoint g.point)) :
    ∀ r : Fin 3,(g.ports.port r).edge ≠ e.val := by
  intro r he
  have ht := vertexRecord_tangent hP hT hg r
  dsimp only at ht
  rw [he] at ht
  cases hd : (g.ports.port r).dir
  · simp only [hd,Bool.false_eq_true,ite_false] at ht
    exact hp ht.point
  · simp only [hd,ite_true] at ht
    exact hp ht.point

/-- Off the actual reversed edge, every new emitted primitive keeps its literal normal phase. -/
private theorem localCode_off_edge_samePhase (w : ℕ) (word : Word) (hG : word.compile.Valid)
    (hP : word.checkPlane = true) (hT : word.WellTyped [] [])
    (c : Fin word.compile.edgeCount → Bool) (e : Fin word.compile.edgeCount)
    (p : GridRouting.Point)
    (hp : ¬HasPoint (Route.edgeSegments (refinedProgram word,e.val)) p)
    {code : PrimitiveCode} (hc : code ∈ localCodes w (CellPlan.cell (oneEdgeSource word c e,p))) :
    code.SamePhase := by
  cases hv : Raster.vertexAt (word,p) with
  | some g =>
    obtain ⟨hg,hpos⟩ := Raster.vertexAt_sound hv
    have hs := vertex_off_edge word hP hT e g hg (by simpa only [hpos] using hp)
    have hflags := gate_unchanged word hG hP hT c e g hg hs
    simp only [CellPlan.cell,oneEdgeSource,hv,Option.elim_some,localCodes,Sum.elim_inl] at hc
    exact gateCodes_samePhase w _ hflags hc
  | none =>
    simp only [CellPlan.cell,oneEdgeSource,hv,Option.elim_none,CellPlan.ordinary] at hc
    cases ho : Raster.owner (word,p) with
    | none => simp only [ho,Option.elim_none,localCodes,List.not_mem_nil] at hc
    | some f =>
      have hf : f ≠ e.val := by
        intro he
        subst f
        exact hp ((Route.edgeSegments_trace _ _ _).mpr (Raster.owner_sound ho))
      have hphase := congrArg not (reverse_other c e f hf)
      simp only [ho,Option.elim_some,CellPlan.wireData] at hc
      cases hk : Raster.wireAt (word,(f,p)) with
      | none => simp only [hk,Option.map_none,localCodes,Option.elim_none,List.not_mem_nil] at hc
      | some kind =>
        simp only [hk,Option.map_some,localCodes,Option.elim_some,Sum.elim_inr] at hc
        rw [hphase] at hc
        exact wireCodes_samePhase w kind _ hc

/-- The complete actual primitive table changes phases only on the reversed source edge's real support. -/
private theorem code_off_edge_samePhase (w : ℕ) (word : Word) (hG : word.compile.Valid)
    (hP : word.checkPlane = true) (hT : word.WellTyped [] [])
    (c : Fin word.compile.edgeCount → Bool) (e : Fin word.compile.edgeCount)
    {q : GridRouting.Point × PrimitiveCode} (hq : q ∈ codes w (oneEdgeSource word c e))
    (hp : ¬HasPoint (Route.edgeSegments (refinedProgram word,e.val)) q.1) : q.2.SamePhase :=
  localCode_off_edge_samePhase w word hG hP hT c e q.1 hp (edge_code_local w _ hq)

/-- Every literal global label off this one edge has identical actual source and target cells. -/
theorem off_edge_source_eq_target (w : ℕ) (hw : 2 ≤ w) (word : Word) (hG : word.compile.Valid)
    (hP : word.checkPlane = true) (hT : word.WellTyped [] [])
    (c : Fin word.compile.edgeCount → Bool) (e : Fin word.compile.edgeCount)
    (l : (inventory w hw (oneEdgeSource word c e)).PhysicalLabel)
    (hp : ¬HasPoint (Route.edgeSegments (refinedProgram word,e.val))
      ((codes w (oneEdgeSource word c e)).get l.1).1) :
    (inventory w hw (oneEdgeSource word c e)).source l =
      (inventory w hw (oneEdgeSource word c e)).target l := by
  apply congrArg ((inventory w hw (oneEdgeSource word c e)).embedding l.1).cells
  exact PrimitiveCode.matching_samePhase w hw _
    (code_off_edge_samePhase w word hG hP hT c e (List.get_mem _ _) hp) l.2

/-- Exactly the arms naming the reversed original edge change their actual physical phase. -/
private theorem gate_arm_phase_equal (word : Word) (hG : word.compile.Valid)
    (hP : word.checkPlane = true) (hT : word.WellTyped [] [])
    (c : Fin word.compile.edgeCount → Bool) (e : Fin word.compile.edgeCount)
    (g : VertexData) (hg : g ∈ vertexRecords word) (r : Fin 3) (hr : (g.ports.port r).edge ≠ e.val) :
    portInflow (gateTileState (g,(oneEdgeSource word c e).2)).core.initial.left
      (gateTileState (g,(oneEdgeSource word c e).2)).core.initial.upper
      (gateTileState (g,(oneEdgeSource word c e).2)).core.initial.right r =
    portInflow (gateTileState (g,(oneEdgeSource word c e).2)).core.target.left
      (gateTileState (g,(oneEdgeSource word c e).2)).core.target.upper
      (gateTileState (g,(oneEdgeSource word c e).2)).core.target.right r := by
  dsimp only [gateTileState,oneEdgeSource]
  rw [portInflow_eq_gateClaim,portInflow_eq_gateClaim]
  simpa only [hr,ite_false] using (gateClaim_reverse word hG hP hT c e g hg r).symm

/-- All actual line and turn inventories on every other arm of an affected gate stay fixed. -/
theorem gate_arm_code_samePhase (w : ℕ) (word : Word) (hG : word.compile.Valid)
    (hP : word.checkPlane = true) (hT : word.WellTyped [] [])
    (c : Fin word.compile.edgeCount → Bool) (e : Fin word.compile.edgeCount)
    (g : VertexData) (hg : g ∈ vertexRecords word) (r : Fin 3) (hr : (g.ports.port r).edge ≠ e.val)
    {code : PrimitiveCode}
    (hc : code ∈ pathCodes (armRoute w (gateTileState (g,(oneEdgeSource word c e).2)) r)
      (coreSide g.ports.isAND r) ((gateTileState (g,(oneEdgeSource word c e).2)).incoming.get r)
      (!((gateTileState (g,(oneEdgeSource word c e).2)).incoming.get r))
      (portInflow (gateTileState (g,(oneEdgeSource word c e).2)).core.initial.left
        (gateTileState (g,(oneEdgeSource word c e).2)).core.initial.upper
        (gateTileState (g,(oneEdgeSource word c e).2)).core.initial.right r)
      (portInflow (gateTileState (g,(oneEdgeSource word c e).2)).core.target.left
        (gateTileState (g,(oneEdgeSource word c e).2)).core.target.upper
        (gateTileState (g,(oneEdgeSource word c e).2)).core.target.right r)) : code.SamePhase := by
  rw [gate_arm_phase_equal word hG hP hT c e g hg r hr] at hc
  exact pathCodes_samePhase _ _ _ _ _ hc

end PushPuzzle.PushS.FiniteSourceInventory
