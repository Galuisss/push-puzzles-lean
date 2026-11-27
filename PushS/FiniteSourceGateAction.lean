/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceGateConcreteSteps

/-! A genuine legal single-port change selects its complete actual thick-gate action. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting FiniteGeometry FiniteGateState FiniteGateSelected
open FiniteGateCanonicalAccess FiniteGateFaceBridge
open scoped Classical

attribute [local irreducible] codes width height FiniteGeometry.side

namespace GatePhysicalContext

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} {c : CoreSite w hw v} {role : Fin 3}
  {p : PathSite w hw v (armSpec w c.gate role)} {B : Board (width w v) (height w v)}

/-- The unchanged flags and the flipped flag of one selected physical port. -/
private inductive PortChange (role : Fin 3) (initial final : Gadgets.Gates.Signals) : Prop
  | left (hr : role = 0) (a b d : Bool) (hi : initial = ⟨a,b,d⟩) (hf : final = ⟨!a,b,d⟩)
  | upper (hr : role = 1) (a b d : Bool) (hi : initial = ⟨a,b,d⟩) (hf : final = ⟨a,!b,d⟩)
  | right (hr : role = 2) (a b d : Bool) (hi : initial = ⟨a,b,d⟩) (hf : final = ⟨a,b,!d⟩)

private theorem portChange_of_flip (role : Fin 3) (initial final : Gadgets.Gates.Signals)
    (hs : Gadgets.Gates.singleChange initial final)
    (hb : portInflow final.left final.upper final.right role =
      !portInflow initial.left initial.upper initial.right role) : PortChange role initial final := by
  rcases initial with ⟨a,b,d⟩
  rcases final with ⟨a',b',d'⟩
  fin_cases role <;> cases a <;> cases b <;> cases d <;> cases a' <;> cases b' <;> cases d' <;>
    simp [Gadgets.Gates.singleChange,portInflow] at hs hb
  all_goals first
    | exact .left rfl _ _ _ rfl rfl
    | exact .upper rfl _ _ _ rfl rfl
    | exact .right rfl _ _ _ rfl rfl

private theorem selected_change (C : GatePhysicalContext c role p B)
    (hs : Gadgets.Gates.singleChange c.gate.core.initial c.gate.core.target) :
    PortChange role c.gate.core.initial c.gate.core.target :=
  portChange_of_flip role _ _ hs C.reversed

private theorem and_step (C : GatePhysicalContext c role p B) (hg : c.gate.core.isAND = true)
    (hi : Gadgets.Gates.legal true c.gate.core.initial) (hf : Gadgets.Gates.legal true c.gate.core.target)
    (hs : Gadgets.Gates.singleChange c.gate.core.initial c.gate.core.target) :
    AndStep w c.embedding B C.outside c.gate.core.initial c.gate.core.target := by
  rcases C.selected_change hs with ⟨hr,a,b,d,hiE,hfE⟩ | ⟨hr,a,b,d,hiE,hfE⟩ | ⟨hr,a,b,d,hiE,hfE⟩
  · subst role
    simp only [hiE,hfE] at hi hf ⊢
    cases a <;> cases b <;> cases d <;> simp [Gadgets.Gates.legal] at hi hf
    all_goals first
      | exact and_left_on (w:=w) (hw:=hw) (v:=v) (c:=c) (B:=B) (p:=p) C hg _
      | exact and_left_off (w:=w) (hw:=hw) (v:=v) (c:=c) (B:=B) (p:=p) C hg _ _
  · subst role
    simp only [hiE,hfE] at hi hf ⊢
    cases a <;> cases b <;> cases d <;> simp [Gadgets.Gates.legal] at hi hf
    all_goals first
      | exact and_upper_on_open (w:=w) (hw:=hw) (v:=v) (c:=c) (B:=B) (p:=p) C hg
      | exact and_upper_on_closed (w:=w) (hw:=hw) (v:=v) (c:=c) (B:=B) (p:=p) C hg
      | exact and_upper_off (w:=w) (hw:=hw) (v:=v) (c:=c) (B:=B) (p:=p) C hg _ _
  · subst role
    simp only [hiE,hfE] at hi hf ⊢
    cases a <;> cases b <;> cases d <;> simp [Gadgets.Gates.legal] at hi hf
    all_goals first
      | exact and_right_on (w:=w) (hw:=hw) (v:=v) (c:=c) (B:=B) (p:=p) C hg _ _
      | exact and_right_off (w:=w) (hw:=hw) (v:=v) (c:=c) (B:=B) (p:=p) C hg

private theorem or_step (C : GatePhysicalContext c role p B) (hg : c.gate.core.isAND = false)
    (hi : Gadgets.Gates.legal false c.gate.core.initial) (hf : Gadgets.Gates.legal false c.gate.core.target)
    (hs : Gadgets.Gates.singleChange c.gate.core.initial c.gate.core.target) :
    OrStep w c.embedding B C.outside c.gate.core.initial c.gate.core.target := by
  rcases C.selected_change hs with ⟨hr,a,b,d,hiE,hfE⟩ | ⟨hr,a,b,d,hiE,hfE⟩ | ⟨hr,a,b,d,hiE,hfE⟩
  · subst role
    simp only [hiE,hfE] at hi hf ⊢
    cases a <;> cases b <;> cases d <;> simp [Gadgets.Gates.legal] at hi hf
    all_goals first
      | exact or_left_on_closed (w:=w) (hw:=hw) (v:=v) (c:=c) (B:=B) (p:=p) C hg
      | exact or_left_on_open (w:=w) (hw:=hw) (v:=v) (c:=c) (B:=B) (p:=p) C hg _
      | exact or_left_off (w:=w) (hw:=hw) (v:=v) (c:=c) (B:=B) (p:=p) C hg _ _
  · subst role
    simp only [hiE,hfE] at hi hf ⊢
    cases a <;> cases b <;> cases d <;> simp [Gadgets.Gates.legal] at hi hf
    all_goals first
      | exact or_upper_on_closed (w:=w) (hw:=hw) (v:=v) (c:=c) (B:=B) (p:=p) C hg
      | exact or_upper_on_open (w:=w) (hw:=hw) (v:=v) (c:=c) (B:=B) (p:=p) C hg _
      | exact or_upper_off (w:=w) (hw:=hw) (v:=v) (c:=c) (B:=B) (p:=p) C hg _ _
  · subst role
    simp only [hiE,hfE] at hi hf ⊢
    cases a <;> cases b <;> cases d <;> simp [Gadgets.Gates.legal] at hi hf
    all_goals first
      | exact or_right_on (w:=w) (hw:=hw) (v:=v) (c:=c) (B:=B) (p:=p) C hg _ _
      | exact or_right_off_A (w:=w) (hw:=hw) (v:=v) (c:=c) (B:=B) (p:=p) C hg _
      | exact or_right_off_B (w:=w) (hw:=hw) (v:=v) (c:=c) (B:=B) (p:=p) C hg

private theorem action (C : GatePhysicalContext c role p B)
    (hi : Gadgets.Gates.legal c.gate.core.isAND c.gate.core.initial)
    (hf : Gadgets.Gates.legal c.gate.core.isAND c.gate.core.target)
    (hs : Gadgets.Gates.singleChange c.gate.core.initial c.gate.core.target) :
    c.Action (c.corePhase role p (tilePhases C.phase)) B := by
  cases hg : c.gate.core.isAND
  · refine .orStep hg ?_ ?_ ?_
    · simpa only [outside,CoreSite.remaining,c.orLabels_piece hg] using
        C.or_step hg (by simpa only [hg] using hi) (by simpa only [hg] using hf) hs
    · simpa only [orMixedBoxes_normal,outside,CoreSite.remaining,c.orLabels_piece hg] using
        C.orAccess hg (orNormalPhases w c.gate.core.initial.left c.gate.core.initial.upper c.gate.core.initial.right)
    · simpa only [orMixedBoxes_normal,outside,CoreSite.remaining,c.orLabels_piece hg] using
        C.orAccess hg (orNormalPhases w c.gate.core.target.left c.gate.core.target.upper c.gate.core.target.right)
  · refine .andStep hg ?_ ?_ ?_
    · simpa only [outside,CoreSite.remaining,c.andLabels_piece hg] using
        C.and_step hg (by simpa only [hg] using hi) (by simpa only [hg] using hf) hs
    · simpa only [andMixedBoxes_normal,outside,CoreSite.remaining,c.andLabels_piece hg] using
        C.andCanonicalAccess hg (andNormalPhases w c.gate.core.initial.left c.gate.core.initial.upper c.gate.core.initial.right)
    · simpa only [andMixedBoxes_normal,outside,CoreSite.remaining,c.andLabels_piece hg] using
        C.andCanonicalAccess hg (andNormalPhases w c.gate.core.target.left c.gate.core.target.upper c.gate.core.target.right)

end GatePhysicalContext

theorem CoreSite.actual_action {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source}
    (c : CoreSite w hw v) (role : Fin 3) (p : PathSite w hw v (armSpec w c.gate role))
    (hloc : p.location = ((codes w v).get c.index).1)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) (ha : (inventory w hw v).Admissible)
    (g : Plan.VertexData) (hc : CellPlan.cell (v,p.location) = some (.inl (g,c.gate)))
    (phase : Cslib.Complexity.NCL.GridRouting.Point → Bool) (fresh : phase p.location = false)
    (hb : (armSpec w c.gate role).target = !(armSpec w c.gate role).initial)
    (B : Board (width w v) (height w v)) (hB : B.walls = (inventory w hw v).walls)
    (hi : Gadgets.Gates.legal c.gate.core.isAND c.gate.core.initial)
    (hf : Gadgets.Gates.legal c.gate.core.isAND c.gate.core.target)
    (hs : Gadgets.Gates.singleChange c.gate.core.initial c.gate.core.target) :
    c.Action (c.corePhase role p (tilePhases phase)) B :=
  (GatePhysicalContext.of_actual hloc hP hT ha g hc phase fresh hb hB).action hi hf hs

end PushPuzzle.PushS.FiniteSourceInventory
