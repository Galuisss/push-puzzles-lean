/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourcePathCompletion
public import PushS.FiniteSourceCoreForward
public import PushS.FiniteSourcePhaseCongruence

/-! Completing the real selected arm and core completes precisely one actual gate tile. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting
open Cslib.Complexity.NCL Plan SourceCanonical
open scoped Classical

attribute [local irreducible] codes width height inventory

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} {P : PathSpec}

namespace PathSite

variable (p : PathSite w hw v P)

/-- Updating an external owner commutes with every literal cut of the path's real phase wave. -/
theorem wave_update_external (base : Fin (codes w v).length → Bool) (cut : ℕ)
    (i : Fin (codes w v).length) (hi : ∀ a : PathEvent P,a.owner p ≠ i) :
    p.wave (Function.update base i true) cut = Function.update (p.wave base cut) i true := by
  funext j
  by_cases he : j = i
  · subst j
    rw [p.wave_outside _ _ _ hi,Function.update_self,Function.update_self]
  · rw [Function.update_of_ne he]
    unfold wave
    split_ifs
    · rfl
    · exact Function.update_of_ne he _ _

end PathSite

namespace CoreSite

variable (c : CoreSite w hw v)

/-- The final complete phase after physically executing the core and its selected full arm. -/
@[expose] noncomputable def armCoreFinal (role : Fin 3) (p : PathSite w hw v (armSpec w c.gate role))
    (base : Fin (codes w v).length → Bool) : Fin (codes w v).length → Bool :=
  Function.update (p.wave base (PathSite.waveLength (P := armSpec w c.gate role))) c.index true

/-- The selected arm's actual owners are all complete after either legal arm/core order. -/
private theorem armCoreFinal_event (role : Fin 3) (p : PathSite w hw v (armSpec w c.gate role))
    (base : Fin (codes w v).length → Bool) (a : PathEvent (armSpec w c.gate role)) :
    c.armCoreFinal role p base (a.owner p) = true := by
  rw [armCoreFinal,Function.update_of_ne (c.arm_event_ne_core role p a),p.wave_final]
  exact ite_eq_left ⟨a,rfl⟩

/-- The core's actual owner is complete at the final inventory. -/
private theorem armCoreFinal_core (role : Fin 3) (p : PathSite w hw v (armSpec w c.gate role))
    (base : Fin (codes w v).length → Bool) : c.armCoreFinal role p base c.index = true :=
  Function.update_self _ _ _

/-- Every actual owner away from the selected path and core remains at its initial tile-profile phase. -/
private theorem armCoreFinal_outside (role : Fin 3) (p : PathSite w hw v (armSpec w c.gate role))
    (base : Fin (codes w v).length → Bool) (i : Fin (codes w v).length)
    (hic : i ≠ c.index) (hip : ∀ a : PathEvent (armSpec w c.gate role),a.owner p ≠ i) :
    c.armCoreFinal role p base i = base i := by
  rw [armCoreFinal,Function.update_of_ne hic,p.wave_outside _ _ _ hip]

/-- Finishing a selected arm and core gives exactly the complete updated gate-tile stock; all other arms are literally idle. -/
theorem armCoreFinal_state (role : Fin 3) (p : PathSite w hw v (armSpec w c.gate role))
    (hloc : p.location = ((codes w v).get c.index).1) (ha : (inventory w hw v).Admissible)
    (phase : GridRouting.Point → Bool)
    (idle : ∀ i : Fin (codes w v).length,((codes w v).get i).1 = p.location → i ≠ c.index →
      ((codes w v).get i).2 ∉ (armSpec w c.gate role).codes → (((codes w v).get i).2).SamePhase)
    (player : Cell (width w v) (height w v)) :
    PrimitiveProfile.state w hw v (c.armCoreFinal role p (tilePhases phase)) player =
      PrimitiveProfile.state w hw v (tilePhases (Function.update phase p.location true)) player := by
  apply PrimitiveProfile.state_congr
  intro i
  by_cases hl : ((codes w v).get i).1 = p.location
  · by_cases hic : i = c.index
    · subst i
      exact Or.inl (by rw [c.armCoreFinal_core]; simp only [tilePhases,hl,Function.update_self])
    · by_cases hp : ((codes w v).get i).2 ∈ (armSpec w c.gate role).codes
      · obtain ⟨a,rfl⟩ := p.owner_covers ha i hl hp
        exact Or.inl (by rw [c.armCoreFinal_event]; simp only [tilePhases,a.owner_location,Function.update_self])
      · exact Or.inr (idle i hl hic hp)
  · apply Or.inl
    have hic : i ≠ c.index := by intro he; apply hl; exact he ▸ hloc.symm
    have hip : ∀ a : PathEvent (armSpec w c.gate role),a.owner p ≠ i := by
      intro a he
      exact hl (he ▸ a.owner_location p)
    rw [c.armCoreFinal_outside role p _ i hic hip]
    simp only [tilePhases,Function.update_of_ne hl]

end CoreSite

/-- Every other arm of this actual gate has exactly equal source and target primitive slots. -/
theorem gate_remaining_idle (w : ℕ) (word : Word) (hG : word.compile.Valid)
    (hP : word.checkPlane = true) (hT : word.WellTyped [] [])
    (c : Fin word.compile.edgeCount → Bool) (e : Fin word.compile.edgeCount)
    (g : VertexData) (hg : g ∈ vertexRecords word) (role : Fin 3) (he : (g.ports.port role).edge = e.val)
    {code : PrimitiveCode} (hc : code ∈ gateCodes w (gateTileState (g,(oneEdgeSource word c e).2)))
    (hcore : code ≠ .core (gateTileState (g,(oneEdgeSource word c e).2)))
    (hselected : code ∉ (armSpec w (gateTileState (g,(oneEdgeSource word c e).2)) role).codes) :
    code.SamePhase := by
  rcases List.mem_cons.mp hc with hc | hc
  · exact (hcore hc).elim
  · obtain ⟨r,_,hr⟩ := List.mem_flatMap.mp hc
    have hne : r ≠ role := by
      intro hh
      subst r
      exact hselected hr
    have hedge : (g.ports.port r).edge ≠ e.val := by
      intro hh
      exact hne (vertexRecord_edges_injective hP hT hg (hh.trans he.symm))
    exact gate_arm_code_samePhase w word hG hP hT c e g hg r hedge hr

end PushPuzzle.PushS.FiniteSourceInventory
