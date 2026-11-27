/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateBoundary.Caps
public import PushFS.Reduction.FullGateBoundary.Lines
public import PushFS.Reduction.FullGateBoundary.RawWalls
public import PushFS.Reduction.FullGateBoundary.SlotIdentity

/-! Exact walls of the complete seven-cell exterior frame of every actual pad3 gate tile. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateBoundary

open Inventory
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- A used outer face has exactly its two common guard walls throughout the whole exterior frame. -/
theorem walls (g : GateTileState) (f : Direction) (p : C) (hf : InFrame f (p.1.val,p.2.val)) :
    p∈(fullPuzzle g).board.walls ↔Used g f ∧Guard f (p.1.val,p.2.val) := by
  rw [raw_wall_membership]
  constructor
  · rintro ⟨i,q,hq,he⟩
    have ho:=raw_owner g i f q (by rwa [he])
    rcases i with i | (⟨role,j | j⟩ | role)
    · exact ho.elim
    · obtain ⟨hj,hd⟩:=ho
      refine ⟨⟨role,hd⟩,?_⟩
      have hd' : PortAnnulus.outerDirection (key g role).1.2=f := hd
      have hw:=(last_line_wall (key g role) j hj (initialPhase g role) (targetPhase g role)
        q (p.1.val,p.2.val) he (by rwa [hd'])).mp hq
      rwa [hd'] at hw
    · exact ho.elim
    · refine ⟨⟨role.val,ho⟩,?_⟩
      have hw:=cap_wall_guard (g.key role.val) q hq
      change Guard (PortAnnulus.outerDirection (g.key role.val).2)
        ((offset g (.inr (.inr role))).1+q.1.val,(offset g (.inr (.inr role))).2+q.2.val) at hw
      rwa [he,ho] at hw
  · rintro ⟨⟨role,hd⟩,hg⟩
    have hd' : PortAnnulus.outerDirection (key g role).1.2=f := hd
    by_cases hc : g.incoming.get role=false ∧CapPoint f (p.1.val,p.2.val)
    · obtain ⟨q,hq,he⟩:=cap_covers (g.key role) (p.1.val,p.2.val) (by simpa only [hd] using hc.2) (by rwa [hd])
      exact ⟨.inr (.inr ⟨role,hc.1⟩),q,hq,he⟩
    · have hp : g.incoming.get role=true ∨¬CapPoint f (p.1.val,p.2.val) := by
        cases hi : g.incoming.get role <;> simp_all
      let j : Fin (curve (key g role)).length := ⟨(curve (key g role)).length-1,by have := last_valid (key g role); omega⟩
      have hj : j.val+1=(curve (key g role)).length := by dsimp only [j]; have := last_valid (key g role); omega
      obtain ⟨q,hq,he⟩:=last_line_covers (key g role) j hj (initialPhase g role) (targetPhase g role)
        (p.1.val,p.2.val) p.1.isLt p.2.isLt (by rwa [hd']) (by rwa [hd']) (by simpa only [key,hd] using hp)
      exact ⟨.inr (.inl ⟨role,.inl j⟩),q,hq,he⟩

end PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateBoundary
