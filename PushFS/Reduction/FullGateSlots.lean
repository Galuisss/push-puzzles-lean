/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateBoundary

/-! Complete semantic gate-label positions throughout each true exterior face. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateTileRouting


open Inventory FullGateBoundary

abbrev FullLabel (g : GateTileState) := (i : Fin (Fintype.card (Inventory.Index g)))×Inventory.AtlasLabels g i

theorem full_source_frame (g : GateTileState) (d : Direction) (l : FullLabel g)
    (hf : InFrame d (((fullSlotMatching g).source l).1.val,((fullSlotMatching g).source l).2.val)) :
    ∃role : Fin 3,∃prev : Bool,PortAnnulus.outerDirection (g.key role).2=d ∧
      (((fullSlotMatching g).source l).1.val,((fullSlotMatching g).source l).2.val)=
        endpointPoint d (g.incoming.get role) (initialPhase g role) prev := by
  rcases l with ⟨j,l⟩
  let i := (numbering g).symm j
  change Labels g i at l
  change InFrame d ((offset g i).1+((matching g i).source l).1.val,
    (offset g i).2+((matching g i).source l).2.val) at hf
  change ∃role : Fin 3,∃prev : Bool,PortAnnulus.outerDirection (g.key role).2=d ∧
    ((offset g i).1+((matching g i).source l).1.val,
      (offset g i).2+((matching g i).source l).2.val)=
      endpointPoint d (g.incoming.get role) (initialPhase g role) prev
  have hh := source_identity g d i l hf
  rcases i with i | (⟨role,j | j⟩ | role)
  · exact hh.elim
  · rcases hh with ⟨_,hd,hh|hh⟩
    · exact ⟨role,false,hd,hh.2⟩
    · exact ⟨role,true,hd,hh.2.2⟩
  · exact hh.elim
  · exact l.elim0

theorem full_target_frame (g : GateTileState) (d : Direction) (l : FullLabel g)
    (hf : InFrame d (((fullSlotMatching g).target l).1.val,((fullSlotMatching g).target l).2.val)) :
    ∃role : Fin 3,∃prev : Bool,PortAnnulus.outerDirection (g.key role).2=d ∧
      (((fullSlotMatching g).target l).1.val,((fullSlotMatching g).target l).2.val)=
        endpointPoint d (g.incoming.get role) (targetPhase g role) prev := by
  rcases l with ⟨j,l⟩
  let i := (numbering g).symm j
  change Labels g i at l
  change InFrame d ((offset g i).1+((matching g i).target l).1.val,
    (offset g i).2+((matching g i).target l).2.val) at hf
  change ∃role : Fin 3,∃prev : Bool,PortAnnulus.outerDirection (g.key role).2=d ∧
    ((offset g i).1+((matching g i).target l).1.val,
      (offset g i).2+((matching g i).target l).2.val)=
      endpointPoint d (g.incoming.get role) (targetPhase g role) prev
  have hh := target_identity g d i l hf
  rcases i with i | (⟨role,j | j⟩ | role)
  · exact hh.elim
  · rcases hh with ⟨_,hd,hh|hh⟩
    · exact ⟨role,false,hd,hh.2⟩
    · exact ⟨role,true,hd,hh.2.2⟩
  · exact hh.elim
  · exact l.elim0

end PushPuzzle.PushFS.Reduction.GateTileRouting
