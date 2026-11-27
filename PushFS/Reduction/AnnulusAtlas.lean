/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.AnnulusAssembleContacts
public import PushFS.Reduction.AnnulusPlayer
public import PushFS.Reduction.BitmapExt

/-! Assemble the complete genuine physical annular inventory into the exact unlabelled storage instance and bitmap. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateTileRouting.Inventory


open Turing.MultiTapeTM ComputableInPolyTime

set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

noncomputable def numbering (g : GateTileState) : Index g≃Fin (Fintype.card (Index g)) := Fintype.equivFin _

noncomputable def AtlasLabels (g : GateTileState) (i : Fin (Fintype.card (Index g))) : Type :=
  Labels g ((numbering g).symm i)

noncomputable instance (g : GateTileState) (i : Fin (Fintype.card (Index g))) : Fintype (AtlasLabels g i) :=
  inferInstanceAs (Fintype (Labels g ((numbering g).symm i)))

/-- Every primitive buffer, complete long line, short turn and output guard retains its real storage identities. -/
noncomputable def atlas (g : GateTileState) (f : FrontierContactProofs g) :
    StorageAtlas (Fintype.card (Index g)) 200007 198068 (AtlasLabels g) where
  piece i := piece g ((numbering g).symm i)
  matching i := matching g ((numbering g).symm i)
  dx i := (offset g ((numbering g).symm i)).1
  dy i := (offset g ((numbering g).symm i)).2
  fitsX i := (fits g ((numbering g).symm i)).1
  fitsY i := (fits g ((numbering g).symm i)).2
  walls_compatible i j p q he := (contactProofs g f).walls_compatible ((numbering g).symm i) ((numbering g).symm j) p q he
  source_owners i j l k he := (numbering g).symm.injective ((contactProofs g f).source_owners ((numbering g).symm i) ((numbering g).symm j) l k he)
  target_owners i j l k he := (numbering g).symm.injective ((contactProofs g f).target_owners ((numbering g).symm i) ((numbering g).symm j) l k he)
  player := player g
  player_floor i p hp := player_floor g ((numbering g).symm i) p hp
  player_empty i l := player_empty g ((numbering g).symm i) l

theorem atlas_patch (g : GateTileState) (f : FrontierContactProofs g) (i : Fin (Fintype.card (Index g))) :
    Bitmap.instancePatch ((atlas g f).piece i) ((atlas g f).dx i) ((atlas g f).dy i)=patch g ((numbering g).symm i) := rfl

noncomputable def puzzle (g : GateTileState) (f : FrontierContactProofs g) : Instance := (atlas g f).puzzle

noncomputable def slotMatching (g : GateTileState) (f : FrontierContactProofs g) :
    SlotMatching (puzzle g f) ((i : Fin (Fintype.card (Index g)))×AtlasLabels g i) := (atlas g f).slotMatching

theorem atlas_patch_membership (g : GateTileState) (f : FrontierContactProofs g) (p : Bitmap.Patch) :
    p∈(atlas g f).input.patches ↔ p∈(input g).patches := by
  simp only [StorageAtlas.input,List.mem_ofFn,input,patches,List.mem_map,atlas_patch]
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨(numbering g).symm i,mem_indices g _,rfl⟩
  · rintro ⟨i,_,rfl⟩
    refine ⟨numbering g i,?_⟩
    rw [Equiv.symm_apply_apply]

/-- The exact full physical storage puzzle is the actual complete dense machine-rendered gate tile. -/
theorem puzzle_data (g : GateTileState) (f : FrontierContactProofs g) : Encoding.data (puzzle g f)=data g := by
  exact (atlas g f).data_eq.trans (Bitmap.emit_ext (atlas g f).input (input g) rfl rfl rfl rfl (atlas_patch_membership g f))

end PushPuzzle.PushFS.Reduction.GateTileRouting.Inventory
