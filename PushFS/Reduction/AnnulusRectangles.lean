/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.AnnulusRectangles.Data

/-! Recover the complete checked noncontact rectangle separation for all canonical physical phases. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateTileRouting.Inventory


private theorem contact_geometry (g : GateTileState) (i j : Index g) :
    contact (ofGeometry (geometry g)) i j=contact g i j := by
  rcases i with a | (⟨r,s | t⟩ | u) <;>
    rcases j with b | (⟨r',s' | t'⟩ | u') <;> rfl

private theorem rectangle_geometry (g : GateTileState) (i : Index g) :
    rectangle (ofGeometry (geometry g)) i=rectangle g i := by
  rcases i with i | (⟨role,j | j⟩ | role) <;> rfl

/-- Every possible rectangle overlap is one of the actual local physical seam contacts above. -/
theorem separated (g : GateTileState) (i j : Index g) (hij : i≠j) (hc : contact g i j=false) :
    (rectangle g i).Disjoint (rectangle g j) := by
  change Index (ofGeometry (geometry g)) at i j
  have hh := separated_checked (geometry g)
  have hi := mem_indices (ofGeometry (geometry g)) i
  have hj := mem_indices (ofGeometry (geometry g)) j
  have hp := List.all_eq_true.mp (List.all_eq_true.mp hh (i,rectangle (ofGeometry (geometry g)) i)
    (List.mem_map.mpr ⟨i,hi,rfl⟩)) (j,rectangle (ofGeometry (geometry g)) j) (List.mem_map.mpr ⟨j,hj,rfl⟩)
  dsimp only at hp
  have hc' : contact (ofGeometry (geometry g)) i j=false := (contact_geometry g i j).trans hc
  have hp' : (rectangle (ofGeometry (geometry g)) i).Disjoint (rectangle (ofGeometry (geometry g)) j) := by
    have hn : ¬(i=j ∨ contact (ofGeometry (geometry g)) i j=true) := by
      rintro (he | he)
      · exact hij he
      · cases hc'.symm.trans he
    rw [ite_eq_right hn] at hp
    exact of_decide_eq_true hp
  rw [rectangle_geometry g i,rectangle_geometry g j] at hp'
  exact hp'

end PushPuzzle.PushFS.Reduction.GateTileRouting.Inventory
