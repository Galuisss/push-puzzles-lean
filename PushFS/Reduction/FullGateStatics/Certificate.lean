/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateStatics.Components
public import PushFS.Reduction.FullGateStatics.CoreNames
public import PushFS.Reduction.FullGateStatics.EnvelopesChecked
public import PushFS.Reduction.FullGateStatics.Separated
public import PushFS.Reduction.FullGateStatics.Sparse

/-! C1–C3 for the complete physical gate, including every annular auxiliary box. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics

open Inventory Gadgets Gadgets.Wires
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] StorageAtlas.initial StorageAtlas.board Mosaic.name

private theorem primitive_adjacent (g : GateTileState) (i : Inventory.Index g)
    (p q : Cell (Inventory.piece g i).width (Inventory.piece g i).height) (d : Direction)
    (ha : Adjacent d ((primitiveEmbedding g i).cells p) ((primitiveEmbedding g i).cells q)) :
    Adjacent d p q := by
  cases d <;>
    dsimp only [Adjacent,primitiveEmbedding,GridEmbedding.translate,Function.Embedding.coeFn_mk] at ha ⊢ <;>
    simp only [Fin.mk.injEq] at ha <;> constructor <;> omega

private theorem primitive_target_mem (g : GateTileState) (i : Inventory.Index g) (l : Inventory.Labels g i) :
    (Inventory.matching g i).target l∈(Inventory.piece g i).board.goals := by
  rw [←(Inventory.matching g i).target_image]
  exact Finset.mem_map.mpr ⟨l,Finset.mem_univ _,rfl⟩

private theorem noncore_sparse (g : GateTileState) (i : Inventory.Index g) (hi : i≠.inl 0)
    (p : Cell (Inventory.piece g i).width (Inventory.piece g i).height) (hp : p∈(Inventory.piece g i).board.goals)
    (q : Cell (Inventory.piece g i).width (Inventory.piece g i).height) (hq : q∈(Inventory.piece g i).board.goals) (d : Direction) :
    ¬Adjacent d p q := by
  rcases i with i|(⟨role,j|j⟩|role)
  · fin_cases i
    · exact False.elim (hi rfl)
    · exact west_sparse _ _ _ _ _ p hp q hq d
    · exact north_sparse _ _ _ _ p hp q hq d
    · exact east_sparse _ _ _ _ p hp q hq d
  · exact line_sparse _ _ j.isLt _ _ p hp q hq d
  · exact corner_sparse _ _ _ _ p hp q hq d
  · exact False.elim (Finset.notMem_empty p hp)

private theorem core_target_name (g : GateTileState) (l : Fin (Gates.slots g.core.isAND).length) :
    (classifier g).name (rawTarget g ⟨.inl 0,l⟩)=
      AxisTrack.shift (chart g (.inl (.inl 0))).dx (chart g (.inl (.inl 0))).dy
        (Gates.axisName g.core.isAND ((Gates.slotMatching g.core.isAND g.core.initial g.core.target).target l)) := by
  let s:=(Gates.slots g.core.isAND)[l.val]
  have hs : s∈Gates.slots g.core.isAND:=List.getElem_mem l.isLt
  exact core_name g (s.position g.core.target)
    (Gates.slot_position_active _ _ hs _) (coreLevel_position g s hs _)

private theorem core_targets_separated (g : GateTileState)
    (l k : Fin (Gates.slots g.core.isAND).length)
    (he : (classifier g).name (rawTarget g ⟨.inl 0,l⟩)=
      (classifier g).name (rawTarget g ⟨.inl 0,k⟩)) (d : Direction) :
    ¬Adjacent d (rawTarget g ⟨.inl 0,l⟩) (rawTarget g ⟨.inl 0,k⟩) := by
  rw [core_target_name,core_target_name] at he
  have hn:=AxisTrack.shift_injective _ _ he
  have hp:=primitive_target_mem g (.inl 0) l
  have hq:=primitive_target_mem g (.inl 0) k
  intro ha
  exact Gates.normal_separated _ _ _ hp _ hq hn d (primitive_adjacent g (.inl 0) _ _ d ha)

section
attribute [local irreducible] rawTarget

private theorem core_offset_bounds (kind : Bool) (x y : ℕ) (hx : x<81) (hy : y<107) :
    7≤(bufferOffset kind).1+2311+x ∧(bufferOffset kind).1+2311+x<200000 ∧
    7≤(bufferOffset kind).2+2321+y ∧(bufferOffset kind).2+2321+y<198061 := by
  cases kind
  · change 7≤99959+x ∧99959+x<200000 ∧7≤98974+y ∧98974+y<198061
    omega
  · change 7≤99960+x ∧99960+x<200000 ∧7≤98974+y ∧98974+y<198061
    omega

/-- All central-core target identities are deep inside the complete physical gate. -/
theorem core_target_bounds (g : GateTileState) (l : Fin (Gates.slots g.core.isAND).length) :
    7≤(rawTarget g ⟨.inl 0,l⟩).1.val ∧(rawTarget g ⟨.inl 0,l⟩).1.val<200000 ∧
    7≤(rawTarget g ⟨.inl 0,l⟩).2.val ∧(rawTarget g ⟨.inl 0,l⟩).2.val<198061 := by
  unfold rawTarget
  let p:=(Gates.slotMatching g.core.isAND g.core.initial g.core.target).target l
  have hx:=p.1.isLt
  have hy:=p.2.isLt
  change 7≤(bufferOffset g.core.isAND).1+2311+p.1.val ∧
    (bufferOffset g.core.isAND).1+2311+p.1.val<200000 ∧
    7≤(bufferOffset g.core.isAND).2+2321+p.2.val ∧
    (bufferOffset g.core.isAND).2+2321+p.2.val<198061
  exact core_offset_bounds g.core.isAND p.1.val p.2.val hx hy

end

/-- Adjacent complete-gate goals both belong to the original central core. -/
theorem adjacent_targets_core (g : GateTileState) (i j : Inventory.Index g)
    (l : Inventory.Labels g i) (k : Inventory.Labels g j) (d : Direction)
    (ha : Adjacent d (rawTarget g ⟨i,l⟩) (rawTarget g ⟨j,k⟩)) : i=.inl 0 ∧j=.inl 0 := by
  by_cases hij : i=j
  · subst j
    by_cases hi : i=.inl 0
    · exact ⟨hi,hi⟩
    · exact False.elim (noncore_sparse g i hi _ (primitive_target_mem g i l) _
        (primitive_target_mem g i k) d (primitive_adjacent g i _ _ d ha))
  · exact False.elim (targets_of_different_primitives g (envelopesApart_all g) i j hij l k d ha)

/-- Goals carrying the same actual global rail name are separated. -/
theorem named_separated (g : GateTileState) (p : C) (hp : p∈(fullPuzzle g).board.goals)
    (q : C) (hq : q∈(fullPuzzle g).board.goals)
    (he : (classifier g).name p=(classifier g).name q) (d : Direction) :
    ¬Adjacent d p q := by
  obtain ⟨⟨i,l⟩,rfl⟩:=(full_goals_mem g p).mp hp
  obtain ⟨⟨j,k⟩,rfl⟩:=(full_goals_mem g q).mp hq
  by_cases hij : i=j
  · subst j
    by_cases hi : i=.inl 0
    · subst i
      exact core_targets_separated g l k he d
    · exact fun ha=>noncore_sparse g i hi _ (primitive_target_mem g i l) _
        (primitive_target_mem g i k) d (primitive_adjacent g i _ _ d ha)
  · exact targets_of_different_primitives g (envelopesApart_all g) i j hij l k d

end PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics
