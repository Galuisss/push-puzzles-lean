/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.ReadScan
public import PushPush.Walking
public import Push.ColumnScanForward
import all Push.ColumnScanForward

/-! Maximum-sliding commitment to the existing physical column reader. -/

@[expose] public section
namespace PushPuzzle.PushPush.ColumnReader

open PushFS (Cell State Direction Adjacent)
open Reader

variable (r : Push.ColumnScan.Input)

/-- The player at the eastern room's bottom, before closing the source door. -/
def bottomState : State r.outputWidth r.outputHeight := ⟨r.bottom, r.emptyᶜ⟩

private theorem bottom_data : northData (bottomState r) (r.height + 1) = {r.door, r.upper} := by
  ext p
  simp only [northData, bottomState, compl_compl, Finset.mem_filter,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hp, hx, hy⟩
    have hcol : p.1.val = r.width := congrArg Fin.val hx
    rcases (r.separator_holes p hcol).mp hp with he | he | he
    · exact Or.inl he
    · exact Or.inr he
    · have he := congrArg (fun q => q.2.val) he
      change p.2.val = r.outputHeight - 1 at he
      have := r.length_ge_seven
      unfold Push.ColumnScan.Input.outputHeight at he
      omega
  · intro hp
    rcases hp with rfl | rfl
    · exact ⟨r.door_mem, rfl, by
        change r.height - 1 < r.height + 1
        omega⟩
    · exact ⟨r.upper_mem, rfl, by change r.height < r.height + 1; omega⟩

private theorem bottom_gap : ∀ p : Cell r.outputWidth r.outputHeight,
    p.1 = (bottomState r).player.1 → r.height + 1 ≤ p.2.val →
      p.2.val < (bottomState r).player.2.val → p ∈ (bottomState r).boxes := by
  intro p hx hlo hhi
  apply Finset.mem_compl.mpr
  intro hp
  have hcol : p.1.val = r.width := congrArg Fin.val hx
  rcases (r.separator_holes p hcol).mp hp with he | he | he
  · have hy := congrArg (fun q => q.2.val) he
    change p.2.val = r.height - 1 at hy
    omega
  · have hy := congrArg (fun q => q.2.val) he
    change p.2.val = r.height at hy
    omega
  · have hy := congrArg (fun q => q.2.val) he
    change p.2.val = (bottomState r).player.2.val at hy
    omega

private theorem bottom_valid : (bottomState r).player ∉ (bottomState r).boxes := by
  exact Finset.notMem_compl.mpr r.bottom_mem

/-- One maximum slide consumes both seal holes; walking one cell finishes commitment. -/
private theorem seal_readPath : ReadPath (bottomState r) r.sealedState.toState := by
  have hne : r.door ≠ r.upper := by
    intro he
    have := congrArg (fun q => q.2.val) he
    change r.height - 1 = r.height at this
    have := r.height_pos
    omega
  have hdata : (northData (bottomState r) (r.height + 1)).card = 2 := by
    rw [bottom_data]
    simp [hne]
  have H : ExactNorthRead (northData (bottomState r) (r.height + 1)) ∅ := by
    refine ⟨Finset.empty_subset _, ?_, ?_⟩ <;> simp
  obtain ⟨t, ht, htx, hty, _, _, hholes⟩ :=
    read_north_exact_path 2 (bottomState r) (r.height + 1) ∅ H (by simpa using hdata.symm)
      (bottom_valid r) (by
        rw [hdata]
        change r.height + 1 + 2 < r.outputHeight - 1
        have := r.length_ge_seven
        unfold Push.ColumnScan.Input.outputHeight
        omega) (bottom_gap r)
  have hp : t.player = r.landing := by
    apply Prod.ext
    · exact htx
    · apply Fin.ext
      change t.player.2.val + 2 = r.outputHeight - 1 at hty
      change t.player.2.val = r.firstLevel
      have := r.length_ge_seven
      have := r.height_pos
      unfold Push.ColumnScan.Input.firstLevel Push.ColumnScan.Input.outputHeight at *
      omega
  have htrail : northTrail (bottomState r) 2 = {r.firstSeal, r.landing} := by
    ext p
    simp only [northTrail, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff, Fin.ext_iff]
    change (p.1.val = r.width ∧ r.outputHeight - 1 - 2 ≤ p.2.val ∧ p.2.val < r.outputHeight - 1) ↔
      (p.1.val = r.width ∧ p.2.val = r.outputHeight - 2) ∨
        (p.1.val = r.width ∧ p.2.val = r.firstLevel)
    have := r.length_ge_seven
    have := r.height_pos
    unfold Push.ColumnScan.Input.firstLevel Push.ColumnScan.Input.outputHeight
    omega
  have he : t = r.sealedState.toState := by
    apply State.ext hp
    apply compl_injective
    rw [hholes, Finset.sdiff_empty, bottom_data, htrail]
    simp only [bottomState, compl_compl]
    ext p
    simp only [PushS.HoleState.toState, Push.ColumnScan.Input.sealedState,
      Push.ColumnScan.Input.firstSealState, compl_compl,
      Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase]
    have hfl : r.firstSeal ≠ r.door := by
      intro he
      have heq := congrArg (fun q => q.2.val) he
      change r.outputHeight - 2 = r.height - 1 at heq
      have := r.length_ge_seven
      have := r.height_pos
      unfold Push.ColumnScan.Input.outputHeight at heq
      omega
    by_cases hpd : p = r.door <;> by_cases hpf : p = r.firstSeal <;> simp_all
    tauto
  exact he ▸ ht

/-- The source corner reaches the eastern room using ordinary empty-cell walks. -/
private theorem corner_to_bottom_readPath (hcorner : r.initial.player = r.sourceCorner) :
    ReadPath r.compile.initial (bottomState r) := by
  have hdoor : Move .east r.compile.initial ⟨r.door, r.emptyᶜ⟩ := by
    apply Move.walk
    · exact Finset.notMem_compl.mpr r.initialState.player_empty
    · change r.door.1.val = r.initial.player.1.val + 1 ∧
        r.door.2 = (r.embed r.initial.player).2
      rw [hcorner]
      refine ⟨?_, rfl⟩
      change r.width = r.width - 1 + 1
      have := r.width_pos
      omega
    · exact Finset.notMem_compl.mpr r.door_mem
    · rfl
  have hupper : Move .south (⟨r.door, r.emptyᶜ⟩ : State r.outputWidth r.outputHeight)
      ⟨r.upper, r.emptyᶜ⟩ := by
    apply Move.walk (Finset.notMem_compl.mpr r.door_mem)
    · refine ⟨rfl, ?_⟩
      change r.height = r.height - 1 + 1
      have := r.height_pos
      omega
    · exact Finset.notMem_compl.mpr r.upper_mem
    · rfl
  have hentry : Move .east (⟨r.upper, r.emptyᶜ⟩ : State r.outputWidth r.outputHeight)
      ⟨r.roomEntry, r.emptyᶜ⟩ :=
    .walk (Finset.notMem_compl.mpr r.upper_mem) ⟨rfl, rfl⟩
      (Finset.notMem_compl.mpr r.roomEntry_mem) rfl
  have hroom : ReadPath (⟨r.roomEntry, r.emptyᶜ⟩ : State r.outputWidth r.outputHeight)
      ⟨r.roomBottom, r.emptyᶜ⟩ := by
    apply ReadPath.walk_vertical r.emptyᶜ r.roomEntry.1 r.roomEntry.2 r.roomBottom.2
    intro y hlo _
    apply Finset.notMem_compl.mpr
    apply r.room_mem rfl
    change min r.height (r.outputHeight - 1) ≤ y.val at hlo
    have hle : r.height ≤ r.outputHeight - 1 := by
      have := r.length_ge_seven
      unfold Push.ColumnScan.Input.outputHeight
      omega
    rwa [Nat.min_eq_left hle] at hlo
  have hbottom : Move .west (⟨r.roomBottom, r.emptyᶜ⟩ : State r.outputWidth r.outputHeight)
      (bottomState r) :=
    .walk (Finset.notMem_compl.mpr r.roomBottom_mem) ⟨rfl, rfl⟩
      (Finset.notMem_compl.mpr r.bottom_mem) rfl
  exact (((Relation.ReflTransGen.single ⟨.east, hdoor, Or.inr rfl⟩).tail ⟨.south, hupper, Or.inr rfl⟩).tail
    ⟨.east, hentry, Or.inr rfl⟩ |>.trans hroom).tail ⟨.west, hbottom, Or.inr rfl⟩

/-- The committed reader closes its source door with the maximum-sliding semantics. -/
theorem sealed_readPath (hcorner : r.initial.player = r.sourceCorner) :
    ReadPath r.compile.initial r.sealedState.toState :=
  (corner_to_bottom_readPath r hcorner).trans (seal_readPath r)

theorem sealed_reachable (hcorner : r.initial.player = r.sourceCorner) :
    Reachable r.compile.initial r.sealedState.toState :=
  (sealed_readPath r hcorner).reachable

end PushPuzzle.PushPush.ColumnReader
