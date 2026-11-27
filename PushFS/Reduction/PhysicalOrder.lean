/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalTileOrder
public import PushFS.Reduction.PhysicalMotion
public import PushFS.Reduction.PhysicalCertificate
public import PushFS.Reduction.PhysicalOrderGeometry

/-! The full physical source compiler retains each box's prescribed coordinate order. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.PhysicalInventory

open PhysicalBitmap
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] Raster.width Raster.height StorageAtlas.initial StorageAtlas.board

private theorem unit_pair_order {I : Instance} {L : Type} [Fintype L] (M : SlotMatching I L) (cert : Certificate I)
    (i j : L) (hi : Cell.UnitClose (M.source i) (M.target i)) (hj : Cell.UnitClose (M.source j) (M.target j))
    (hc : component I.board (M.source i)=component I.board (M.source j)) :
    ((M.source i).1.val<(M.source j).1.val→(M.target i).1.val<(M.target j).1.val) ∧
    ((M.source i).2.val<(M.source j).2.val→(M.target i).2.val<(M.target j).2.val) := by
  have hs (l : L) : M.source l∈I.initial.boxes := by
    rw [←M.source_image]
    exact Finset.mem_map.mpr ⟨l,Finset.mem_univ _,rfl⟩
  have ht (l : L) : M.target l∈I.board.goals := by
    rw [←M.target_image]
    exact Finset.mem_map.mpr ⟨l,Finset.mem_univ _,rfl⟩
  have hcomp (l : L) : component I.board (M.source l)=component I.board (M.target l) := component_eq_iff.mpr (M.connected l)
  constructor
  · intro ho
    have hij : i≠j:=by rintro rfl; exact Nat.lt_irrefl _ ho
    rcases cert.linear (M.source i) (hs i) with hx|hy
    · have hh:=congrArg Fin.val (hx _ _ rfl hc.symm)
      omega
    · have hyt:=hy _ _ (hcomp i).symm ((hcomp j).symm.trans hc.symm)
      have hxt : (M.target i).1.val≠(M.target j).1.val:=by
        intro he
        exact hij (M.target.injective (Prod.ext (Fin.ext he) hyt))
      by_contra hnot
      have ha : Adjacent .west (M.target i) (M.target j):=by
        refine ⟨?_,hyt.symm⟩
        dsimp only [Cell.UnitClose] at hi hj
        omega
      exact cert.separated _ (ht i) _ (ht j) ((hcomp i).symm.trans (hc.trans (hcomp j))) .west ha
  · intro ho
    have hij : i≠j:=by rintro rfl; exact Nat.lt_irrefl _ ho
    rcases cert.linear (M.source i) (hs i) with hx|hy
    · have hxt:=hx _ _ (hcomp i).symm ((hcomp j).symm.trans hc.symm)
      have hyt : (M.target i).2.val≠(M.target j).2.val:=by
        intro he
        exact hij (M.target.injective (Prod.ext hxt (Fin.ext he)))
      by_contra hnot
      have ha : Adjacent .north (M.target i) (M.target j):=by
        refine ⟨hxt.symm,?_⟩
        dsimp only [Cell.UnitClose] at hi hj
        omega
      exact cert.separated _ (ht i) _ (ht j) ((hcomp i).symm.trans (hc.trans (hcomp j))) .north ha
    · have hh:=congrArg Fin.val (hy _ _ rfl hc.symm)
      omega

private theorem translated_unit (v : CellPlan.Source) (i : Index v) (l : PhysicalTiles.Labels (tile i))
    (hi : Cell.UnitClose ((PhysicalTiles.matching (tile i)).source l) ((PhysicalTiles.matching (tile i)).target l)) :
    Cell.UnitClose (rawSource v ⟨i,l⟩) (rawTarget v ⟨i,l⟩) := by
  dsimp only [Cell.UnitClose] at hi ⊢
  change (PhysicalTiles.offset (position i) (tile i)).1+((PhysicalTiles.matching (tile i)).source l).1.val≤
      (PhysicalTiles.offset (position i) (tile i)).1+((PhysicalTiles.matching (tile i)).target l).1.val+1 ∧
    (PhysicalTiles.offset (position i) (tile i)).1+((PhysicalTiles.matching (tile i)).target l).1.val≤
      (PhysicalTiles.offset (position i) (tile i)).1+((PhysicalTiles.matching (tile i)).source l).1.val+1 ∧
    (PhysicalTiles.offset (position i) (tile i)).2+((PhysicalTiles.matching (tile i)).source l).2.val≤
      (PhysicalTiles.offset (position i) (tile i)).2+((PhysicalTiles.matching (tile i)).target l).2.val+1 ∧
    (PhysicalTiles.offset (position i) (tile i)).2+((PhysicalTiles.matching (tile i)).target l).2.val≤
      (PhysicalTiles.offset (position i) (tile i)).2+((PhysicalTiles.matching (tile i)).source l).2.val+1
  omega

private theorem raw_unit_order (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (i j : Index v) (l : PhysicalTiles.Labels (tile i)) (k : PhysicalTiles.Labels (tile j))
    (hi : Cell.UnitClose ((PhysicalTiles.matching (tile i)).source l) ((PhysicalTiles.matching (tile i)).target l))
    (hj : Cell.UnitClose ((PhysicalTiles.matching (tile j)).source k) ((PhysicalTiles.matching (tile j)).target k))
    (hc : component (puzzle v hP hT).board (rawSource v ⟨i,l⟩)=component (puzzle v hP hT).board (rawSource v ⟨j,k⟩)) :
    ((rawSource v ⟨i,l⟩).1.val<(rawSource v ⟨j,k⟩).1.val→(rawTarget v ⟨i,l⟩).1.val<(rawTarget v ⟨j,k⟩).1.val) ∧
    ((rawSource v ⟨i,l⟩).2.val<(rawSource v ⟨j,k⟩).2.val→(rawTarget v ⟨i,l⟩).2.val<(rawTarget v ⟨j,k⟩).2.val) := by
  have hgi : Cell.UnitClose ((rawSlotMatching v hP hT).source ⟨i,l⟩) ((rawSlotMatching v hP hT).target ⟨i,l⟩) := by
    rw [raw_source,raw_target]
    exact translated_unit v i l hi
  have hgj : Cell.UnitClose ((rawSlotMatching v hP hT).source ⟨j,k⟩) ((rawSlotMatching v hP hT).target ⟨j,k⟩) := by
    rw [raw_source,raw_target]
    exact translated_unit v j k hj
  have hgc : component (puzzle v hP hT).board ((rawSlotMatching v hP hT).source ⟨i,l⟩)=
      component (puzzle v hP hT).board ((rawSlotMatching v hP hT).source ⟨j,k⟩) := by
    rw [raw_source,raw_source]
    exact hc
  have hh:=unit_pair_order (rawSlotMatching v hP hT) (certificate v hP hT) ⟨i,l⟩ ⟨j,k⟩ hgi hgj hgc
  rw [raw_source,raw_source,raw_target,raw_target] at hh
  exact hh

private theorem same_cell_order (v : CellPlan.Source) (i : Index v) (l k : PhysicalTiles.Labels (tile i)) :
    ((rawSource v ⟨i,l⟩).2=(rawSource v ⟨i,k⟩).2 →
      (rawSource v ⟨i,l⟩).1.val<(rawSource v ⟨i,k⟩).1.val→(rawTarget v ⟨i,l⟩).1.val<(rawTarget v ⟨i,k⟩).1.val) ∧
    ((rawSource v ⟨i,l⟩).1=(rawSource v ⟨i,k⟩).1 →
      (rawSource v ⟨i,l⟩).2.val<(rawSource v ⟨i,k⟩).2.val→(rawTarget v ⟨i,l⟩).2.val<(rawTarget v ⟨i,k⟩).2.val) := by
  have hh:=PhysicalTiles.rail_order (tile i) l k
  constructor
  · intro he ho
    have he':=congrArg Fin.val he
    change (PhysicalTiles.offset (position i) (tile i)).2+((PhysicalTiles.matching (tile i)).source l).2.val=
      (PhysicalTiles.offset (position i) (tile i)).2+((PhysicalTiles.matching (tile i)).source k).2.val at he'
    change (PhysicalTiles.offset (position i) (tile i)).1+((PhysicalTiles.matching (tile i)).source l).1.val<
      (PhysicalTiles.offset (position i) (tile i)).1+((PhysicalTiles.matching (tile i)).source k).1.val at ho
    change (PhysicalTiles.offset (position i) (tile i)).1+((PhysicalTiles.matching (tile i)).target l).1.val<
      (PhysicalTiles.offset (position i) (tile i)).1+((PhysicalTiles.matching (tile i)).target k).1.val
    have ht:=hh.1 (Fin.ext (by omega)) (by omega)
    omega
  · intro he ho
    have he':=congrArg Fin.val he
    change (PhysicalTiles.offset (position i) (tile i)).1+((PhysicalTiles.matching (tile i)).source l).1.val=
      (PhysicalTiles.offset (position i) (tile i)).1+((PhysicalTiles.matching (tile i)).source k).1.val at he'
    change (PhysicalTiles.offset (position i) (tile i)).2+((PhysicalTiles.matching (tile i)).source l).2.val<
      (PhysicalTiles.offset (position i) (tile i)).2+((PhysicalTiles.matching (tile i)).source k).2.val at ho
    change (PhysicalTiles.offset (position i) (tile i)).2+((PhysicalTiles.matching (tile i)).target l).2.val<
      (PhysicalTiles.offset (position i) (tile i)).2+((PhysicalTiles.matching (tile i)).target k).2.val
    have ht:=hh.2 (Fin.ext (by omega)) (by omega)
    omega

private theorem raw_order (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (i j : Index v) (l : PhysicalTiles.Labels (tile i)) (k : PhysicalTiles.Labels (tile j))
    (hc : component (puzzle v hP hT).board (rawSource v ⟨i,l⟩)=component (puzzle v hP hT).board (rawSource v ⟨j,k⟩)) :
    ((rawSource v ⟨i,l⟩).1.val<(rawSource v ⟨j,k⟩).1.val→(rawTarget v ⟨i,l⟩).1.val<(rawTarget v ⟨j,k⟩).1.val) ∧
    ((rawSource v ⟨i,l⟩).2.val<(rawSource v ⟨j,k⟩).2.val→(rawTarget v ⟨i,l⟩).2.val<(rawTarget v ⟨j,k⟩).2.val) := by
  have hs : rawSource v ⟨i,l⟩∈(puzzle v hP hT).initial.boxes := by
    rw [←(rawSlotMatching v hP hT).source_image]
    exact Finset.mem_map.mpr ⟨⟨i,l⟩,Finset.mem_univ _,raw_source v hP hT i l⟩
  have hline:=componentLinear v hP hT (rawSource v ⟨i,l⟩) hs
  have sameRow (ho : (rawSource v ⟨i,l⟩).1.val<(rawSource v ⟨j,k⟩).1.val) : (rawSource v ⟨i,l⟩).2=(rawSource v ⟨j,k⟩).2 := by
    rcases hline with hx|hy
    · have he:=congrArg Fin.val (hx _ _ rfl hc.symm); omega
    · exact hy _ _ rfl hc.symm
  have sameCol (ho : (rawSource v ⟨i,l⟩).2.val<(rawSource v ⟨j,k⟩).2.val) : (rawSource v ⟨i,l⟩).1=(rawSource v ⟨j,k⟩).1 := by
    rcases hline with hx|hy
    · exact hx _ _ rfl hc.symm
    · have he:=congrArg Fin.val (hy _ _ rfl hc.symm); omega
  by_cases hij : i=j
  · subst j
    have hh:=same_cell_order v i l k
    exact ⟨fun ho=>hh.1 (sameRow ho) ho,fun ho=>hh.2 (sameCol ho) ho⟩
  · rcases PhysicalTiles.slot_motion (tile i) l with hi|⟨hp,hp'⟩
    · rcases PhysicalTiles.slot_motion (tile j) k with hj|⟨hq,hq'⟩
      · exact raw_unit_order v hP hT i j l k hi hj hc
      · constructor
        · intro ho
          have hh:=inner_order_x v j i (Ne.symm hij) ((PhysicalTiles.matching (tile j)).source k) ((PhysicalTiles.matching (tile j)).target k)
            ((PhysicalTiles.matching (tile i)).source l) ((PhysicalTiles.matching (tile i)).target l) hq hq' (congrArg Fin.val (sameRow ho).symm)
          exact hh.2.mp ho
        · intro ho
          have hh:=inner_order_y v j i (Ne.symm hij) ((PhysicalTiles.matching (tile j)).source k) ((PhysicalTiles.matching (tile j)).target k)
            ((PhysicalTiles.matching (tile i)).source l) ((PhysicalTiles.matching (tile i)).target l) hq hq' (congrArg Fin.val (sameCol ho).symm)
          exact hh.2.mp ho
    · constructor
      · intro ho
        have hh:=inner_order_x v i j hij ((PhysicalTiles.matching (tile i)).source l) ((PhysicalTiles.matching (tile i)).target l)
          ((PhysicalTiles.matching (tile j)).source k) ((PhysicalTiles.matching (tile j)).target k) hp hp' (congrArg Fin.val (sameRow ho))
        exact hh.1.mp ho
      · intro ho
        have hh:=inner_order_y v i j hij ((PhysicalTiles.matching (tile i)).source l) ((PhysicalTiles.matching (tile i)).target l)
          ((PhysicalTiles.matching (tile j)).source k) ((PhysicalTiles.matching (tile j)).target k) hp hp' (congrArg Fin.val (sameCol ho))
        exact hh.1.mp ho

/-- Every true full-board physical box retains its prescribed goal identity order. -/
theorem matching_ordered (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] []) :
    (rawSlotMatching v hP hT).Ordered where
  horizontal:=by
    rintro ⟨i,l⟩ ⟨j,k⟩ hc ho
    rw [raw_source,raw_source] at hc ho
    rw [raw_target,raw_target]
    exact (raw_order v hP hT i j l k hc).1 ho
  vertical:=by
    rintro ⟨i,l⟩ ⟨j,k⟩ hc ho
    rw [raw_source,raw_source] at hc ho
    rw [raw_target,raw_target]
    exact (raw_order v hP hT i j l k hc).2 ho

end PushPuzzle.PushFS.Reduction.PhysicalInventory
