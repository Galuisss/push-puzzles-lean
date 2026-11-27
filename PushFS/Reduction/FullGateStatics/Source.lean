/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateStatics.Thin
public import PushFS.Reduction.FullGateRawLabels

/-! All real canonical physical source identities lie in the active static chart union. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics

open Inventory Gadgets Gadgets.Wires
set_option maxHeartbeats 100000
set_option maxRecDepth 65536

def LocatedActive (g : GateTileState) (c : ChartIndex g) (p : C) : Prop :=
  ∃q : Cell (chart g c).width (chart g c).height,
    (chart g c).classifier.name q≠.outside ∧(chart g c).embedding.cells q=p

private theorem row_active_image (o : RectOrientation) (w : ℕ) (q : Cell w 21) (hq : q.2.val=10) :
    rowName o w ((o.axis w 21).geometry.cells q)≠.outside := by
  unfold rowName
  rw [Equiv.symm_apply_apply,ite_eq_left hq]
  intro he
  have hh:=((o.axis w 21).outside _).mp he
  cases hh

private theorem line_base_name (f : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool)
    (p : Cell (lineBase f n hn a b).width (lineBase f n hn a b).height) :
    (lineBaseClassifier f n hn a b).name p=if p.2.val=10 then .horizontal 10 else .outside := by
  cases f <;> rfl

private theorem line_source_active (g : GateTileState) (role : Fin 3) (j : Fin (curve
    (key g role)).length)
    (l : lineLabels (fillerFlip (key g role) j.val) (fillerSpan (key g role) j.val)) :
    LocatedActive g (.inl (.inr (.inl ⟨role,.inl j⟩))) (rawSource g ⟨.inr (.inl ⟨role,.inl j⟩),l⟩) := by
  let g0:=ofGeometry (geometry g)
  let k:=key g role
  let n:=fillerSpan k j.val
  let f:=fillerFlip k j.val
  let a:=initialPhase g role
  let b:=targetPhase g role
  let a0:=initialPhase g0 role
  let b0:=targetPhase g0 role
  have hn:2301≤n:=(filler_shape k j.val j.isLt).2.1
  let A:=lineBase f n hn a0 b0
  let o:=lineOrientation (original k j.val).travel f
  let e:=o.axis A.width A.height
  let x:=((lineMatching f n hn a b).source l).1.val
  have hb:=line_source_bounds f n hn a b l
  have hab : a.toNat≤1 := by cases a <;> decide
  let r : Cell A.width A.height := (⟨x,by
      rw [(line_dimensions f n hn a0 b0).1]
      have hh : n+(if f then 20 else 0)+a.toNat<n+(if f then 25 else 5) := by
        split_ifs <;> omega
      exact hb.2.1.trans_lt hh⟩,⟨10,by rw [(line_dimensions f n hn a0 b0).2]; decide⟩)
  let q :=e.geometry.cells r
  refine ⟨q,?_,?_⟩
  · change e.name ((lineBaseClassifier f n hn a0 b0).name (e.geometry.cells.symm (e.geometry.cells r)))≠.outside
    rw [Equiv.symm_apply_apply,line_base_name,ite_eq_left (show r.2.val=10 from rfl)]
    intro he
    cases (e.outside (.horizontal 10)).mp he
  · have he:=line_source_coordinates k j.val j.isLt a b l
    rw [RectOrientation.coordinates_point] at he
    have hd : (A.width,A.height)=((lineBase f n hn a b).width,(lineBase f n hn a b).height) :=
      Prod.ext ((line_dimensions f n hn a0 b0).1.trans (line_dimensions f n hn a b).1.symm)
        ((line_dimensions f n hn a0 b0).2.trans (line_dimensions f n hn a b).2.symm)
    have ht:=congrArg (fun wh : ℕ×ℕ=>o.point wh.1 wh.2 (x,10)) hd
    have hq:=(o.point_cells A.width A.height r).symm.trans ht
    have hx:=congrArg Prod.fst he
    have hy:=congrArg Prod.snd he
    have hqx:=congrArg Prod.fst hq
    have hqy:=congrArg Prod.snd hq
    rw [hb.2.2] at hx hy
    apply Prod.ext <;> apply Fin.ext
    · change (lineOffset k j.val).1+q.1.val=(lineOffset k j.val).1+((lineSlotMatching k j.val j.isLt a b).source l).1.val
      exact (congrArg ((lineOffset k j.val).1+·) hqx).trans hx.symm
    · change (lineOffset k j.val).2+q.2.val=(lineOffset k j.val).2+((lineSlotMatching k j.val j.isLt a b).source l).2.val
      exact (congrArg ((lineOffset k j.val).2+·) hqy).trans hy.symm

private theorem corner_name (k : Key) (i : ℕ) (a b : Bool)
    (p : Cell ((cornerOrientation k i).width (ShortCorners.width (cornerKind k i)) (ShortCorners.height (cornerKind k i)))
      ((cornerOrientation k i).height (ShortCorners.width (cornerKind k i)) (ShortCorners.height (cornerKind k i)))) :
    (cornerClassifier k i a b).name p=(cornerIso k i).name
      (ShortCorners.axisName (cornerKind k i) ((cornerIso k i).geometry.cells.symm p)) := by
  dsimp only [cornerClassifier,classifier_rebase,AxisIsometry.classifier,ShortCorners.classifier,AxisClassifier.of_strong_check,AxisClassifier.of_check]

private theorem buffer_west_name (kind : Bool) (n : ℕ) (hn : 2301≤n) (a b : Gates.Signals)
    (p : Cell (n+5) 21) :
    (bufferClassifier kind n hn a b 1).name p=rowName ⟨false,true,!kind⟩ (n+5) p := by
  cases kind <;> rfl

private theorem corner_active_image (k : Key) (i : ℕ) (a b phase : Bool) (l : Fin
    (ShortCorners.count (cornerKind k i))) :
    (cornerClassifier k i a b).name ((cornerIso k i).geometry.cells ((ShortCorners.template (cornerKind k i)).position phase l))≠.outside := by
  intro he
  have hh:=corner_name k i a b ((cornerIso k i).geometry.cells ((ShortCorners.template (cornerKind k i)).position phase l))
  have he':=hh.symm.trans he
  rw [Equiv.symm_apply_apply] at he'
  exact ShortCorners.slot_active (cornerKind k i) phase l (((cornerIso k i).outside _).mp he')

attribute [local irreducible] cornerKind cornerOrientation

private theorem corner_source_active (g : GateTileState) (role : Fin 3) (j : Fin ((curve
    (key g role)).length-1))
    (l : Fin (ShortCorners.count (cornerKind (key g role) j.val))) :
    LocatedActive g (.inl (.inr (.inl ⟨role,.inr j⟩))) (rawSource g ⟨.inr (.inl ⟨role,.inr j⟩),l⟩) := by
  let k:=key g role
  let e:=cornerIso k j.val
  let p:=(ShortCorners.template (cornerKind k j.val)).position (initialPhase g role) l
  let q:=e.geometry.cells p
  refine ⟨q,?_,?_⟩
  · change (cornerClassifier k j.val (initialPhase (ofGeometry (geometry g)) role)
      (targetPhase (ofGeometry (geometry g)) role)).name q≠.outside
    exact corner_active_image k j.val (initialPhase (ofGeometry (geometry g)) role)
      (targetPhase (ofGeometry (geometry g)) role) (initialPhase g role) l
  · have he:=corner_source_coordinates (key g role) j.val (initialPhase g role) (targetPhase g role) l
    rw [RectOrientation.coordinates_point] at he
    have hq:=((cornerOrientation k j.val).point_cells (ShortCorners.width (cornerKind k j.val))
      (ShortCorners.height (cornerKind k j.val)) p).symm
    have hx:=congrArg Prod.fst he
    have hy:=congrArg Prod.snd he
    have hqx:=congrArg Prod.fst hq
    have hqy:=congrArg Prod.snd hq
    apply Prod.ext <;> apply Fin.ext
    · change (cornerOffset (key g role) j.val).1+q.1.val=(cornerOffset (key g role) j.val).1+((cornerMatching (key g role) j.val (initialPhase g role) (targetPhase g role)).source l).1.val
      exact (congrArg ((cornerOffset (key g role) j.val).1+·) hqx).trans hx.symm
    · change (cornerOffset (key g role) j.val).2+q.2.val=(cornerOffset (key g role) j.val).2+((cornerMatching (key g role) j.val (initialPhase g role) (targetPhase g role)).source l).2.val
      exact (congrArg ((cornerOffset (key g role) j.val).2+·) hqy).trans hy.symm



private theorem west_position_active (kind : Bool) (n : ℕ) (hn : 2301≤n) (a b : Gates.Signals)
    (phase : Bool) (l : Chain.Label n) :
    (bufferClassifier kind n hn a b 1).name
      ((GateLead.westIso kind n).cells (Chain.position n hn (Chain.uniform n phase) l))≠.outside := by
  rw [buffer_west_name]
  cases kind
  · exact row_active_image ⟨false,true,true⟩ _ _ (Chain.position_row n hn _ _)
  · exact row_active_image ⟨false,true,false⟩ _ _ (Chain.position_row n hn _ _)

private theorem north_position_active (kind : Bool) (n : ℕ) (hn : 2301≤n) (a b : Gates.Signals)
    (phase : Bool) (l : Chain.Label n) :
    (bufferClassifier kind n hn a b 2).name
      ((GateLead.northIso n).cells (Chain.position n hn (Chain.uniform n phase) l))≠.outside :=
  row_active_image ⟨true,true,true⟩ _ _ (Chain.position_row n hn _ _)

private theorem east_position_active (kind : Bool) (n : ℕ) (hn : 2301≤n) (a b : Gates.Signals)
    (phase : Bool) (l : Chain.Label n) :
    (bufferClassifier kind n hn a b 3).name
      ((GateLead.eastIso n).cells (Chain.position n hn (Chain.uniform n phase) l))≠.outside :=
  row_active_image ⟨false,false,true⟩ _ _ (Chain.position_row n hn _ _)

private theorem buffer_source_located (kind : Bool) (n : ℕ) (hn : 2301≤n)
    (a b c d : Gates.Signals) (i : Fin 4) (l : GateLead.Labels kind n i) :
    ∃q : Cell (GateLead.piece kind n hn c d i).width (GateLead.piece kind n hn c d i).height,
      (bufferClassifier kind n hn c d i).name q≠.outside ∧
      q.1.val=((GateLead.matching kind n hn a b i).source l).1.val ∧
      q.2.val=((GateLead.matching kind n hn a b i).source l).2.val := by
  fin_cases i
  · refine ⟨(Gates.slotMatching kind a b).source l,?_,rfl,rfl⟩
    exact Gates.slot_position_active kind (Gates.slots kind)[l.val] (List.getElem_mem l.isLt) a
  · exact ⟨_,west_position_active kind n hn c d a.left l,rfl,rfl⟩
  · exact ⟨_,north_position_active kind n hn c d a.upper l,rfl,rfl⟩
  · exact ⟨_,east_position_active kind n hn c d (!a.right) l,rfl,rfl⟩

private theorem buffer_source_active (g : GateTileState) (i : Fin 4) (l : GateLead.Labels g.core.isAND 2301 i) :
    LocatedActive g (.inl (.inl i)) (rawSource g ⟨.inl i,l⟩) := by
  obtain ⟨q,hq,hx,hy⟩:=buffer_source_located g.core.isAND 2301 (by omega)
    g.core.initial g.core.target (ofGeometry (geometry g)).core.initial (ofGeometry (geometry g)).core.target i l
  refine ⟨q,hq,?_⟩
  apply Prod.ext <;> apply Fin.ext
  · change (Inventory.offset (ofGeometry (geometry g)) (.inl i)).1+q.1.val=
      (Inventory.offset g (.inl i)).1+((GateLead.matching g.core.isAND 2301 (by omega) g.core.initial g.core.target i).source l).1.val
    rw [hx]
    rfl
  · change (Inventory.offset (ofGeometry (geometry g)) (.inl i)).2+q.2.val=
      (Inventory.offset g (.inl i)).2+((GateLead.matching g.core.isAND 2301 (by omega) g.core.initial g.core.target i).source l).2.val
    rw [hy]
    rfl

theorem raw_source_active (g : GateTileState) (l : RawLabel g) : ∃c,LocatedActive g c (rawSource g l) := by
  rcases l with ⟨i,l⟩
  rcases i with i|(⟨role,j|j⟩|role)
  · exact ⟨_,buffer_source_active g i l⟩
  · exact ⟨_,line_source_active g role j l⟩
  · exact ⟨_,corner_source_active g role j l⟩
  · exact Fin.elim0 l

end PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics
