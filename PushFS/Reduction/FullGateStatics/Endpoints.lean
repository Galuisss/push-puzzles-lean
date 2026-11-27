/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateStatics.Thin

/-! The small checked boundary lists contain every actual active primitive chart endpoint. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics

open Inventory Gadgets Gadgets.Wires Gadgets.Wires.Catalog
set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

private theorem short_wide : ∀(o : RectOrientation) (k : ShortCorners.Kind),
    o.width (ShortCorners.width k) (ShortCorners.height k)≠21 ∧
    o.height (ShortCorners.width k) (ShortCorners.height k)≠21 := by decide +kernel

private theorem cap_wide : ∀d : Direction,(capOrientation d).width 1 3≠21 ∧(capOrientation d).height 1 3≠21 := by decide +kernel

private theorem ribbon_wide : ∀d : Direction,ribbonWidth d≠21 ∧ribbonHeight d≠21 := by decide +kernel

private theorem wide_boundary_edge (C : TranslatedAxisChart 200007 198068)
    (hw : C.width≠21) (hh : C.height≠21) (p : Cell C.width C.height)
    (hp : p.1.val=0 ∨p.1.val+1=C.width ∨p.2.val=0 ∨p.2.val+1=C.height) :
    (p.1.val,p.2.val)∈(shape C).boundary := by
  simp only [Shape.boundary,shape,hw,hh,ite_false]
  exact perimeter_complete (shape C) _ p.1.isLt p.2.isLt hp

theorem raw_boundary_edge (k : Geometry) (c : ChartIndex (ofGeometry k))
    (p : Cell (rawChart (ofGeometry k) c).width (rawChart (ofGeometry k) c).height)
    (ha : (rawChart (ofGeometry k) c).classifier.name p≠.outside)
    (hp : p.1.val=0 ∨p.1.val+1=(rawChart (ofGeometry k) c).width ∨
      p.2.val=0 ∨p.2.val+1=(rawChart (ofGeometry k) c).height) :
    (p.1.val,p.2.val)∈(shape (rawChart (ofGeometry k) c)).boundary := by
  revert p
  rcases k with ⟨kind,pattern,rotation,incoming⟩
  let a : Gates.Signals:=⟨false,false,false⟩
  let b : Gates.Signals:=⟨false,false,false⟩
  let g : GateTileState:=ofGeometry (kind,pattern,rotation,incoming)
  rcases c with i | role
  · rcases i with i | (⟨role,j | j⟩ | role)
    · fin_cases i
      all_goals intro p ha hp
      · apply wide_boundary_edge (rawChart g (.inl (.inl 0))) (by change 81≠21; decide) (by change 107≠21; decide) p hp
      · change Cell 2306 21 at p
        have hr : p.2.val=10 := by
          cases kind
          · dsimp only [rawChart,primitiveChart,primitiveClassifier,rawClassifier] at ha
            change rowName ⟨false,true,true⟩ 2306 p≠.outside at ha
            exact row_active ⟨false,true,true⟩ 2306 p ha
          · dsimp only [rawChart,primitiveChart,primitiveClassifier,rawClassifier] at ha
            change rowName ⟨false,true,false⟩ 2306 p≠.outside at ha
            exact row_active ⟨false,true,false⟩ 2306 p ha
        have hb:=hp
        change p.1.val=0 ∨p.1.val+1=2306 ∨p.2.val=0 ∨p.2.val+1=21 at hb
        clear ha hp
        change (p.1.val,p.2.val)∈[(0,10),(2305,10)]
        simp only [List.mem_cons,Prod.mk.injEq]
        omega
      · change Cell 21 2306 at p
        dsimp only [rawChart,primitiveChart,primitiveClassifier,rawClassifier] at ha
        change rowName ⟨true,true,true⟩ 2306 p≠.outside at ha
        have hr:=row_active ⟨true,true,true⟩ 2306 p ha
        change p.1.val=10 at hr
        have hb:=hp
        change p.1.val=0 ∨p.1.val+1=21 ∨p.2.val=0 ∨p.2.val+1=2306 at hb
        clear ha hp
        change (p.1.val,p.2.val)∈[(10,0),(10,2305)]
        simp only [List.mem_cons,Prod.mk.injEq]
        omega
      · change Cell 2306 21 at p
        dsimp only [rawChart,primitiveChart,primitiveClassifier,rawClassifier] at ha
        change rowName ⟨false,false,true⟩ 2306 p≠.outside at ha
        have hr:=row_active ⟨false,false,true⟩ 2306 p ha
        change p.2.val=10 at hr
        have hb:=hp
        change p.1.val=0 ∨p.1.val+1=2306 ∨p.2.val=0 ∨p.2.val+1=21 at hb
        clear ha hp
        change (p.1.val,p.2.val)∈[(0,10),(2305,10)]
        simp only [List.mem_cons,Prod.mk.injEq]
        omega
    · intro p ha hp
      have hd:=linePiece_dimensions (key g role) j.val j.isLt (initialPhase g role) (targetPhase g role)
      change (rawChart g (.inl (.inr (.inl ⟨role,.inl j⟩)))).width=_ ∧
        (rawChart g (.inl (.inr (.inl ⟨role,.inl j⟩)))).height=_ at hd
      have hw : 21<lineWidth (key g role) j.val := by
        have hn:=(filler_shape (key g role) j.val j.isLt).2.1
        unfold lineWidth
        split_ifs <;> omega
      have haxis (q : Cell (rawChart g (.inl (.inr (.inl ⟨role,.inl j⟩)))).width
          (rawChart g (.inl (.inr (.inl ⟨role,.inl j⟩)))).height)
          (hq : (rawChart g (.inl (.inr (.inl ⟨role,.inl j⟩)))).classifier.name q≠.outside) :
          if (original (key g role) j.val).travel=.east ∨(original (key g role) j.val).travel=.west then q.2.val=10 else q.1.val=10 :=
        line_active (original (key g role) j.val).travel (fillerFlip (key g role) j.val) (fillerSpan (key g role) j.val)
          (filler_shape (key g role) j.val j.isLt).2.1 (initialPhase g role) (targetPhase g role) q hq
      have hb:=hp
      apply thin_boundary_nat (shape (rawChart g (.inl (.inr (.inl ⟨role,.inl j⟩)))))
        (p.1.val,p.2.val) p.1.isLt p.2.isLt hb
      change ((rawChart g (.inl (.inr (.inl ⟨role,.inl j⟩)))).width=21 ∧
          21<(rawChart g (.inl (.inr (.inl ⟨role,.inl j⟩)))).height ∧p.1.val=10) ∨
        (21<(rawChart g (.inl (.inr (.inl ⟨role,.inl j⟩)))).width ∧
          (rawChart g (.inl (.inr (.inl ⟨role,.inl j⟩)))).height=21 ∧p.2.val=10)
      cases ht : (original (key g role) j.val).travel
      all_goals simp only [ht,lineOrientation,RectOrientation.width,RectOrientation.height,Bool.false_eq_true,ite_true,ite_false] at hd
      · exact Or.inl ⟨hd.1,by omega,by simpa [ht] using haxis p ha⟩
      · exact Or.inr ⟨by omega,hd.2,by simpa [ht] using haxis p ha⟩
      · exact Or.inl ⟨hd.1,by omega,by simpa [ht] using haxis p ha⟩
      · exact Or.inr ⟨by omega,hd.2,by simpa [ht] using haxis p ha⟩
    · intro p ha hp
      exact wide_boundary_edge (rawChart g (.inl (.inr (.inl ⟨role,.inr j⟩)))) (short_wide (cornerOrientation (key g role) j.val) (cornerKind (key g role) j.val)).1
        (short_wide (cornerOrientation (key g role) j.val) (cornerKind (key g role) j.val)).2 p hp
    · intro p ha hp
      exact wide_boundary_edge (rawChart g (.inl (.inr (.inr role)))) (cap_wide (PortAnnulus.outerDirection (g.key role.val).2)).1
        (cap_wide (PortAnnulus.outerDirection (g.key role.val).2)).2 p hp
  · intro p ha hp
    exact wide_boundary_edge (rawChart g (.inr role)) (ribbon_wide (PortAnnulus.outerDirection (g.key role).2)).1
      (ribbon_wide (PortAnnulus.outerDirection (g.key role).2)).2 p hp

theorem boundary_complete (g : GateTileState) (c : ChartIndex g)
    (p : Cell (chart g c).width (chart g c).height) (ha : (chart g c).classifier.name p≠.outside)
    (hp : ¬BoundaryAligned (W:=200007) (H:=198068) (chart g c).dx (chart g c).dy p) :
    (p.1.val,p.2.val)∈(shape (chart g c)).boundary := raw_boundary_edge (geometry g) c p ha
  (not_aligned_boundary (chart g c).dx (chart g c).dy p hp)

end PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics
