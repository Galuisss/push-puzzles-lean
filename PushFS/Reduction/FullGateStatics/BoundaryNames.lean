/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateStatics.Classifier
public import PushFS.Reduction.FullGateStatics.BoundaryNamesChecked

/-! Exact active names at the four outer edges of every complete physical gate. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics

open Inventory
set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem chart_edge_name (g : GateTileState) (c : ChartIndex g)
    (q : Cell (chart g c).width (chart g c).height)
    (ha : (chart g c).classifier.name q≠.outside)
    (he : OnEdge (((chart g c).embedding.cells q).1.val,((chart g c).embedding.cells q).2.val)) :
    AxisTrack.shift (chart g c).dx (chart g c).dy ((chart g c).classifier.name q)=
      edgeName g (((chart g c).embedding.cells q).1.val,((chart g c).embedding.cells q).2.val) := by
  have hx:=q.1.isLt
  have hy:=q.2.isLt
  have hfx:=(chart g c).fits_x
  have hfy:=(chart g c).fits_y
  have hb : q.1.val=0 ∨q.1.val+1=(chart g c).width ∨
      q.2.val=0 ∨q.2.val+1=(chart g c).height := by
    change OnEdge ((chart g c).dx+q.1.val,(chart g c).dy+q.2.val) at he
    dsimp only [OnEdge] at he
    omega
  have hmem:=raw_boundary_edge (geometry g) c q ha hb
  have ht:=List.all_eq_true.mp (List.all_eq_true.mp (edgeNames_all g) c (mem_chartIndices g c))
    (q.1.val,q.2.val) hmem
  change (if (shape (chart g c)).name (q.1.val,q.2.val)≠.outside ∧
      OnEdge ((shape (chart g c)).global (q.1.val,q.2.val)) then _ else true)=true at ht
  rw [shape_name] at ht
  rw [ite_eq_left (show (chart g c).classifier.name q≠.outside ∧
      OnEdge ((shape (chart g c)).global (q.1.val,q.2.val)) from ⟨ha,he⟩)] at ht
  exact of_decide_eq_true ht

theorem classifier_edge_name (g : GateTileState) (p : C)
    (ha : (classifier g).name p≠.outside) (he : OnEdge (p.1.val,p.2.val)) :
    (classifier g).name p=edgeName g (p.1.val,p.2.val) := by
  obtain ⟨c,q,hq,hn⟩:=(mosaic g).attained p ha
  change (chart g c).embedding.cells q=p at hq
  change AxisTrack.shift (chart g c).dx (chart g c).dy ((chart g c).classifier.name q)=
    (classifier g).name p at hn
  have hqa : (chart g c).classifier.name q≠.outside := by
    intro hh
    rw [hh] at hn
    exact ha hn.symm
  have hh:=chart_edge_name g c q hqa (hq.symm ▸he)
  rw [hq] at hh
  exact hn.symm.trans hh

def outerTrack : Direction→AxisTrack
  | .west | .east=>.horizontal 99034
  | .north | .south=>.vertical 100003

private theorem ribbon_bounds (d : Direction) (p : C)
    (hf : FullGateBoundary.InFrame d (p.1.val,p.2.val)) (hr : (outerTrack d).Supports p) :
    (ribbonOffset d).1≤p.1.val ∧p.1.val<(ribbonOffset d).1+ribbonWidth d ∧
      (ribbonOffset d).2≤p.2.val ∧p.2.val<(ribbonOffset d).2+ribbonHeight d := by
  have hx:=p.1.isLt
  have hy:=p.2.isLt
  cases d <;> dsimp only [outerTrack,AxisTrack.Supports,FullGateBoundary.InFrame,
    ribbonOffset,ribbonWidth,ribbonHeight] at hf hr ⊢ <;> omega

private theorem ribbon_name (d : Direction) (q : Cell (ribbonWidth d) (ribbonHeight d)) (p : C)
    (he : (ribbonChart d).embedding.cells q=p) (hr : (outerTrack d).Supports p) :
    AxisTrack.shift (ribbonOffset d).1 (ribbonOffset d).2 ((ribbonClassifier d).name q)=outerTrack d := by
  have hx:=congrArg (fun z : C=>z.1.val) he
  have hy:=congrArg (fun z : C=>z.2.val) he
  change (ribbonOffset d).1+q.1.val=p.1.val at hx
  change (ribbonOffset d).2+q.2.val=p.2.val at hy
  revert q
  cases d <;> intro q he hx hy
  all_goals
    dsimp only [outerTrack,AxisTrack.Supports,ribbonOffset] at hr hx hy
    dsimp only [ribbonClassifier,AxisClassifier.of_strong_check,AxisClassifier.of_check,
      ribbonName,ribbonOffset,outerTrack]
    split_ifs <;> simp_all [AxisTrack.shift]
  all_goals omega

theorem classifier_port_level (g : GateTileState) (d : Direction)
    (hu : FullGateBoundary.Used g d) (p : C)
    (hf : FullGateBoundary.InFrame d (p.1.val,p.2.val))
    (hr : (outerTrack d).Supports p) : (outerTrack d).level≤((classifier g).name p).level := by
  obtain ⟨role,rfl⟩:=hu
  let d:=PortAnnulus.outerDirection (g.key role).2
  have hx:=p.1.isLt
  have hy:=p.2.isLt
  have hb:=ribbon_bounds d p hf hr
  let q : Cell (ribbonWidth d) (ribbonHeight d) :=
    (⟨p.1.val-(ribbonOffset d).1,by omega⟩,⟨p.2.val-(ribbonOffset d).2,by omega⟩)
  have he : (ribbonChart d).embedding.cells q=p := by
    apply Prod.ext <;> apply Fin.ext
    · change (ribbonOffset d).1+(p.1.val-(ribbonOffset d).1)=p.1.val
      omega
    · change (ribbonOffset d).2+(p.2.val-(ribbonOffset d).2)=p.2.val
      omega
  have hn:=ribbon_name d q p he hr
  have hrepr : (mosaic g).Represents p (outerTrack d) := ⟨.inr role,q,he,hn⟩
  exact (mosaic g).represented_le hrepr

end PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateStatics
