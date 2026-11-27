/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.PlacedTracks
public import PushFS.Gadgets.Wires.Catalog.RotateCertificate

/-! Complete supported axial classifiers, C1–C3 and exact target order for all seven padded physical cells. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog

set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

private theorem row_active {w h : ℕ} (p : PushFS.Cell w h)
    (hp : (if p.2.val=10 then AxisTrack.horizontal 10 else .outside)≠.outside) : p.2.val=10 := by
  by_contra he
  simp only [he,ite_false,ne_self_iff_false] at hp

private theorem corner_active {w h : ℕ} (p : PushFS.Cell w h)
    (hp : (if p.1.val=10 ∧p.2.val=10 then AxisTrack.sink 10 10
      else if p.2.val=10 ∧10<p.1.val then .horizontal 10
      else if p.1.val=10 ∧10<p.2.val then .vertical 10 else .outside)≠.outside) :
    10≤p.1.val ∧10≤p.2.val := by
  split at hp
  · omega
  · split at hp
    · omega
    · split at hp
      · omega
      · contradiction

/-- Every active local boundary lies on the genuine finite logic-cell boundary. -/
theorem base_aligned (k : Kind) (a b : Bool) (p : PushFS.Cell (base k a b).width (base k a b).height)
    (hp : (baseStrong k a b).axes.name p≠.outside) :
    BoundaryAligned (W:=width) (H:=height) (dx k) (dy k) p := by
  cases k
  · have hb:=row_active p hp
    change (p.1.val=0→0=0) ∧ (p.1.val+1=200005→0+200005=200005) ∧
      (p.2.val=0→99023=0) ∧ (p.2.val+1=21→99023+21=198066)
    have hx:=p.1.isLt
    have hy:=p.2.isLt
    refine ⟨?_,?_,?_,?_⟩ <;> intro he <;> omega
  · obtain ⟨q,hq⟩:=(GridIsometry.reflectX 200005 21).cells.surjective p
    have he : p=(GridIsometry.reflectX 200005 21).cells (q) := hq.symm
    subst p
    have hraw : (chainStrong 200000 (by decide) a b).axes.name q≠.outside := ((chainStrong 200000 (by decide) a b).rotate_active (AxisIsometry.reflectX 200005 21) (q) (hp))
    have hb:=row_active q hraw
    change (200005-(q.1.val+1)=0→0=0) ∧ (200005-(q.1.val+1)+1=200005→0+200005=200005) ∧
      (q.2.val=0→99023=0) ∧ (q.2.val+1=21→99023+21=198066)
    have hx:=q.1.isLt
    have hy:=q.2.isLt
    refine ⟨?_,?_,?_,?_⟩ <;> intro he <;> omega
  · obtain ⟨q,hq⟩:=((GridIsometry.transpose 198066 21).trans (GridIsometry.reflectX 21 198066)).cells.surjective p
    have he : p=(GridIsometry.reflectX 21 198066).cells ((GridIsometry.transpose 198066 21).cells (q)) := hq.symm
    subst p
    have hraw : (chainStrong 198061 (by decide) a b).axes.name q≠.outside := ((chainStrong 198061 (by decide) a b).rotate_active (AxisIsometry.transpose 198066 21) (q) ((((chainStrong 198061 (by decide) a b).rotate (AxisIsometry.transpose 198066 21)).rotate_active (AxisIsometry.reflectX 21 198066) ((GridIsometry.transpose 198066 21).cells (q)) (hp))))
    have hb:=row_active q hraw
    change (21-(q.2.val+1)=0→99992=0) ∧ (21-(q.2.val+1)+1=21→99992+21=200005) ∧
      (q.1.val=0→0=0) ∧ (q.1.val+1=198066→0+198066=198066)
    have hx:=q.1.isLt
    have hy:=q.2.isLt
    refine ⟨?_,?_,?_,?_⟩ <;> intro he <;> omega
  · have hb:=corner_active p hp
    change (p.1.val=0→99992=0) ∧ (p.1.val+1=100013→99992+100013=200005) ∧
      (p.2.val=0→99023=0) ∧ (p.2.val+1=99043→99023+99043=198066)
    have hx:=p.1.isLt
    have hy:=p.2.isLt
    refine ⟨?_,?_,?_,?_⟩ <;> intro he <;> omega
  · obtain ⟨q,hq⟩:=(GridIsometry.reflectX 100013 99043).cells.surjective p
    have he : p=(GridIsometry.reflectX 100013 99043).cells (q) := hq.symm
    subst p
    have hraw : (outStrong 99970 98979 (by decide) (by decide) a b).axes.name q≠.outside := ((outStrong 99970 98979 (by decide) (by decide) a b).rotate_active (AxisIsometry.reflectX 100013 99043) (q) (hp))
    have hb:=corner_active q hraw
    change (100013-(q.1.val+1)=0→0=0) ∧ (100013-(q.1.val+1)+1=100013→0+100013=200005) ∧
      (q.2.val=0→99023=0) ∧ (q.2.val+1=99043→99023+99043=198066)
    have hx:=q.1.isLt
    have hy:=q.2.isLt
    refine ⟨?_,?_,?_,?_⟩ <;> intro he <;> omega
  · obtain ⟨q,hq⟩:=((GridIsometry.reflectX 99044 100013).trans (GridIsometry.transpose 99044 100013)).cells.surjective p
    have he : p=(GridIsometry.transpose 99044 100013).cells ((GridIsometry.reflectX 99044 100013).cells (q)) := hq.symm
    subst p
    have hraw : (inStrong 98981 99969 (by decide) (by decide) a b).axes.name q≠.outside := ((inStrong 98981 99969 (by decide) (by decide) a b).rotate_active (AxisIsometry.reflectX 99044 100013) (q) ((((inStrong 98981 99969 (by decide) (by decide) a b).rotate (AxisIsometry.reflectX 99044 100013)).rotate_active (AxisIsometry.transpose 99044 100013) ((GridIsometry.reflectX 99044 100013).cells (q)) (hp))))
    have hb:=corner_active q hraw
    change (q.2.val=0→99992=0) ∧ (q.2.val+1=100013→99992+100013=200005) ∧
      (99044-(q.1.val+1)=0→0=0) ∧ (99044-(q.1.val+1)+1=99044→0+99044=198066)
    have hx:=q.1.isLt
    have hy:=q.2.isLt
    refine ⟨?_,?_,?_,?_⟩ <;> intro he <;> omega
  · obtain ⟨q,hq⟩:=(((GridIsometry.reflectX 99044 100013).trans (GridIsometry.transpose 99044 100013)).trans (GridIsometry.reflectX 100013 99044)).cells.surjective p
    have he : p=(GridIsometry.reflectX 100013 99044).cells ((GridIsometry.transpose 99044 100013).cells ((GridIsometry.reflectX 99044 100013).cells (q))) := hq.symm
    subst p
    have hraw : (normalStrong 99001 99969 (by decide) (by decide) a b).axes.name q≠.outside := ((normalStrong 99001 99969 (by decide) (by decide) a b).rotate_active (AxisIsometry.reflectX 99044 100013) (q) ((((normalStrong 99001 99969 (by decide) (by decide) a b).rotate (AxisIsometry.reflectX 99044 100013)).rotate_active (AxisIsometry.transpose 99044 100013) ((GridIsometry.reflectX 99044 100013).cells (q)) (((((normalStrong 99001 99969 (by decide) (by decide) a b).rotate (AxisIsometry.reflectX 99044 100013)).rotate (AxisIsometry.transpose 99044 100013)).rotate_active (AxisIsometry.reflectX 100013 99044) ((GridIsometry.transpose 99044 100013).cells ((GridIsometry.reflectX 99044 100013).cells (q))) (hp))))))
    have hb:=corner_active q hraw
    change (100013-(q.2.val+1)=0→0=0) ∧ (100013-(q.2.val+1)+1=100013→0+100013=200005) ∧
      (99044-(q.1.val+1)=0→0=0) ∧ (99044-(q.1.val+1)+1=99044→0+99044=198066)
    have hx:=q.1.isLt
    have hy:=q.2.isLt
    refine ⟨?_,?_,?_,?_⟩ <;> intro he <;> omega

noncomputable def axisTracks (k : Kind) (a b : Bool) : AxisTracks (puzzle k a b) :=
  placedAxisTracks (baseMatching k a b) (baseStrong k a b) (dx k) (dy k)
    (fitsX k a b) (fitsY k a b) (base_aligned k a b)

end PushPuzzle.PushFS.Gadgets.Wires.Catalog
