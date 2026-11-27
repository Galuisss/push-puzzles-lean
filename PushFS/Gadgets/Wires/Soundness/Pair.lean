/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Soundness.Track
public import PushFS.Gadgets.Wires.Soundness.Strip
public import PushFS.Placement

/-! Strip obstructions applied to arbitrary successful physical-label trajectories. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Soundness


variable {I : Instance} {Label : Type} [Fintype Label]

/-- Two physical identities, retaining the full actual puzzle state and player. -/
def pair (S : LabelledState Label I.width I.height) (i j : Label) : Configuration I.width I.height :=
  ⟨S.state,S.position i,S.position j⟩

theorem pair_tracked {S T : LabelledState Label I.width I.height}
    (hs : LabelledState.Step I.board S T) (i j : Label) : TrackedStep I.board (pair S i j) (pair T i j) := by
  obtain ⟨d,hm,hw|hp⟩ := hs
  · exact ⟨d,hm,Or.inl ⟨hw.1,congrFun hw.2 i,congrFun hw.2 j⟩⟩
  · obtain ⟨q,hq,ha,he,hb,hp⟩ := hp
    exact ⟨d,hm,Or.inr ⟨q,hq,ha,he,hb,congrFun hp i,congrFun hp j⟩⟩

namespace Successful

variable {M : SlotMatching I Label} {S final : LabelledState Label I.width I.height}

private theorem pair_shape (h : Successful M S final) (A : AxisTracks I) (y : ℕ) (i j : Label)
    (hi : A.name (M.source i) = .horizontal y) (hj : A.name (M.source j) = .horizontal y)
    (hij : (M.source i).1.val < (M.source j).1.val) : Shape y (pair S i j) :=
  ⟨S.position_mem i,S.position_mem j,h.line A true y i hi,h.line A true y j hj,
    h.order A true y i j hi hj hij⟩

/-- The strip invariant follows with all intermediate geometry discharged by real tracks and identities. -/
theorem strip_good (h : Successful M S final) (cert : Certificate I) (ho : M.Ordered)
    (A : AxisTracks I) (lo hi y : ℕ) (i j : Label)
    (hw : StripWalls I.board lo hi y)
    (hirow : A.name (M.source i) = .horizontal y) (hjrow : A.name (M.source j) = .horizontal y)
    (hij : (M.source i).1.val < (M.source j).1.val)
    (hstart : (M.source i).1.val+1 < lo ∨ hi+1 < (M.source j).1.val)
    (hfinish : (M.target i).1.val+1 < lo ∨ hi+1 < (M.target j).1.val) : Good lo hi (pair S i j) := by
  have hstep U V (hu : Successful M U final) (hv : Successful M V final)
      (hs : LabelledState.Step I.board U V) : GeometricStep I.board y (pair U i j) (pair V i j) :=
    ⟨hu.pair_shape A y i j hirow hjrow hij,hv.pair_shape A y i j hirow hjrow hij,pair_tracked hs i j⟩
  have hb := map_successful (fun U => pair U i j) h.before (.refl) h.after h.solved hstep
  have ha := map_successful (fun U => pair U i j) h.after h.before (.refl) h.solved hstep
  apply good_on_successful_path (initial := pair M.initialLabelled i j)
    (S := pair S i j) (final := pair final i j) hw hstart (hbefore := hb) (hafter := ha)
  have ht := h.target ho cert
  simpa only [Good,pair,ht] using hfinish

end Successful

namespace StripWalls

variable {w h W H : ℕ} {B : Board w h} {ambient : Board W H} {lo hi y : ℕ}

/-- A finite literal strip wall certificate survives exact translation into the ambient wall table. -/
theorem translate (hw : StripWalls B lo hi y) (hhi : hi < w) (hy0 : 0 < y) (hy : y+1 < h)
    (dx dy : ℕ) (hx : dx+w ≤ W) (hh : dy+h ≤ H)
    (he : (GridEmbedding.translate dx dy hx hh).WallsAgree B ambient) :
    StripWalls ambient (dx+lo) (dx+hi) (dy+y) := by
  have wall (p : Cell W H) (hpx : dx+lo ≤ p.1.val) (hpx' : p.1.val ≤ dx+hi)
      (hpy : p.2.val = dy+y+1 ∨ p.2.val+1 = dy+y) : p ∈ ambient.walls := by
    let q : Cell w h := (⟨p.1.val-dx,by omega⟩,⟨p.2.val-dy,by omega⟩)
    have hq : (GridEmbedding.translate dx dy hx hh).cells q = p := by
      apply Prod.ext <;> apply Fin.ext <;> dsimp [GridEmbedding.translate,q] <;> omega
    have hqw : q ∈ B.walls := by
      rcases hpy with hp | hp
      · exact hw.below q (by dsimp [q]; omega) (by dsimp [q]; omega) (by dsimp [q]; omega)
      · exact hw.above q (by dsimp [q]; omega) (by dsimp [q]; omega) (by dsimp [q]; omega)
    exact hq ▸ (he q).mpr hqw
  exact ⟨fun p hp hl hh => wall p hl hh (Or.inl hp), fun p hp hl hh => wall p hl hh (Or.inr hp)⟩

end StripWalls
end PushPuzzle.PushFS.Gadgets.Wires.Soundness
