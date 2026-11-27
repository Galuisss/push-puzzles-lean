/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module
public import PushFS.Gadgets.Wires.Catalog.PreparedFrames
import Mathlib.Tactic.NormNum

/-! Two literal external collar cells suffice for all actual seven-cell native macro preparations. -/
@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog

set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def sourceCollar : Kind→Cell
  | .east | .eastSouth=>(0,99033)
  | .west | .westSouth=>(200004,99033)
  | .south | .southEast | .southWest=>(100002,0)
def targetCollar : Kind→Cell
  | .east | .southEast=>(200003,99033)
  | .west | .southWest=>(1,99033)
  | .south | .westSouth | .eastSouth=>(100002,198064)
def PreparedMask (k : Kind) (p : Cell) : Prop:=p=sourceCollar k ∨p=targetCollar k

private def nativeLocal (k : Kind) (a b : Bool) := nativeEmbedding k a b
    (GridIsometry.refl width height).embedding

private theorem collar0 (a b : Bool) (p : Chain.C 200000)
    (hp : PreparedMask .east ((nativeLocal .east a b).cells p)) : p∈Chain.neighbors 200000 := by
  have hpx:=p.1.isLt
  have hpy:=p.2.isLt
  rcases hp with hp|hp
  all_goals have hx:=congrArg (fun q : Cell=>q.1.val) hp
  all_goals have hy:=congrArg (fun q : Cell=>q.2.val) hp
  all_goals change 0+(p.1.val)=_ at hx
  all_goals change 99023+(p.2.val)=_ at hy
  all_goals dsimp only [sourceCollar,targetCollar] at hx hy
  all_goals simp only [Chain.neighbors,Finset.mem_insert,Finset.mem_singleton,Prod.ext_iff,Fin.ext_iff]
  all_goals norm_num [width,height] at hx hy ⊢
  all_goals simp only [Fin.ext_iff,Fin.val_zero] at hx hy ⊢
  all_goals omega

private theorem collar1 (a b : Bool) (p : Chain.C 200000)
    (hp : PreparedMask .west ((nativeLocal .west a b).cells p)) : p∈Chain.neighbors 200000 := by
  have hpx:=p.1.isLt
  have hpy:=p.2.isLt
  rcases hp with hp|hp
  all_goals have hx:=congrArg (fun q : Cell=>q.1.val) hp
  all_goals have hy:=congrArg (fun q : Cell=>q.2.val) hp
  all_goals change 0+(200005-((p.1.val)+1))=_ at hx
  all_goals change 99023+(p.2.val)=_ at hy
  all_goals dsimp only [sourceCollar,targetCollar] at hx hy
  all_goals simp only [Chain.neighbors,Finset.mem_insert,Finset.mem_singleton,Prod.ext_iff,Fin.ext_iff]
  all_goals norm_num [width,height] at hx hy ⊢
  all_goals simp only [Fin.ext_iff,Fin.val_zero] at hx hy ⊢
  all_goals omega

private theorem collar2 (a b : Bool) (p : Chain.C 198061)
    (hp : PreparedMask .south ((nativeLocal .south a b).cells p)) : p∈Chain.neighbors 198061 := by
  have hpx:=p.1.isLt
  have hpy:=p.2.isLt
  rcases hp with hp|hp
  all_goals have hx:=congrArg (fun q : Cell=>q.1.val) hp
  all_goals have hy:=congrArg (fun q : Cell=>q.2.val) hp
  all_goals change 99992+(21-((p.2.val)+1))=_ at hx
  all_goals change 0+(p.1.val)=_ at hy
  all_goals dsimp only [sourceCollar,targetCollar] at hx hy
  all_goals simp only [Chain.neighbors,Finset.mem_insert,Finset.mem_singleton,Prod.ext_iff,Fin.ext_iff]
  all_goals norm_num [width,height] at hx hy ⊢
  all_goals simp only [Fin.ext_iff,Fin.val_zero] at hx hy ⊢
  all_goals omega

private theorem collar3 (a b : Bool) (p : Chain.C 99970)
    (hp : PreparedMask .westSouth (((Polyline.L.inEmbed 99970 98999 (by decide) (by decide)).trans (nativeLocal .westSouth a b)).cells p)) : p∈Chain.neighbors 99970 := by
  have hpx:=p.1.isLt
  have hpy:=p.2.isLt
  rcases hp with hp|hp
  all_goals have hx:=congrArg (fun q : Cell=>q.1.val) hp
  all_goals have hy:=congrArg (fun q : Cell=>q.2.val) hp
  all_goals change 99992+(38+(99975-(p.1.val+1)))=_ at hx
  all_goals change 99023+(0+p.2.val)=_ at hy
  all_goals dsimp only [sourceCollar,targetCollar] at hx hy
  all_goals simp only [Chain.neighbors,Finset.mem_insert,Finset.mem_singleton,Prod.ext_iff,Fin.ext_iff]
  all_goals norm_num [width,height] at hx hy ⊢
  all_goals simp only [Fin.ext_iff,Fin.val_zero] at hx hy ⊢
  all_goals omega

private theorem collar4 (a b : Bool) (p : Turn.C)
    (hp : PreparedMask .westSouth (((Polyline.L.turnRect 99970 98999 (by decide) (by decide)).trans (nativeLocal .westSouth a b)).cells p)) : p∈Turn.template.neighbors := by
  have hpx:=p.1.isLt
  have hpy:=p.2.isLt
  rcases hp with hp|hp
  all_goals have hx:=congrArg (fun q : Cell=>q.1.val) hp
  all_goals have hy:=congrArg (fun q : Cell=>q.2.val) hp
  all_goals change 99992+(0+p.1.val)=_ at hx
  all_goals change 99023+(1+p.2.val)=_ at hy
  all_goals dsimp only [sourceCollar,targetCollar] at hx hy
  all_goals simp only [Turn.template,Turn.neighbors,Finset.mem_insert,Finset.mem_singleton,Prod.ext_iff,Fin.ext_iff]
  all_goals norm_num [width,height] at hx hy ⊢
  all_goals omega

private theorem collar5 (a b : Bool) (p : Chain.C 98999)
    (hp : PreparedMask .westSouth (((Polyline.L.outEmbed 99970 98999 (by decide) (by decide)).trans (nativeLocal .westSouth a b)).cells p)) : p∈Chain.neighbors 98999 := by
  have hpx:=p.1.isLt
  have hpy:=p.2.isLt
  rcases hp with hp|hp
  all_goals have hx:=congrArg (fun q : Cell=>q.1.val) hp
  all_goals have hy:=congrArg (fun q : Cell=>q.2.val) hp
  all_goals change 99992+(0+(21-(p.2.val+1)))=_ at hx
  all_goals change 99023+(39+p.1.val)=_ at hy
  all_goals dsimp only [sourceCollar,targetCollar] at hx hy
  all_goals simp only [Chain.neighbors,Finset.mem_insert,Finset.mem_singleton,Prod.ext_iff,Fin.ext_iff]
  all_goals norm_num [width,height] at hx hy ⊢
  all_goals simp only [Fin.ext_iff,Fin.val_zero] at hx hy ⊢
  all_goals omega

private theorem collar6 (a b : Bool) (p : Chain.C 99970)
    (hp : PreparedMask .eastSouth (((Out.inEmbed 99970 98979 (by decide) (by decide)).trans (nativeLocal .eastSouth a b)).cells p)) : p∈Chain.neighbors 99970 := by
  have hpx:=p.1.isLt
  have hpy:=p.2.isLt
  rcases hp with hp|hp
  all_goals have hx:=congrArg (fun q : Cell=>q.1.val) hp
  all_goals have hy:=congrArg (fun q : Cell=>q.2.val) hp
  all_goals change 0+(100013-((38+(99975-(p.1.val+1)))+1))=_ at hx
  all_goals change 99023+(0+p.2.val)=_ at hy
  all_goals dsimp only [sourceCollar,targetCollar] at hx hy
  all_goals simp only [Chain.neighbors,Finset.mem_insert,Finset.mem_singleton,Prod.ext_iff,Fin.ext_iff]
  all_goals norm_num [width,height] at hx hy ⊢
  all_goals simp only [Fin.ext_iff,Fin.val_zero] at hx hy ⊢
  all_goals omega

private theorem collar7 (a b : Bool) (p : Turn.C)
    (hp : PreparedMask .eastSouth (((Out.turnRect 99970 98979 (by decide) (by decide)).trans (nativeLocal .eastSouth a b)).cells p)) : p∈Turn.template.neighbors := by
  have hpx:=p.1.isLt
  have hpy:=p.2.isLt
  rcases hp with hp|hp
  all_goals have hx:=congrArg (fun q : Cell=>q.1.val) hp
  all_goals have hy:=congrArg (fun q : Cell=>q.2.val) hp
  all_goals change 0+(100013-((0+p.1.val)+1))=_ at hx
  all_goals change 99023+(1+p.2.val)=_ at hy
  all_goals dsimp only [sourceCollar,targetCollar] at hx hy
  all_goals simp only [Turn.template,Turn.neighbors,Finset.mem_insert,Finset.mem_singleton,Prod.ext_iff,Fin.ext_iff]
  all_goals norm_num [width,height] at hx hy ⊢
  all_goals omega

private theorem collar8 (a b : Bool) (p : FlippedChain.C 98979)
    (hp : PreparedMask .eastSouth (((Out.outEmbed 99970 98979 (by decide) (by decide)).trans (nativeLocal .eastSouth a b)).cells p)) : p∈Tail.neighbors 98979 := by
  have hpx:=p.1.isLt
  have hpy:=p.2.isLt
  rcases hp with hp|hp
  all_goals have hx:=congrArg (fun q : Cell=>q.1.val) hp
  all_goals have hy:=congrArg (fun q : Cell=>q.2.val) hp
  all_goals change 0+(100013-((0+(21-(p.2.val+1)))+1))=_ at hx
  all_goals change 99023+(39+p.1.val)=_ at hy
  all_goals dsimp only [sourceCollar,targetCollar] at hx hy
  all_goals simp only [Tail.neighbors,FlippedChain.neighbors,Finset.mem_insert,Finset.mem_singleton,Prod.ext_iff,Fin.ext_iff]
  all_goals norm_num [width,height] at hx hy ⊢
  all_goals simp only [Fin.ext_iff,Fin.val_zero] at hx hy ⊢
  all_goals omega

private theorem collar9 (a b : Bool) (p : FlippedChain.C 98981)
    (hp : PreparedMask .southEast (((In.inEmbed 98981 99969 (by decide) (by decide)).trans (nativeLocal .southEast a b)).cells p)) : p∈Head.neighbors 98981 := by
  have hpx:=p.1.isLt
  have hpy:=p.2.isLt
  rcases hp with hp|hp
  all_goals have hx:=congrArg (fun q : Cell=>q.1.val) hp
  all_goals have hy:=congrArg (fun q : Cell=>q.2.val) hp
  all_goals change 99992+(0+(21-(p.2.val+1)))=_ at hx
  all_goals change 0+(99044-((38+(99006-(p.1.val+1)))+1))=_ at hy
  all_goals dsimp only [sourceCollar,targetCollar] at hx hy
  all_goals simp only [Head.neighbors,FlippedChain.neighbors,Finset.mem_insert,Finset.mem_singleton,Prod.ext_iff,Fin.ext_iff]
  all_goals norm_num [width,height] at hx hy ⊢
  all_goals simp only [Fin.ext_iff,Fin.val_zero] at hx hy ⊢
  all_goals omega

private theorem collar10 (a b : Bool) (p : Turn.C)
    (hp : PreparedMask .southEast (((In.turnRect 98981 99969 (by decide) (by decide)).trans (nativeLocal .southEast a b)).cells p)) : p∈Turn.template.neighbors := by
  have hpx:=p.1.isLt
  have hpy:=p.2.isLt
  rcases hp with hp|hp
  all_goals have hx:=congrArg (fun q : Cell=>q.1.val) hp
  all_goals have hy:=congrArg (fun q : Cell=>q.2.val) hp
  all_goals change 99992+(1+p.2.val)=_ at hx
  all_goals change 0+(99044-((0+p.1.val)+1))=_ at hy
  all_goals dsimp only [sourceCollar,targetCollar] at hx hy
  all_goals simp only [Turn.template,Turn.neighbors,Finset.mem_insert,Finset.mem_singleton,Prod.ext_iff,Fin.ext_iff]
  all_goals norm_num [width,height] at hx hy ⊢
  all_goals omega

private theorem collar11 (a b : Bool) (p : Chain.C 99969)
    (hp : PreparedMask .southEast (((In.outEmbed 98981 99969 (by decide) (by decide)).trans (nativeLocal .southEast a b)).cells p)) : p∈Chain.neighbors 99969 := by
  have hpx:=p.1.isLt
  have hpy:=p.2.isLt
  rcases hp with hp|hp
  all_goals have hx:=congrArg (fun q : Cell=>q.1.val) hp
  all_goals have hy:=congrArg (fun q : Cell=>q.2.val) hp
  all_goals change 99992+(39+p.1.val)=_ at hx
  all_goals change 0+(99044-((0+(21-(p.2.val+1)))+1))=_ at hy
  all_goals dsimp only [sourceCollar,targetCollar] at hx hy
  all_goals simp only [Chain.neighbors,Finset.mem_insert,Finset.mem_singleton,Prod.ext_iff,Fin.ext_iff]
  all_goals norm_num [width,height] at hx hy ⊢
  all_goals simp only [Fin.ext_iff,Fin.val_zero] at hx hy ⊢
  all_goals omega

private theorem collar12 (a b : Bool) (p : Chain.C 99001)
    (hp : PreparedMask .southWest (((Polyline.L.inEmbed 99001 99969 (by decide) (by decide)).trans (nativeLocal .southWest a b)).cells p)) : p∈Chain.neighbors 99001 := by
  have hpx:=p.1.isLt
  have hpy:=p.2.isLt
  rcases hp with hp|hp
  all_goals have hx:=congrArg (fun q : Cell=>q.1.val) hp
  all_goals have hy:=congrArg (fun q : Cell=>q.2.val) hp
  all_goals change 0+(100013-((0+p.2.val)+1))=_ at hx
  all_goals change 0+(99044-((38+(99006-(p.1.val+1)))+1))=_ at hy
  all_goals dsimp only [sourceCollar,targetCollar] at hx hy
  all_goals simp only [Chain.neighbors,Finset.mem_insert,Finset.mem_singleton,Prod.ext_iff,Fin.ext_iff]
  all_goals norm_num [width,height] at hx hy ⊢
  all_goals simp only [Fin.ext_iff,Fin.val_zero] at hx hy ⊢
  all_goals omega

private theorem collar13 (a b : Bool) (p : Turn.C)
    (hp : PreparedMask .southWest (((Polyline.L.turnRect 99001 99969 (by decide) (by decide)).trans (nativeLocal .southWest a b)).cells p)) : p∈Turn.template.neighbors := by
  have hpx:=p.1.isLt
  have hpy:=p.2.isLt
  rcases hp with hp|hp
  all_goals have hx:=congrArg (fun q : Cell=>q.1.val) hp
  all_goals have hy:=congrArg (fun q : Cell=>q.2.val) hp
  all_goals change 0+(100013-((1+p.2.val)+1))=_ at hx
  all_goals change 0+(99044-((0+p.1.val)+1))=_ at hy
  all_goals dsimp only [sourceCollar,targetCollar] at hx hy
  all_goals simp only [Turn.template,Turn.neighbors,Finset.mem_insert,Finset.mem_singleton,Prod.ext_iff,Fin.ext_iff]
  all_goals norm_num [width,height] at hx hy ⊢
  all_goals omega

private theorem collar14 (a b : Bool) (p : Chain.C 99969)
    (hp : PreparedMask .southWest (((Polyline.L.outEmbed 99001 99969 (by decide) (by decide)).trans (nativeLocal .southWest a b)).cells p)) : p∈Chain.neighbors 99969 := by
  have hpx:=p.1.isLt
  have hpy:=p.2.isLt
  rcases hp with hp|hp
  all_goals have hx:=congrArg (fun q : Cell=>q.1.val) hp
  all_goals have hy:=congrArg (fun q : Cell=>q.2.val) hp
  all_goals change 0+(100013-((39+p.1.val)+1))=_ at hx
  all_goals change 0+(99044-((0+(21-(p.2.val+1)))+1))=_ at hy
  all_goals dsimp only [sourceCollar,targetCollar] at hx hy
  all_goals simp only [Chain.neighbors,Finset.mem_insert,Finset.mem_singleton,Prod.ext_iff,Fin.ext_iff]
  all_goals norm_num [width,height] at hx hy ⊢
  all_goals simp only [Fin.ext_iff,Fin.val_zero] at hx hy ⊢
  all_goals omega

variable {W H : ℕ}

attribute [local irreducible] Polyline.Frame.fixed

private theorem mask_preimage {w h : ℕ} (k : Kind) (e : GridEmbedding width height W H)
    (z : GridEmbedding w h W H) (localChart : GridEmbedding w h width height)
    (neighbors : Finset (PushFS.Cell w h)) (outside : Finset (PushFS.Cell W H))
    (hz : ∀p,z.cells p=e.cells (localChart.cells p))
    (hc : ∀p,PreparedMask k (localChart.cells p)→p∈neighbors)
    (hm : ∀p,e.cells p∈outside→PreparedMask k p) :
    Polyline.Frame.fixed z outside⊆neighbors := by
  intro p hp
  have hpoint: z.cells p∈outside:=(Polyline.Frame.mem_fixed _ _ p).mp hp
  rw [hz] at hpoint
  exact hc p (hm (localChart.cells p) hpoint)

/-- The two real prepared outer slots imply every thin-line and protected-corner collar obligation. -/
theorem prepared_of_mask (k : Kind) (a b : Bool) (e : GridEmbedding width height W H)
    (outside : Finset (PushFS.Cell W H))
    (hm : ∀p,e.cells p∈outside→PreparedMask k p) : Prepared k a b e outside := by
  cases k
  · exact mask_preimage _ e _ _ _ outside (fun _=>rfl) (collar0 a b) hm
  · exact mask_preimage _ e _ _ _ outside (fun _=>rfl) (collar1 a b) hm
  · exact mask_preimage _ e _ _ _ outside (fun _=>rfl) (collar2 a b) hm
  · exact ⟨mask_preimage _ e _ _ _ outside (fun _=>rfl) (collar3 a b) hm,
      mask_preimage _ e _ _ _ outside (fun _=>rfl) (collar4 a b) hm,mask_preimage _ e _ _ _ outside (fun _=>rfl) (collar5 a b) hm⟩
  · exact ⟨mask_preimage _ e _ _ _ outside (fun _=>rfl) (collar6 a b) hm,
      mask_preimage _ e _ _ _ outside (fun _=>rfl) (collar7 a b) hm,mask_preimage _ e _ _ _ outside (fun _=>rfl) (collar8 a b) hm⟩
  · exact ⟨mask_preimage _ e _ _ _ outside (fun _=>rfl) (collar9 a b) hm,
      mask_preimage _ e _ _ _ outside (fun _=>rfl) (collar10 a b) hm,mask_preimage _ e _ _ _ outside (fun _=>rfl) (collar11 a b) hm⟩
  · exact ⟨mask_preimage _ e _ _ _ outside (fun _=>rfl) (collar12 a b) hm,
      mask_preimage _ e _ _ _ outside (fun _=>rfl) (collar13 a b) hm,mask_preimage _ e _ _ _ outside (fun _=>rfl) (collar14 a b) hm⟩
end PushPuzzle.PushFS.Gadgets.Wires.Catalog
