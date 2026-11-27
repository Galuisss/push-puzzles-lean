/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.ImageGlyphs

/-! True directional long-train endpoint implications inside arbitrary successful ambient trajectories. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog.StorageImage

open Soundness Polyline

variable {I : Instance} {L : Type} [Fintype L] {M : SlotMatching I L}
    {n : ℕ} {hn : 2301≤n} {a b : Bool} {S T : LabelledState L I.width I.height}

theorem east_chain (g : StorageImage M (Chain.slotMatching n hn a b))
    (h : Successful M S T) (cert : Certificate I) (ho : M.Ordered)
    (hin : g.dx+3≤(S.position (g.labels (ChainEnds.first n hn))).1.val) :
    g.dx+n+1≤(S.position (g.labels (ChainEnds.last n hn))).1.val :=
  g.chainGlyph.signal h cert ho hin

theorem west_chain (g : StorageImage M ((Chain.slotMatching n hn a b).reorient (GridIsometry.reflectX (n+5) 21)))
    (h : Successful M S T) (cert : Certificate I) (ho : M.Ordered)
    (hin : (S.position (g.labels (ChainEnds.first n hn))).1.val≤g.dx+n+1) :
    (S.position (g.labels (ChainEnds.last n hn))).1.val≤g.dx+3 := by
  let e:=GridIsometry.reflectX I.width I.height
  have hs:=orient_successful M h e
  have hc:=reflectXCertificate M cert
  have hord:=ordered_reflectX M ho
  have hfit : g.dx+(n+5)≤I.width := g.fit_x
  have hi : g.unreflectX.chainGlyph.dx+3≤
      ((orientLabels e S).position (g.unreflectX.chainGlyph.labels (ChainEnds.first n hn))).1.val := by
    change I.width-g.dx-(n+5)+3≤I.width-((S.position (g.labels (ChainEnds.first n hn))).1.val+1)
    omega
  have hh:=g.unreflectX.chainGlyph.signal hs hc hord hi
  change I.width-g.dx-(n+5)+n+1≤I.width-((S.position (g.labels (ChainEnds.last n hn))).1.val+1) at hh
  have hb:=(S.position (g.labels (ChainEnds.last n hn))).1.isLt
  omega

theorem south_chain (g : StorageImage M (((Chain.slotMatching n hn a b).reorient
    (GridIsometry.transpose (n+5) 21)).reorient (GridIsometry.reflectX 21 (n+5))))
    (h : Successful M S T) (cert : Certificate I) (ho : M.Ordered)
    (hin : g.dy+3≤(S.position (g.labels (ChainEnds.first n hn))).2.val) :
    g.dy+n+1≤(S.position (g.labels (ChainEnds.last n hn))).2.val := by
  let e:=GridIsometry.reflectX I.width I.height
  let M1:=M.reorient e
  have h1:=orient_successful M h e
  have c1:=reflectXCertificate M cert
  have o1:=ordered_reflectX M ho
  let f:=GridIsometry.transpose I.width I.height
  have h2:=orient_successful M1 h1 f
  have c2:=transposeCertificate M1 c1
  have o2:=ordered_transpose M1 o1
  have hi : g.unreflectX.untranspose.chainGlyph.dx+3≤
      ((orientLabels f (orientLabels e S)).position
        (g.unreflectX.untranspose.chainGlyph.labels (ChainEnds.first n hn))).1.val := hin
  exact g.unreflectX.untranspose.chainGlyph.signal h2 c2 o2 hi

theorem south_flipped (g : StorageImage M (((FlippedChain.slotMatching n hn a b).reorient
    (GridIsometry.transpose (n+25) 21)).reorient (GridIsometry.reflectX 21 (n+25))))
    (h : Successful M S T) (cert : Certificate I) (ho : M.Ordered)
    (hin : g.dy+3≤(S.position (g.labels (FlippedChain.firstLabel n hn))).2.val) :
    g.dy+n+21≤(S.position (g.labels (FlippedChain.lastLabel n))).2.val := by
  let e:=GridIsometry.reflectX I.width I.height
  let M1:=M.reorient e
  have h1:=orient_successful M h e
  have c1:=reflectXCertificate M cert
  have o1:=ordered_reflectX M ho
  let f:=GridIsometry.transpose I.width I.height
  have h2:=orient_successful M1 h1 f
  have c2:=transposeCertificate M1 c1
  have o2:=ordered_transpose M1 o1
  have hi : g.unreflectX.untranspose.flippedGlyph.dx+3≤
      ((orientLabels f (orientLabels e S)).position
        (g.unreflectX.untranspose.flippedGlyph.labels (FlippedChain.firstLabel n hn))).1.val := hin
  exact g.unreflectX.untranspose.flippedGlyph.signal h2 c2 o2 hi

theorem west_flipped (g : StorageImage M (((((FlippedChain.slotMatching n hn a b).reorient
    (GridIsometry.transpose (n+25) 21)).reorient (GridIsometry.reflectX 21 (n+25))).reorient
      (GridIsometry.transpose 21 (n+25))).reorient (GridIsometry.reflectX (n+25) 21)))
    (h : Successful M S T) (cert : Certificate I) (ho : M.Ordered)
    (hin : (S.position (g.labels (FlippedChain.firstLabel n hn))).1.val≤g.dx+n+21) :
    (S.position (g.labels (FlippedChain.lastLabel n))).1.val≤g.dx+3 := by
  let e:=GridIsometry.reflectX I.width I.height
  let M1:=M.reorient e
  have h1:=orient_successful M h e
  have c1:=reflectXCertificate M cert
  have o1:=ordered_reflectX M ho
  let f:=GridIsometry.transpose I.width I.height
  let M2:=M1.reorient f
  have h2:=orient_successful M1 h1 f
  have c2:=transposeCertificate M1 c1
  have o2:=ordered_transpose M1 o1
  let z:=GridIsometry.reflectX I.height I.width
  let M3:=M2.reorient z
  have h3:=orient_successful M2 h2 z
  have c3:=reflectXCertificate M2 c2
  have o3:=ordered_reflectX M2 o2
  let t:=GridIsometry.transpose I.height I.width
  have h4:=orient_successful M3 h3 t
  have c4:=transposeCertificate M3 c3
  have o4:=ordered_transpose M3 o3
  have hfit : g.dx+(n+25)≤I.width := g.fit_x
  have hi : g.unreflectX.untranspose.unreflectX.untranspose.flippedGlyph.dx+3≤
      ((orientLabels t (orientLabels z (orientLabels f (orientLabels e S)))).position
        (g.unreflectX.untranspose.unreflectX.untranspose.flippedGlyph.labels (FlippedChain.firstLabel n hn))).1.val := by
    change I.width-g.dx-(n+25)+3≤I.width-((S.position (g.labels (FlippedChain.firstLabel n hn))).1.val+1)
    omega
  have hh:=g.unreflectX.untranspose.unreflectX.untranspose.flippedGlyph.signal h4 c4 o4 hi
  change I.width-g.dx-(n+25)+n+21≤I.width-((S.position (g.labels (FlippedChain.lastLabel n))).1.val+1) at hh
  have hb:=(S.position (g.labels (FlippedChain.lastLabel n))).1.isLt
  omega

end PushPuzzle.PushFS.Gadgets.Wires.Catalog.StorageImage
