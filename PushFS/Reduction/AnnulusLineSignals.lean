/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.AnnulusLineEndpoints
public import PushFS.Gadgets.Wires.Catalog.RectImages
public import PushFS.Gadgets.Wires.Catalog.ImageGlyphs

/-! The true near-to-far threshold of every physical annular long line in all four travel directions. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting

open Gadgets.Wires Catalog Soundness Polyline
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def lineSourceHigh {W H : ℕ} (d : Direction) (f : Bool) (n dx dy : ℕ) (p : Cell W H) : Prop :=
  match d with
  | .east=>dx+3≤p.1.val
  | .west=>p.1.val≤dx+n+(if f then 21 else 1)
  | .south=>dy+3≤p.2.val
  | .north=>p.2.val≤dy+n+(if f then 21 else 1)

def lineTargetHigh {W H : ℕ} (d : Direction) (f : Bool) (n dx dy : ℕ) (p : Cell W H) : Prop :=
  match d with
  | .east=>dx+n+(if f then 21 else 1)≤p.1.val
  | .west=>p.1.val≤dx+3
  | .south=>dy+n+(if f then 21 else 1)≤p.2.val
  | .north=>p.2.val≤dy+3

theorem lineSourceHigh_undo {W H : ℕ} (d : Direction) (f : Bool) (n dx dy : ℕ)
    (hx : dx+(lineOrientation d f).width (n+(if f then 25 else 5)) 21≤W)
    (hy : dy+(lineOrientation d f).height (n+(if f then 25 else 5)) 21≤H) (p : Cell W H) :
    lineSourceHigh d f n dx dy p ↔
      ((lineOrientation d f).undoOffset W H (n+(if f then 25 else 5)) 21 dx dy).1+3≤
        (((lineOrientation d f).undo W H).cells p).1.val := by
  have he:=(congrArg Prod.fst ((lineOrientation d f).inverse.point_cells W H p)).symm
  rw [show (((lineOrientation d f).undo W H).cells p).1.val=
    ((lineOrientation d f).inverse.point W H (p.1.val,p.2.val)).1 from he]
  have hpx:=p.1.isLt
  have hpy:=p.2.isLt
  cases d <;> cases f <;>
    simp only [lineSourceHigh,lineOrientation,RectOrientation.inverse,RectOrientation.point,
      RectOrientation.width,RectOrientation.height,RectOrientation.undoOffset,
      Bool.false_eq_true,ite_true,ite_false,Bool.not_true,Bool.not_false] at hx hy ⊢
  all_goals omega

theorem lineTargetHigh_undo {W H : ℕ} (d : Direction) (f : Bool) (n dx dy : ℕ)
    (hx : dx+(lineOrientation d f).width (n+(if f then 25 else 5)) 21≤W)
    (hy : dy+(lineOrientation d f).height (n+(if f then 25 else 5)) 21≤H) (p : Cell W H) :
    lineTargetHigh d f n dx dy p ↔
      ((lineOrientation d f).undoOffset W H (n+(if f then 25 else 5)) 21 dx dy).1+n+(if f then 21 else 1)≤
        (((lineOrientation d f).undo W H).cells p).1.val := by
  have he:=(congrArg Prod.fst ((lineOrientation d f).inverse.point_cells W H p)).symm
  rw [show (((lineOrientation d f).undo W H).cells p).1.val=
    ((lineOrientation d f).inverse.point W H (p.1.val,p.2.val)).1 from he]
  have hpx:=p.1.isLt
  have hpy:=p.2.isLt
  cases d <;> cases f <;>
    simp only [lineTargetHigh,lineOrientation,RectOrientation.inverse,RectOrientation.point,
      RectOrientation.width,RectOrientation.height,RectOrientation.undoOffset,
      Bool.false_eq_true,ite_true,ite_false,Bool.not_true,Bool.not_false] at hx hy ⊢
  all_goals omega

variable {I : Instance} {L : Type} [Fintype L] {M : SlotMatching I L}

/-- Every actual intermediate state of a successful ambient trajectory transmits the line's physical signal. -/
theorem line_signal (f : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool) (d : Direction)
    (g : StorageImage M ((lineMatching f n hn a b).reorient
      ((lineOrientation d f).axis (lineBase f n hn a b).width (lineBase f n hn a b).height).geometry))
    {S T : LabelledState L I.width I.height} (hs : Successful M S T) (cert : Certificate I) (ordered : M.Ordered)
    (hin : lineSourceHigh d f n g.dx g.dy (S.position (g.labels (lineFirst f n hn)))) :
    lineTargetHigh d f n g.dx g.dy (S.position (g.labels (lineLast f n hn))) := by
  let o:=lineOrientation d f
  let e:=o.undo I.width I.height
  let h:=g.straighten o
  have hp:=orient_successful M hs e
  have hc:=rectCertificate M cert o.inverse
  have ho:=rectOrdered M ordered o.inverse
  have hd:=line_dimensions f n hn a b
  have hdPair : ((lineBase f n hn a b).width,(lineBase f n hn a b).height)=(n+(if f then 25 else 5),21):=Prod.ext hd.1 hd.2
  have hx0 : g.dx+o.width (lineBase f n hn a b).width (lineBase f n hn a b).height≤I.width:=g.fit_x
  have hy0 : g.dy+o.height (lineBase f n hn a b).width (lineBase f n hn a b).height≤I.height:=g.fit_y
  have hdx:=congrArg (fun wh : ℕ×ℕ=>o.width wh.1 wh.2) hdPair
  have hdy:=congrArg (fun wh : ℕ×ℕ=>o.height wh.1 wh.2) hdPair
  have hx : g.dx+o.width (n+(if f then 25 else 5)) 21≤I.width:=by
    calc
      _ = g.dx+o.width (lineBase f n hn a b).width (lineBase f n hn a b).height:=congrArg (g.dx+·) hdx.symm
      _ ≤ I.width:=hx0
  have hy : g.dy+o.height (n+(if f then 25 else 5)) 21≤I.height:=by
    calc
      _ = g.dy+o.height (lineBase f n hn a b).width (lineBase f n hn a b).height:=congrArg (g.dy+·) hdy.symm
      _ ≤ I.height:=hy0
  have hoff : h.dx=(o.undoOffset I.width I.height (n+(if f then 25 else 5)) 21 g.dx g.dy).1 :=
    congrArg (fun wh : ℕ×ℕ=>(o.undoOffset I.width I.height wh.1 wh.2 g.dx g.dy).1) hdPair
  have hi:=((lineSourceHigh_undo d f n g.dx g.dy hx hy _).mp hin)
  have hf:=lineTargetHigh_undo d f n g.dx g.dy hx hy (S.position (g.labels (lineLast f n hn)))
  apply hf.mpr
  have hi' : h.dx+3≤((orientLabels e S).position (h.labels (lineFirst f n hn))).1.val := by
    change h.dx+3≤(e.cells (S.position (g.labels (lineFirst f n hn)))).1.val
    change _≤(e.cells (S.position (g.labels (lineFirst f n hn)))).1.val at hi
    exact (congrArg (fun z=>z+3) hoff).trans_le hi
  have hout : h.dx+n+(if f then 21 else 1)≤((orientLabels e S).position (h.labels (lineLast f n hn))).1.val := by
    cases f
    · exact h.chainGlyph.signal hp hc ho hi'
    · exact h.flippedGlyph.signal hp hc ho hi'
  change _≤(e.cells (S.position (g.labels (lineLast f n hn)))).1.val
  change h.dx+n+(if f then 21 else 1)≤(e.cells (S.position (g.labels (lineLast f n hn)))).1.val at hout
  exact (congrArg (fun z=>z+n+(if f then 21 else 1)) hoff.symm).trans_le hout

end PushPuzzle.PushFS.Reduction.GateTileRouting
