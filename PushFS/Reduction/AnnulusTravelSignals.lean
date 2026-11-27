/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.AnnulusLineSignals
public import PushFS.Gadgets.Wires.Catalog.RectThresholds

/-! Actual true-phase physical endpoint cells express all annular line thresholds uniformly by travel direction. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting

open Gadgets.Wires Catalog
set_option maxRecDepth 65536

def lineThresholdCell (f : Bool) (n : ℕ) (hn : 2301≤n) (a b last : Bool) :
    Cell (lineBase f n hn a b).width (lineBase f n hn a b).height :=
  (⟨if last then n+(if f then 21 else 1) else 3,by
    rw [(line_dimensions f n hn a b).1]
    cases last <;> cases f <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega⟩,
    ⟨10,by rw [(line_dimensions f n hn a b).2]; decide⟩)

variable {I : Instance} {L : Type} [Fintype L] {M : SlotMatching I L}

def lineThreshold (f : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool) (d : Direction)
    (g : StorageImage M ((lineMatching f n hn a b).reorient
      ((lineOrientation d f).axis (lineBase f n hn a b).width (lineBase f n hn a b).height).geometry))
    (last : Bool) : Cell I.width I.height :=
  (GridEmbedding.translate g.dx g.dy g.fit_x g.fit_y).cells
    (((lineOrientation d f).axis (lineBase f n hn a b).width (lineBase f n hn a b).height).geometry.cells
      (lineThresholdCell f n hn a b last))

theorem lineHigh_iff_travel (f : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool) (d : Direction)
    (g : StorageImage M ((lineMatching f n hn a b).reorient
      ((lineOrientation d f).axis (lineBase f n hn a b).width (lineBase f n hn a b).height).geometry))
    (last : Bool) (p : Cell I.width I.height) :
    (if last then lineTargetHigh d f n g.dx g.dy p else lineSourceHigh d f n g.dx g.dy p) ↔
      TravelHigh d ((lineThreshold f n hn a b d g last).1.val,(lineThreshold f n hn a b d g last).2.val)
        (p.1.val,p.2.val) := by
  let o:=lineOrientation d f
  have hd:=line_dimensions f n hn a b
  have hp : ((lineBase f n hn a b).width,(lineBase f n hn a b).height)=(n+(if f then 25 else 5),21):=
    Prod.ext hd.1 hd.2
  have hx : g.dx+o.width (n+(if f then 25 else 5)) 21≤I.width := by
    have hw:=congrArg (fun wh : ℕ×ℕ=>g.dx+o.width wh.1 wh.2) hp
    exact hw ▸g.fit_x
  have hy : g.dy+o.height (n+(if f then 25 else 5)) 21≤I.height := by
    have hw:=congrArg (fun wh : ℕ×ℕ=>g.dy+o.height wh.1 wh.2) hp
    exact hw ▸g.fit_y
  have hoff:=congrArg (fun wh : ℕ×ℕ=>(o.undoOffset I.width I.height wh.1 wh.2 g.dx g.dy).1) hp
  have he:=congrArg (fun q : Cell (o.width I.width I.height) (o.height I.width I.height)=>q.1.val)
    (o.undo_cells I.width I.height (lineBase f n hn a b).width (lineBase f n hn a b).height g.dx g.dy
      g.fit_x g.fit_y (lineThresholdCell f n hn a b last))
  change ((o.undo I.width I.height).cells (lineThreshold f n hn a b d g last)).1.val=
    (o.undoOffset I.width I.height (lineBase f n hn a b).width (lineBase f n hn a b).height g.dx g.dy).1+
      (if last then n+(if f then 21 else 1) else 3) at he
  have he' : ((o.undo I.width I.height).cells (lineThreshold f n hn a b d g last)).1.val=
      (o.undoOffset I.width I.height (n+(if f then 25 else 5)) 21 g.dx g.dy).1+
        (if last then n+(if f then 21 else 1) else 3) := he.trans (congrArg (fun z=>z+(if last then n+(if f then 21 else 1) else 3)) hoff)
  have htravel:=(undo_east_iff o (lineThreshold f n hn a b d g last) p).trans
    ((congrArg (fun dir=>TravelHigh dir
      ((lineThreshold f n hn a b d g last).1.val,(lineThreshold f n hn a b d g last).2.val)
      (p.1.val,p.2.val)) (line_direction d f)).to_iff)
  apply Iff.trans ?_ htravel
  cases last
  · simp only [Bool.false_eq_true,ite_false] at he' ⊢
    rw [lineSourceHigh_undo d f n g.dx g.dy hx hy p,he']
  · simp only [ite_true] at he' ⊢
    rw [lineTargetHigh_undo d f n g.dx g.dy hx hy p,he']
    change ((o.undoOffset I.width I.height (n+(if f then 25 else 5)) 21 g.dx g.dy).1+n+(if f then 21 else 1)≤((o.undo I.width I.height).cells p).1.val) ↔
      ((o.undoOffset I.width I.height (n+(if f then 25 else 5)) 21 g.dx g.dy).1+(n+(if f then 21 else 1))≤((o.undo I.width I.height).cells p).1.val)
    rw [Nat.add_assoc]

end PushPuzzle.PushFS.Reduction.GateTileRouting
