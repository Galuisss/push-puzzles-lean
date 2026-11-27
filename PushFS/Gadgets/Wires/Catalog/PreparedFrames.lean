/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module
public import PushFS.Gadgets.Wires.Catalog.AmbientMacros
public import PushFS.Gadgets.Wires.Catalog.PlacedSemantics

/-! Actual thin native walls are automatic; prepared macros constrain only literal foreign collars. -/
@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog

open Reduction
set_option maxRecDepth 65536
set_option maxHeartbeats 200000
variable {W H : ℕ}

private theorem walls_trans {w h u v : ℕ} (e : GridEmbedding w h u v) (f : GridEmbedding u v W H)
    {A : Board w h} {B : Board u v} {C : Board W H} (he : e.WallsAgree A B) (hf : f.WallsAgree B C) :
    (e.trans f).WallsAgree A C:=fun p=>(hf (e.cells p)).trans (he p)

private theorem native_walls (k : Kind) (a b : Bool) (e : GridEmbedding width height W H)
    {B : Board W H} (hw : e.WallsAgree (puzzle k a b).board B) :
    (nativeEmbedding k a b e).WallsAgree (native k a b).board B := by
  have hi : (nativeIsometry k a b).embedding.WallsAgree (native k a b).board (base k a b).board := by
    intro p
    rw [←native_board k a b]
    exact (nativeIsometry k a b).mem_walls _ p
  exact walls_trans _ e (walls_trans _ _ hi (placed_walls (baseMatching k a b) (dx k) (dy k) (fitsX k a b) (fitsY k a b))) hw

private theorem l_in_walls (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (a b : Bool)
    (e : GridEmbedding (m+43) (n+44) W H) {B : Board W H}
    (hw : e.WallsAgree (Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).board B) :
    ((Polyline.L.inEmbed m n hm hn).trans e).WallsAgree (Chain.board m hm ∅) B := by
  intro p
  exact (hw ((Polyline.L.inEmbed m n hm hn).cells p)).trans
    (((Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).walls_agree 0 ((Polyline.L.inIso m).cells p)).trans
      (Polyline.L.in_walls m n hm hn _ _ p))

private theorem l_out_walls (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (a b : Bool)
    (e : GridEmbedding (m+43) (n+44) W H) {B : Board W H}
    (hw : e.WallsAgree (Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).board B) :
    ((Polyline.L.outEmbed m n hm hn).trans e).WallsAgree (Chain.board n hn ∅) B := by
  intro p
  exact (hw ((Polyline.L.outEmbed m n hm hn).cells p)).trans
    (((Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).walls_agree 2 ((Polyline.L.outIso n).cells p)).trans
      (Polyline.L.out_walls m n hm hn _ _ p))

private theorem l_turn_walls (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (a b : Bool)
    (e : GridEmbedding (m+43) (n+44) W H) {B : Board W H}
    (hw : e.WallsAgree (Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).board B) :
    ((Polyline.L.turnRect m n hm hn).trans e).WallsAgree (Turn.template.board ∅) B := by
  intro p
  exact (hw ((Polyline.L.turnRect m n hm hn).cells p)).trans
    ((Polyline.L.atlas m n hm hn (Polyline.L.uniform a) (Polyline.L.uniform b)).walls_agree 1 p)

private theorem out_in_walls (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (a b : Bool)
    (e : GridEmbedding (m+43) (n+64) W H) {B : Board W H}
    (hw : e.WallsAgree (Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).board B) :
    ((Out.inEmbed m n hm hn).trans e).WallsAgree (Chain.board m hm ∅) B := by
  intro p
  exact (hw ((Out.inEmbed m n hm hn).cells p)).trans
    (((Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).walls_agree 0 ((Out.inIso m).cells p)).trans (Out.in_walls m n hm hn _ _ p))
private theorem out_out_walls (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (a b : Bool)
    (e : GridEmbedding (m+43) (n+64) W H) {B : Board W H}
    (hw : e.WallsAgree (Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).board B) :
    ((Out.outEmbed m n hm hn).trans e).WallsAgree (Tail.board n hn ∅) B := by
  intro p
  exact (hw ((Out.outEmbed m n hm hn).cells p)).trans
    (((Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).walls_agree 2 ((Out.outIso n).cells p)).trans (Out.out_walls m n hm hn _ _ p))
private theorem out_turn_walls (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (a b : Bool)
    (e : GridEmbedding (m+43) (n+64) W H) {B : Board W H}
    (hw : e.WallsAgree (Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).board B) :
    ((Out.turnRect m n hm hn).trans e).WallsAgree (Turn.template.board ∅) B := by
  intro p
  exact (hw ((Out.turnRect m n hm hn).cells p)).trans ((Out.atlas m n hm hn (Out.uniform a) (Out.uniform b)).walls_agree 1 p)

private theorem in_in_walls (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (a b : Bool)
    (e : GridEmbedding (m+63) (n+44) W H) {B : Board W H}
    (hw : e.WallsAgree (In.atlas m n hm hn (In.uniform a) (In.uniform b)).board B) :
    ((In.inEmbed m n hm hn).trans e).WallsAgree (Head.board m hm ∅) B := by
  intro p
  exact (hw ((In.inEmbed m n hm hn).cells p)).trans
    (((In.atlas m n hm hn (In.uniform a) (In.uniform b)).walls_agree 0 ((In.inIso m).cells p)).trans (In.in_walls m n hm hn _ _ p))
private theorem in_out_walls (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (a b : Bool)
    (e : GridEmbedding (m+63) (n+44) W H) {B : Board W H}
    (hw : e.WallsAgree (In.atlas m n hm hn (In.uniform a) (In.uniform b)).board B) :
    ((In.outEmbed m n hm hn).trans e).WallsAgree (Chain.board n hn ∅) B := by
  intro p
  exact (hw ((In.outEmbed m n hm hn).cells p)).trans
    (((In.atlas m n hm hn (In.uniform a) (In.uniform b)).walls_agree 2 ((In.outIso n).cells p)).trans (In.out_walls m n hm hn _ _ p))
private theorem in_turn_walls (m n : ℕ) (hm : 2301≤m) (hn : 2301≤n) (a b : Bool)
    (e : GridEmbedding (m+63) (n+44) W H) {B : Board W H}
    (hw : e.WallsAgree (In.atlas m n hm hn (In.uniform a) (In.uniform b)).board B) :
    ((In.turnRect m n hm hn).trans e).WallsAgree (Turn.template.board ∅) B := by
  intro p
  exact (hw ((In.turnRect m n hm hn).cells p)).trans ((In.atlas m n hm hn (In.uniform a) (In.uniform b)).walls_agree 1 p)

/-- Only the actual finite primitive collars need preparation; walls and floor follow from the real ambient board. -/
def Prepared (k : Kind) (a b : Bool) (e : GridEmbedding width height W H) (outside : Finset (PushFS.Cell W H)) : Prop :=
  match k with
  | .east=>Polyline.Frame.fixed (nativeEmbedding .east a b e) outside⊆Chain.neighbors 200000
  | .west=>Polyline.Frame.fixed (nativeEmbedding .west a b e) outside⊆Chain.neighbors 200000
  | .south=>Polyline.Frame.fixed (nativeEmbedding .south a b e) outside⊆Chain.neighbors 198061
  | .westSouth=>
    (Polyline.Frame.fixed ((Polyline.L.inEmbed 99970 98999 (by decide) (by decide)).trans (nativeEmbedding .westSouth a b e)) outside⊆Chain.neighbors 99970) ∧
    (Polyline.Frame.fixed ((Polyline.L.turnRect 99970 98999 (by decide) (by decide)).trans (nativeEmbedding .westSouth a b e)) outside⊆Turn.template.neighbors) ∧
    (Polyline.Frame.fixed ((Polyline.L.outEmbed 99970 98999 (by decide) (by decide)).trans (nativeEmbedding .westSouth a b e)) outside⊆Chain.neighbors 98999)
  | .eastSouth=>
    (Polyline.Frame.fixed ((Out.inEmbed 99970 98979 (by decide) (by decide)).trans (nativeEmbedding .eastSouth a b e)) outside⊆Chain.neighbors 99970) ∧
    (Polyline.Frame.fixed ((Out.turnRect 99970 98979 (by decide) (by decide)).trans (nativeEmbedding .eastSouth a b e)) outside⊆Turn.template.neighbors) ∧
    (Polyline.Frame.fixed ((Out.outEmbed 99970 98979 (by decide) (by decide)).trans (nativeEmbedding .eastSouth a b e)) outside⊆Tail.neighbors 98979)
  | .southEast=>
    (Polyline.Frame.fixed ((In.inEmbed 98981 99969 (by decide) (by decide)).trans (nativeEmbedding .southEast a b e)) outside⊆Head.neighbors 98981) ∧
    (Polyline.Frame.fixed ((In.turnRect 98981 99969 (by decide) (by decide)).trans (nativeEmbedding .southEast a b e)) outside⊆Turn.template.neighbors) ∧
    (Polyline.Frame.fixed ((In.outEmbed 98981 99969 (by decide) (by decide)).trans (nativeEmbedding .southEast a b e)) outside⊆Chain.neighbors 99969)
  | .southWest=>
    (Polyline.Frame.fixed ((Polyline.L.inEmbed 99001 99969 (by decide) (by decide)).trans (nativeEmbedding .southWest a b e)) outside⊆Chain.neighbors 99001) ∧
    (Polyline.Frame.fixed ((Polyline.L.turnRect 99001 99969 (by decide) (by decide)).trans (nativeEmbedding .southWest a b e)) outside⊆Turn.template.neighbors) ∧
    (Polyline.Frame.fixed ((Polyline.L.outEmbed 99001 99969 (by decide) (by decide)).trans (nativeEmbedding .southWest a b e)) outside⊆Chain.neighbors 99969)


theorem ambientFrame_of_prepared (k : Kind) (a b : Bool) (e : GridEmbedding width height W H)
    {B : Board W H} {outside : Finset (PushFS.Cell W H)}
    (hw : e.WallsAgree (puzzle k a b).board B) (hf : Disjoint outside B.walls)
    (hp : Prepared k a b e outside) : AmbientFrame k a b e B outside := by
  have hn:=native_walls k a b e hw
  cases k
  · refine ⟨?_,hf,hp⟩
    intro p
    exact hn p
  · refine ⟨?_,hf,hp⟩
    intro p
    exact hn p
  · refine ⟨?_,hf,hp⟩
    intro p
    exact hn p
  · exact ⟨l_in_walls _ _ _ _ a b _ hn,l_turn_walls _ _ _ _ a b _ hn,l_out_walls _ _ _ _ a b _ hn,hf,hp.1,hp.2.1,hp.2.2⟩
  · exact ⟨out_in_walls _ _ _ _ a b _ hn,out_turn_walls _ _ _ _ a b _ hn,out_out_walls _ _ _ _ a b _ hn,hf,hp.1,hp.2.1,hp.2.2⟩
  · exact ⟨in_in_walls _ _ _ _ a b _ hn,in_turn_walls _ _ _ _ a b _ hn,in_out_walls _ _ _ _ a b _ hn,hf,hp.1,hp.2.1,hp.2.2⟩
  · exact ⟨l_in_walls _ _ _ _ a b _ hn,l_turn_walls _ _ _ _ a b _ hn,l_out_walls _ _ _ _ a b _ hn,hf,hp.1,hp.2.1,hp.2.2⟩
end PushPuzzle.PushFS.Gadgets.Wires.Catalog
