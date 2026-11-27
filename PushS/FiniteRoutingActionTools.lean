/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingActionStock
public import PushS.FiniteRoutingFlipWalking
public import PushS.FiniteRoutingParityWalking

/-! Complete physical flip/parity steps remain strictly inside the trimmed routing action arena. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting.Line.Action
open PushFS
variable {last : Bool}
attribute [local irreducible] width height

private theorem reframe {w u v : ℕ} {atoms : List Atom} {above : Bool}
    {localActive : Finset (Cell u v)} {e : GridEmbedding u v (width w atoms) (height w)}
    {fixed : Finset (Cell (width w atoms) (height w))}
    (F : FiniteWireFrame.Frame localActive e (Line.macroBoard w atoms above) fixed)
    (hu : ∀ p ∈ localActive, UsedPoint w atoms above last (e.cells p))
    (hw : 2 ≤ w) (cut : ℕ) (hfixed : fixed ⊆ cutBoxes w hw cut atoms) :
    FiniteWireFrame.Frame localActive e (macroBoard (last:=last) w atoms above) fixed := by
  refine ⟨?_,F.fixed_avoids,?_⟩
  · intro p hp
    apply (FiniteWireFrame.floor_iff _ _ _).mpr
    exact Finset.mem_filter.mpr ⟨(FiniteWireFrame.floor_iff _ _ _).mp (F.floor p hp),hu p hp⟩
  · exact Finset.disjoint_of_subset_left hfixed (cutBoxes_macro_floor w hw cut atoms above)
namespace Flip

private theorem interior_bounds (w : ℕ) (before after : List Atom) (n m : ℕ)
    (hn : buffer w ≤ n) (hm : buffer w ≤ m) (above : Bool)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w)) (hp : p ∈ FiniteTools.flipActive w) :
    FiniteTools.radius w+1 ≤ ((Tool.Flip.place w before after n m above).cells p).1.val ∧
      ((Tool.Flip.place w before after n m above).cells p).1.val ≤
        FiniteTools.radius w+span w (before++ .line n:: .flip:: .line m::after) := by
  have hb := (Finset.mem_filter.mp hp).2
  unfold buffer at hn hm
  dsimp [Tool.Flip.place,Tool.flipPlace,Tool.embedding]
  simp only [span_append,span_cons,Atom.span]
  unfold FiniteTools.radius at *
  omega

theorem frame (w : ℕ) (hw : 2 ≤ w) (before after : List Atom) (n m : ℕ)
    (hn : buffer w ≤ n) (hm : buffer w ≤ m) (above : Bool) :
    FiniteWireFrame.Frame (FiniteTools.flipActive w) (Tool.Flip.place w before after n m above)
      (macroBoard (last:=last) w (before++ .line n:: .flip:: .line m::after) above)
      (Tool.Flip.fixed w hw before after n m (by unfold buffer at hn; omega) (by unfold buffer at hm; omega)) := by
  refine reframe (Tool.Flip.frame w hw before after n m hn hm above) ?_ hw (Tool.Flip.cut w before n false) ?_
  · intro p hp
    exact Or.inr (Or.inl (interior_bounds w before after n m hn hm above p hp))
  · intro p hp
    obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_image.mpr ⟨l,Finset.mem_univ _,rfl⟩

private theorem ports_low_high (w : ℕ) (hw : 2 ≤ w) (before after : List Atom) (n m : ℕ)
    (hn : buffer w ≤ n) (hm : buffer w ≤ m) (above : Bool) :
    Reachable (macroBoard (last:=last) w (before++ .line n:: .flip:: .line m::after) above) (some 1)
      ⟨(Tool.Flip.place w before after n m above).cells (Tool.Flip.Bridge.fVertical.start w),
        cutBoxes w hw (Tool.Flip.cut w before n false) (before++ .line n:: .flip:: .line m::after)⟩
      ⟨(Tool.Flip.place w before after n m above).cells (Tool.Flip.Bridge.fExit.finish w),
        cutBoxes w hw (Tool.Flip.cut w before n true) (before++ .line n:: .flip:: .line m::after)⟩ := by
  have hn' : 0 < n := by unfold buffer at hn; omega
  have hm' : 1 < m := by unfold buffer at hm; omega
  have hr := (Tool.Flip.bridge_walk w hw .fVertical).trans ((Tool.Flip.bridge_walk w hw .fRow).trans
    ((FiniteTools.flip_forward w hw).trans (Tool.Flip.bridge_walk w hw .fExit)))
  have hh := (frame (last:=last) w hw before after n m hn hm above).replay hr
  change Reachable _ _ ⟨_,_⟩ ⟨_,_⟩ at hh
  dsimp only [Tool.Flip.Bridge.phase] at hh
  rw [←Tool.Flip.inventory w hw before after n m hn' hm' above false,
    ←Tool.Flip.inventory w hw before after n m hn' hm' above true] at hh
  exact hh

private theorem ports_high_low (w : ℕ) (hw : 2 ≤ w) (before after : List Atom) (n m : ℕ)
    (hn : buffer w ≤ n) (hm : buffer w ≤ m) (above : Bool) :
    Reachable (macroBoard (last:=last) w (before++ .line n:: .flip:: .line m::after) above) (some 1)
      ⟨(Tool.Flip.place w before after n m above).cells (Tool.Flip.Bridge.bVertical.start w),
        cutBoxes w hw (Tool.Flip.cut w before n true) (before++ .line n:: .flip:: .line m::after)⟩
      ⟨(Tool.Flip.place w before after n m above).cells (Tool.Flip.Bridge.bExit.finish w),
        cutBoxes w hw (Tool.Flip.cut w before n false) (before++ .line n:: .flip:: .line m::after)⟩ := by
  have hn' : 0 < n := by unfold buffer at hn; omega
  have hm' : 1 < m := by unfold buffer at hm; omega
  have hr := (Tool.Flip.bridge_walk w hw .bVertical).trans ((Tool.Flip.bridge_walk w hw .bRow).trans
    ((FiniteTools.flip_backward w hw).trans (Tool.Flip.bridge_walk w hw .bExit)))
  have hh := (frame (last:=last) w hw before after n m hn hm above).replay hr
  change Reachable _ _ ⟨_,_⟩ ⟨_,_⟩ at hh
  dsimp only [Tool.Flip.Bridge.phase] at hh
  rw [←Tool.Flip.inventory w hw before after n m hn' hm' above true,
    ←Tool.Flip.inventory w hw before after n m hn' hm' above false] at hh
  exact hh

theorem sweep_low_high (w : ℕ) (hw : 2 ≤ w) (before after : List Atom) (n m : ℕ)
    (hn : buffer w ≤ n) (hm : buffer w ≤ m) (above : Bool) :
    Reachable (macroBoard (last:=last) w (before++ .line n:: .flip:: .line m::after) above) (some 1)
      ⟨outerHub w _,cutBoxes w hw (ownedCount w before+n+3) (before++ .line n:: .flip:: .line m::after)⟩
      ⟨outerHub w _,cutBoxes w hw (ownedCount w before+n) (before++ .line n:: .flip:: .line m::after)⟩ := by
  have hflip : ∃ l r, before++ .line n:: .flip:: .line m::after = l++ .flip::r :=
    ⟨before++[.line n],.line m::after,by simp only [List.append_assoc,List.singleton_append]⟩
  have hb := interior_bounds w before after n m hn hm above (Tool.Flip.Bridge.fVertical.start w) (Tool.Flip.bridge_start_active w hw _)
  have hb' := interior_bounds w before after n m hn hm above (Tool.Flip.Bridge.fExit.finish w) (Tool.Flip.bridge_finish_active w hw _)
  have hy : ((Tool.Flip.place w before after n m above).cells (Tool.Flip.Bridge.fVertical.start w)).2.val =
      (laneY w (!(exitSide above before))).val := by
    cases hs : exitSide above before <;>
      simp [Tool.Flip.place,Tool.flipPlace,Tool.embedding,Tool.Flip.Bridge.start,Tool.Flip.Bridge.points,laneY,hs,FiniteTools.radius]; omega
  have hy' : ((Tool.Flip.place w before after n m above).cells (Tool.Flip.Bridge.fExit.finish w)).2.val =
      (laneY w (!(exitSide above before))).val := by
    cases hs : exitSide above before <;>
      simp [Tool.Flip.place,Tool.flipPlace,Tool.embedding,Tool.Flip.Bridge.finish,Tool.Flip.Bridge.points,laneY,hs,FiniteTools.radius]; omega
  have he := outer_reachable (last:=last) w hw (Tool.Flip.cut w before n false) _ above hflip _ _ hb.1 hb.2 hy
  have hx := outer_return (last:=last) w hw (Tool.Flip.cut w before n true) _ above hflip _ _ hb'.1 hb'.2 hy'
  exact he.trans ((ports_low_high w hw before after n m hn hm above).trans hx)

theorem sweep_high_low (w : ℕ) (hw : 2 ≤ w) (before after : List Atom) (n m : ℕ)
    (hn : buffer w ≤ n) (hm : buffer w ≤ m) (above : Bool) :
    Reachable (macroBoard (last:=last) w (before++ .line n:: .flip:: .line m::after) above) (some 1)
      ⟨outerHub w _,cutBoxes w hw (ownedCount w before+n) (before++ .line n:: .flip:: .line m::after)⟩
      ⟨outerHub w _,cutBoxes w hw (ownedCount w before+n+3) (before++ .line n:: .flip:: .line m::after)⟩ := by
  have hflip : ∃ l r, before++ .line n:: .flip:: .line m::after = l++ .flip::r :=
    ⟨before++[.line n],.line m::after,by simp only [List.append_assoc,List.singleton_append]⟩
  have hb := interior_bounds w before after n m hn hm above (Tool.Flip.Bridge.bVertical.start w) (Tool.Flip.bridge_start_active w hw _)
  have hb' := interior_bounds w before after n m hn hm above (Tool.Flip.Bridge.bExit.finish w) (Tool.Flip.bridge_finish_active w hw _)
  have hy : ((Tool.Flip.place w before after n m above).cells (Tool.Flip.Bridge.bVertical.start w)).2.val =
      (laneY w (!(exitSide above before))).val := by
    cases hs : exitSide above before <;>
      simp [Tool.Flip.place,Tool.flipPlace,Tool.embedding,Tool.Flip.Bridge.start,Tool.Flip.Bridge.points,laneY,hs,FiniteTools.radius]; omega
  have hy' : ((Tool.Flip.place w before after n m above).cells (Tool.Flip.Bridge.bExit.finish w)).2.val =
      (laneY w (exitSide above before)).val := by
    cases hs : exitSide above before <;>
      simp [Tool.Flip.place,Tool.flipPlace,Tool.embedding,Tool.Flip.Bridge.finish,Tool.Flip.Bridge.points,laneY,hs,FiniteTools.radius]; omega
  have he := outer_reachable (last:=last) w hw (Tool.Flip.cut w before n true) _ above hflip _ _ hb.1 hb.2 hy
  have hx := outer_return (last:=last) w hw (Tool.Flip.cut w before n false) _ above hflip _ _ hb'.1 hb'.2 hy'
  exact he.trans ((ports_high_low w hw before after n m hn hm above).trans hx)

end Flip

namespace Parity

private theorem interior_bounds (w : ℕ) (before after : List Atom) (n m : ℕ)
    (hn : buffer w ≤ n) (hm : buffer w ≤ m) (above : Bool)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w)) (hp : p ∈ FiniteTools.parityActive w) :
    FiniteTools.radius w+1 ≤ ((Tool.Parity.place w before after n m above).cells p).1.val ∧
      ((Tool.Parity.place w before after n m above).cells p).1.val ≤
        FiniteTools.radius w+span w (before++ .line n:: .parity:: .line m::after) := by
  have hb := (Finset.mem_filter.mp hp).2
  unfold buffer at hn hm
  dsimp [Tool.Parity.place,Tool.parityPlace,Tool.embedding]
  simp only [span_append,span_cons,Atom.span]
  unfold FiniteTools.radius at *
  omega

private theorem frame (w : ℕ) (hw : 2 ≤ w) (before after : List Atom) (n m : ℕ)
    (hn : buffer w ≤ n) (hm : buffer w ≤ m) (above : Bool) :
    FiniteWireFrame.Frame (FiniteTools.parityActive w) (Tool.Parity.place w before after n m above)
      (macroBoard (last:=last) w (before++ .line n:: .parity:: .line m::after) above)
      (Tool.Parity.fixed w hw before after n m (by unfold buffer at hn; omega) (by unfold buffer at hm; omega)) := by
  refine reframe (Tool.Parity.frame w hw before after n m hn hm above) ?_ hw (Tool.Parity.cut w before n false) ?_
  · intro p hp
    exact Or.inr (Or.inl (interior_bounds w before after n m hn hm above p hp))
  · intro p hp
    obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_image.mpr ⟨l,Finset.mem_univ _,rfl⟩

private theorem ports_low_high (w : ℕ) (hw : 2 ≤ w) (before after : List Atom) (n m : ℕ)
    (hn : buffer w ≤ n) (hm : buffer w ≤ m) (above : Bool) :
    Reachable (macroBoard (last:=last) w (before++ .line n:: .parity:: .line m::after) above) (some 1)
      ⟨(Tool.Parity.place w before after n m above).cells (Tool.Parity.Bridge.fVertical.start w),
        cutBoxes w hw (Tool.Parity.cut w before n false) (before++ .line n:: .parity:: .line m::after)⟩
      ⟨(Tool.Parity.place w before after n m above).cells (Tool.Parity.Bridge.fExit.finish w),
        cutBoxes w hw (Tool.Parity.cut w before n true) (before++ .line n:: .parity:: .line m::after)⟩ := by
  have hn' : 0 < n := by unfold buffer at hn; omega
  have hm' : 1 < m := by unfold buffer at hm; omega
  have hr := (Tool.Parity.bridge_walk w hw .fVertical).trans ((Tool.Parity.bridge_walk w hw .fRow).trans
    ((FiniteTools.parity_forward_active w).trans (Tool.Parity.bridge_walk w hw .fExit)))
  have hh := (frame (last:=last) w hw before after n m hn hm above).replay hr
  change Reachable _ _ ⟨_,_⟩ ⟨_,_⟩ at hh
  dsimp only [Tool.Parity.Bridge.phase] at hh
  rw [←Tool.Parity.inventory w hw before after n m hn' hm' above false,
    ←Tool.Parity.inventory w hw before after n m hn' hm' above true] at hh
  exact hh

private theorem ports_high_low (w : ℕ) (hw : 2 ≤ w) (before after : List Atom) (n m : ℕ)
    (hn : buffer w ≤ n) (hm : buffer w ≤ m) (above : Bool) :
    Reachable (macroBoard (last:=last) w (before++ .line n:: .parity:: .line m::after) above) (some 1)
      ⟨(Tool.Parity.place w before after n m above).cells (Tool.Parity.Bridge.bVertical.start w),
        cutBoxes w hw (Tool.Parity.cut w before n true) (before++ .line n:: .parity:: .line m::after)⟩
      ⟨(Tool.Parity.place w before after n m above).cells (Tool.Parity.Bridge.bExit.finish w),
        cutBoxes w hw (Tool.Parity.cut w before n false) (before++ .line n:: .parity:: .line m::after)⟩ := by
  have hn' : 0 < n := by unfold buffer at hn; omega
  have hm' : 1 < m := by unfold buffer at hm; omega
  have hr := (Tool.Parity.bridge_walk w hw .bVertical).trans ((Tool.Parity.bridge_walk w hw .bRow).trans
    ((FiniteTools.parity_backward_active w).trans (Tool.Parity.bridge_walk w hw .bExit)))
  have hh := (frame (last:=last) w hw before after n m hn hm above).replay hr
  change Reachable _ _ ⟨_,_⟩ ⟨_,_⟩ at hh
  dsimp only [Tool.Parity.Bridge.phase] at hh
  rw [←Tool.Parity.inventory w hw before after n m hn' hm' above true,
    ←Tool.Parity.inventory w hw before after n m hn' hm' above false] at hh
  exact hh

theorem sweep_low_high (w : ℕ) (hw : 2 ≤ w) (before after : List Atom) (n m : ℕ)
    (hn : buffer w ≤ n) (hm : buffer w ≤ m) (above : Bool)
    (hflip : ∃ l r, before++ .line n:: .parity:: .line m::after = l++ .flip::r) :
    Reachable (macroBoard (last:=last) w (before++ .line n:: .parity:: .line m::after) above) (some 1)
      ⟨outerHub w _,cutBoxes w hw (ownedCount w before+n+2) (before++ .line n:: .parity:: .line m::after)⟩
      ⟨outerHub w _,cutBoxes w hw (ownedCount w before+n) (before++ .line n:: .parity:: .line m::after)⟩ := by
  have hb := interior_bounds w before after n m hn hm above (Tool.Parity.Bridge.fVertical.start w) (Tool.Parity.bridge_start_active w hw _)
  have hb' := interior_bounds w before after n m hn hm above (Tool.Parity.Bridge.fExit.finish w) (Tool.Parity.bridge_finish_active w hw _)
  have hy : ((Tool.Parity.place w before after n m above).cells (Tool.Parity.Bridge.fVertical.start w)).2.val =
      (laneY w (!(exitSide above before))).val := by
    cases hs : exitSide above before <;>
      simp [Tool.Parity.place,Tool.parityPlace,Tool.embedding,Tool.Parity.Bridge.start,Tool.Parity.Bridge.points,laneY,hs,FiniteTools.radius]; omega
  have hy' : ((Tool.Parity.place w before after n m above).cells (Tool.Parity.Bridge.fExit.finish w)).2.val =
      (laneY w (!(exitSide above before))).val := by
    cases hs : exitSide above before <;>
      simp [Tool.Parity.place,Tool.parityPlace,Tool.embedding,Tool.Parity.Bridge.finish,Tool.Parity.Bridge.points,laneY,hs,FiniteTools.radius]; omega
  have he := outer_reachable (last:=last) w hw (Tool.Parity.cut w before n false) _ above hflip _ _ hb.1 hb.2 hy
  have hx := outer_return (last:=last) w hw (Tool.Parity.cut w before n true) _ above hflip _ _ hb'.1 hb'.2 hy'
  exact he.trans ((ports_low_high w hw before after n m hn hm above).trans hx)

theorem sweep_high_low (w : ℕ) (hw : 2 ≤ w) (before after : List Atom) (n m : ℕ)
    (hn : buffer w ≤ n) (hm : buffer w ≤ m) (above : Bool)
    (hflip : ∃ l r, before++ .line n:: .parity:: .line m::after = l++ .flip::r) :
    Reachable (macroBoard (last:=last) w (before++ .line n:: .parity:: .line m::after) above) (some 1)
      ⟨outerHub w _,cutBoxes w hw (ownedCount w before+n) (before++ .line n:: .parity:: .line m::after)⟩
      ⟨outerHub w _,cutBoxes w hw (ownedCount w before+n+2) (before++ .line n:: .parity:: .line m::after)⟩ := by
  have hb := interior_bounds w before after n m hn hm above (Tool.Parity.Bridge.bVertical.start w) (Tool.Parity.bridge_start_active w hw _)
  have hb' := interior_bounds w before after n m hn hm above (Tool.Parity.Bridge.bExit.finish w) (Tool.Parity.bridge_finish_active w hw _)
  have hy : ((Tool.Parity.place w before after n m above).cells (Tool.Parity.Bridge.bVertical.start w)).2.val =
      (laneY w (!(exitSide above before))).val := by
    cases hs : exitSide above before <;>
      simp [Tool.Parity.place,Tool.parityPlace,Tool.embedding,Tool.Parity.Bridge.start,Tool.Parity.Bridge.points,laneY,hs,FiniteTools.radius]; omega
  have hy' : ((Tool.Parity.place w before after n m above).cells (Tool.Parity.Bridge.bExit.finish w)).2.val =
      (laneY w (!(exitSide above before))).val := by
    cases hs : exitSide above before <;>
      simp [Tool.Parity.place,Tool.parityPlace,Tool.embedding,Tool.Parity.Bridge.finish,Tool.Parity.Bridge.points,laneY,hs,FiniteTools.radius]; omega
  have he := outer_reachable (last:=last) w hw (Tool.Parity.cut w before n true) _ above hflip _ _ hb.1 hb.2 hy
  have hx := outer_return (last:=last) w hw (Tool.Parity.cut w before n false) _ above hflip _ _ hb'.1 hb'.2 hy'
  exact he.trans ((ports_high_low w hw before after n m hn hm above).trans hx)

end Parity

end PushPuzzle.PushS.FiniteRouting.Line.Action
