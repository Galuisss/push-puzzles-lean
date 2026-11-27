/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateBoundary.Geometry
public import PushFS.RectPlacement

/-! Actual terminal long-chain wall guards and complete exterior coverage. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateBoundary

open Gadgets Gadgets.Wires
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

theorem normal_far_wall (d : Direction) (incoming : Bool) (n : ℕ) (hn : 2301≤n)
    (dx dy : ℕ) (hd : EndPlacement d incoming n dx dy) (q : Chain.C n) (p : ℕ×ℕ)
    (he : (lineOrientation d false).coordinates (n+5) 21 dx dy q=p) (hf : InFrame d p) :
    q∈Chain.walls n hn ↔Guard d p := by
  rw [RectOrientation.coordinates_point] at he
  have hx:=congrArg Prod.fst he
  have hy:=congrArg Prod.snd he
  have hqx:=q.1.isLt
  have hqy:=q.2.isLt
  have hb : incoming.toNat≤1 := by cases incoming <;> decide
  cases d
  all_goals
    simp only [EndPlacement,InFrame,Guard,lineOrientation,RectOrientation.point,
      RectOrientation.width,RectOrientation.height,Bool.not_false,Bool.false_eq_true,reduceIte] at hd hf hx hy ⊢
    rw [Polyline.chain_right7 n hn q (by omega)]
    omega

def CapPoint : Direction→(ℕ×ℕ)→Prop
  | .west,p => p.1=0
  | .east,p => p.1=200006
  | .north,p => p.2=0
  | .south,p => p.2=198067

instance (d : Direction) (p : ℕ×ℕ) : Decidable (CapPoint d p) := by cases d <;> unfold CapPoint <;> infer_instance

/-- Every frame guard cell lies in its real last chain except for the one output-cap layer. -/
theorem normal_contains (d : Direction) (incoming : Bool) (n : ℕ) (hn : 2301≤n)
    (dx dy : ℕ) (hd : EndPlacement d incoming n dx dy) (p : ℕ×ℕ)
    (hpx : p.1<200007) (hpy : p.2<198068) (hf : InFrame d p) (hg : Guard d p)
    (hc : incoming=true ∨¬CapPoint d p) :
    dx≤p.1 ∧p.1<dx+(lineOrientation d false).width (n+5) 21 ∧
      dy≤p.2 ∧p.2<dy+(lineOrientation d false).height (n+5) 21 := by
  cases d <;> cases incoming <;>
    simp only [EndPlacement,InFrame,Guard,CapPoint,lineOrientation,RectOrientation.width,
      RectOrientation.height,Bool.toNat,Bool.cond_false,Bool.cond_true,reduceIte,Bool.false_eq_true,false_or,true_or] at * <;> omega

end PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateBoundary
