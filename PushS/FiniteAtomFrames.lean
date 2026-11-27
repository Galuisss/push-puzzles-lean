/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteFrameComposition

/-! Minimal physical footprints for ambient walking and single-box pushing. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteAtomFrames

open PushFS

variable {w h W H : ℕ}

/-- A rectangular walking corridor between two fixed endpoints. -/
def walkActive (p q : Cell w h) : Finset (Cell w h) :=
  Finset.univ.filter fun r =>
    min p.1.val q.1.val ≤ r.1.val ∧ r.1.val ≤ max p.1.val q.1.val ∧
      min p.2.val q.2.val ≤ r.2.val ∧ r.2.val ≤ max p.2.val q.2.val

@[simp] theorem mem_walkActive (p q r : Cell w h) : r ∈ walkActive p q ↔
    min p.1.val q.1.val ≤ r.1.val ∧ r.1.val ≤ max p.1.val q.1.val ∧
      min p.2.val q.2.val ≤ r.2.val ∧ r.2.val ≤ max p.2.val q.2.val := by
  simp only [walkActive, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Replay the complete corridor walk while all actual ambient boxes remain fixed. -/
theorem walk_ambient (p q : Cell w h) (e : GridEmbedding w h W H) {B : Board W H}
    {fixed : Finset (Cell W H)} (F : FiniteWireFrame.Frame (walkActive p q) e B fixed) :
    Reachable B (some 1) ⟨e.cells p, fixed⟩ ⟨e.cells q, fixed⟩ := by
  have hr : Reachable (FiniteWireFrame.board (walkActive p q) ∅) (some 1)
      ⟨p, ∅⟩ ⟨q, ∅⟩ := by
    apply FiniteWireFrame.walk_rectangle (Finset.disjoint_empty_left _) p q
    intro r hx hx' hy hy'
    refine ⟨(FiniteWireFrame.floor_iff _ _ _).mpr ((mem_walkActive p q r).mpr ⟨hx,hx',hy,hy'⟩),
      Finset.notMem_empty _⟩
  simpa only [GridEmbedding.extend, Finset.map_empty, Finset.empty_union] using F.replay hr

/-- The support, moving box, and empty destination of one unit push. -/
def pushActive (support src dst : Cell w h) : Finset (Cell w h) := {support, src, dst}

/-- A three-cell frame performs the actual push with every outside box retained. -/
theorem push_ambient (support src dst : Cell w h) (d : Direction)
    (hax : Adjacent d support src) (hxd : Adjacent d src dst)
    (e : GridEmbedding w h W H) {B : Board W H} {fixed : Finset (Cell W H)}
    (F : FiniteWireFrame.Frame (pushActive support src dst) e B fixed) :
    Reachable B (some 1)
      (e.extend fixed ⟨support, {src}⟩) (e.extend fixed ⟨src, {dst}⟩) := by
  let A := FiniteWireFrame.board (pushActive support src dst) ∅
  have hsupport : support ∉ A.walls := by
    apply (FiniteWireFrame.floor_iff _ _ _).mpr
    simp only [pushActive, Finset.mem_insert, true_or]
  have hsource : src ∉ A.walls := by
    apply (FiniteWireFrame.floor_iff _ _ _).mpr
    simp only [pushActive, Finset.mem_insert, Finset.mem_singleton, true_or, or_true]
  have hdest : dst ∉ A.walls := by
    apply (FiniteWireFrame.floor_iff _ _ _).mpr
    simp only [pushActive, Finset.mem_insert, Finset.mem_singleton, or_true]
  have hs : (⟨support, {src}⟩ : State w h).Valid A :=
    ⟨hsupport, Finset.disjoint_singleton_left.mpr hsource, by simpa only [Finset.mem_singleton] using hax.ne⟩
  have hm := SingleMoveView.push hs hax (Finset.mem_singleton_self _) hxd hdest
    (by simpa only [Finset.mem_singleton] using hxd.ne.symm)
  have hmove : Move A (some 1) d ⟨support, {src}⟩ ⟨src, {dst}⟩ := by
    apply Move.single_iff.mpr
    simpa only [Finset.erase_singleton, Finset.insert_empty] using hm
  exact F.replay (Relation.ReflTransGen.single ⟨d, hmove⟩)

end PushPuzzle.PushS.FiniteAtomFrames
