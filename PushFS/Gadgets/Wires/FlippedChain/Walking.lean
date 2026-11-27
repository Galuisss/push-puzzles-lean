/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.FlippedChain.Placement

/-! Four actual corner walks with both independently phased pieces and the five real walking collar slots. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.FlippedChain


set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

variable (n : ℕ) (hn : 2301≤n)

def corner (i : Fin 4) : C n := ![(⟨1,by clear hn; omega⟩,1),(⟨n+23,by clear hn; omega⟩,1),
  (⟨1,by clear hn; omega⟩,19),(⟨n+23,by clear hn; omega⟩,19)] i

theorem allNeighbors_bounds {p : C n} (hp : p∈allNeighbors n) : p.2.val=10 ∧ (p.1.val≤1 ∨ n+22≤p.1.val) := by
  simp only [allNeighbors,Finset.mem_insert,Finset.mem_singleton] at hp
  rcases hp with rfl|rfl|rfl|rfl|rfl <;> simp

private theorem allNeighbors_floor : Disjoint (allNeighbors n) (walls n hn) := by
  apply Finset.disjoint_left.mpr
  intro p hp hw
  have hh:=allNeighbors_bounds n hp
  have hr:=walls_rows n hn hw
  omega

namespace Walking

variable (fixed : Finset (C n)) (hf : fixed⊆allNeighbors n)

include hf in
private theorem external_floor (goals : Finset (C n)) (a : Phases) :
    Disjoint (Frame.chainExternal n fixed a) (board n hn goals).walls ∧
    Disjoint (Frame.flipExternal n hn fixed a) (board n hn goals).walls := by
  have hh:=Finset.disjoint_union_left.mp (boxes_floor n hn a goals)
  have hfix:=(allNeighbors_floor n hn).mono_left hf
  exact ⟨Finset.disjoint_union_left.mpr ⟨hh.2,hfix⟩,Finset.disjoint_union_left.mpr ⟨hh.1,hfix⟩⟩

include hf in
private theorem chain_fixed (a : Phases) : Frame.chainFixed n fixed a⊆Chain.allNeighbors n := by
  intro p hp
  rcases Finset.mem_union.mp ((Frame.mem_chainFixed n fixed a p).mp hp) with hp|hp
  · obtain ⟨q,hq,he⟩:=Finset.mem_map.mp hp
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hq
    have hx:=congrArg (fun p : C n=>p.1.val) he
    have hy:=congrArg (fun p : C n=>p.2.val) he
    rw [flip_x,chain_x] at hx
    rw [flip_y,chain_y] at hy
    have hb:=flip_bounds a.2 i
    have hpBound:=p.1.isLt
    simp only [Chain.allNeighbors,Finset.mem_insert,Finset.mem_singleton,Prod.ext_iff,Fin.ext_iff]
    omega
  · have hb:=allNeighbors_bounds n (hf hp)
    rw [chain_x,chain_y] at hb
    have hpBound:=p.1.isLt
    simp only [Chain.allNeighbors,Finset.mem_insert,Finset.mem_singleton,Prod.ext_iff,Fin.ext_iff]
    omega

include hf in
private theorem flip_fixed
    (a : Phases) : Frame.flipFixed n hn fixed a⊆Flip.template.reservedCells := by
  intro p hp
  have hshape : p.2.val=10 ∧ (p.1.val≤1 ∨ 22≤p.1.val) := by
    rcases Finset.mem_union.mp ((Frame.mem_flipFixed n hn fixed a p).mp hp) with hp|hp
    · obtain ⟨q,hq,he⟩:=Finset.mem_map.mp hp
      rw [Chain.boxes_image] at hq
      obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hq
      have hx:=congrArg (fun p : C n=>p.1.val) he
      have hy:=congrArg (fun p : C n=>p.2.val) he
      rw [chain_x,flip_x] at hx
      rw [chain_y,flip_y,Chain.position_row] at hy
      have hb:=Polyline.chain_phase_bounds n hn a.1 i
      have ha : a.1.toNat≤1 := by cases a.1 <;> decide
      exact ⟨hy.symm,Or.inl (by omega)⟩
    · have hb:=allNeighbors_bounds n (hf hp)
      rw [flip_x,flip_y] at hb
      omega
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  change decide (p.2.val=10 ∧ p.1.val≠9 ∧ p.1.val≠10)=true
  exact decide_eq_true (by omega)

include hf in
private theorem walk_row (goals : Finset (C n)) (a : Phases) (p q : C n) (hp : p.2.val=3)
    (hq : q.2.val=3) :
    Reachable (board n hn goals) (some 1) ⟨p,boxes n hn a∪fixed⟩ ⟨q,boxes n hn a∪fixed⟩ := by
  have hp' : p=(p.1,3) := Prod.ext rfl (Fin.ext hp)
  have hq' : q=(q.1,3) := Prod.ext rfl (Fin.ext hq)
  rw [hp',hq']
  apply walk_horizontal (Finset.disjoint_union_left.mpr ⟨boxes_floor n hn a goals,(allNeighbors_floor n hn).mono_left hf⟩)
  intro x _ _
  constructor
  · intro hw
    have hh:=walls_rows n hn hw
    change 3=8∨3=9∨3=11∨3=12 at hh
    omega
  · intro hb
    rcases Finset.mem_union.mp hb with hb|hb
    · have hh:=boxes_row n hn a hb
      change 3=10 at hh
      contradiction
    · have hh:=(allNeighbors_bounds n (hf hb)).1
      change 3=10 at hh
      contradiction

include hf in
private theorem chain_corners (goals : Finset (C n)) (a : Phases) (i : Fin 4) :
    Reachable (board n hn goals) (some 1) (Frame.state n hn fixed a)
      ⟨(chainPlacement n).cells (Chain.corner n i),boxes n hn a∪fixed⟩ ∧
    Reachable (board n hn goals) (some 1) ⟨(chainPlacement n).cells (Chain.corner n i),boxes n hn a∪fixed⟩
      (Frame.state n hn fixed a) := by
  have hh:=Chain.corners_placed_allNeighbors n hn (Chain.uniform n a.1) i (Frame.chainFixed n fixed a)
    (chain_fixed n fixed hf a) (chainPlacement n) (chain_walls n hn goals)
    (fun p hp=>(Frame.mem_chainFixed n fixed a p).mpr hp) (fun p hp=>(Frame.mem_chainFixed n fixed a p).mp hp)
    (external_floor n hn fixed hf goals a).1
  change Reachable _ _ ((chainPlacement n).extend (Frame.chainExternal n fixed a) ⟨Chain.hub n hn,Chain.boxes n hn (Chain.uniform n a.1)⟩)
      ((chainPlacement n).extend (Frame.chainExternal n fixed a) ⟨Chain.corner n i,Chain.boxes n hn (Chain.uniform n a.1)⟩) ∧
    Reachable _ _ ((chainPlacement n).extend (Frame.chainExternal n fixed a) ⟨Chain.corner n i,Chain.boxes n hn (Chain.uniform n a.1)⟩)
      ((chainPlacement n).extend (Frame.chainExternal n fixed a) ⟨Chain.hub n hn,Chain.boxes n hn (Chain.uniform n a.1)⟩) at hh
  have he : (chainPlacement n).cells (Chain.hub n hn)=player n := by
    apply Prod.ext <;> apply Fin.ext <;> rfl
  simpa only [Frame.place_chain,he,Frame.state,Gates.withFixed,FlippedChain.state] using hh

include hf in
private theorem flip_corners (goals : Finset (C n)) (a : Phases) (i : Fin 4) :
    Reachable (board n hn goals) (some 1) (Frame.state n hn fixed a)
      ⟨(flipPlacement n).cells (Flip.corner i),boxes n hn a∪fixed⟩ ∧
    Reachable (board n hn goals) (some 1) ⟨(flipPlacement n).cells (Flip.corner i),boxes n hn a∪fixed⟩
      (Frame.state n hn fixed a) := by
  have hfw : Disjoint (Frame.flipFixed n hn fixed a) Flip.template.walls := by
    apply Finset.disjoint_left.mpr
    intro p hp hw
    exact Finset.disjoint_left.mp (external_floor n hn fixed hf goals a).2
      ((Frame.mem_flipFixed n hn fixed a p).mp hp) ((flip_walls n hn goals p).mpr hw)
  have hh:=Flip.checked.corners_covered a.2 i (Frame.flipFixed n hn fixed a) (flip_fixed n hn fixed hf a) hfw
    (flipPlacement n) (flip_walls n hn goals)
    (fun p hp=>(Frame.mem_flipFixed n hn fixed a p).mpr hp) (fun p hp=>(Frame.mem_flipFixed n hn fixed a p).mp hp)
    (external_floor n hn fixed hf goals a).2
  change Reachable _ _ ((flipPlacement n).extend (Frame.flipExternal n hn fixed a) ⟨Flip.hub,Flip.template.boxes a.2⟩)
      ((flipPlacement n).extend (Frame.flipExternal n hn fixed a) ⟨Flip.corner i,Flip.template.boxes a.2⟩) ∧
    Reachable _ _ ((flipPlacement n).extend (Frame.flipExternal n hn fixed a) ⟨Flip.corner i,Flip.template.boxes a.2⟩)
      ((flipPlacement n).extend (Frame.flipExternal n hn fixed a) ⟨Flip.hub,Flip.template.boxes a.2⟩) at hh
  rw [Frame.place_flip,Frame.place_flip] at hh
  have hb:=walk_row n hn fixed hf goals a (player n) ((flipPlacement n).cells Flip.hub) rfl rfl
  have ha:=walk_row n hn fixed hf goals a ((flipPlacement n).cells Flip.hub) (player n) rfl rfl
  exact ⟨hb.trans hh.1,hh.2.trans ha⟩

include hf in
/-- The four real exterior corners remain reachable in both directions for all independent canonical piece phases. -/
private theorem corners (goals : Finset (C n)) (a : Phases) (i : Fin 4) :
    Reachable (board n hn goals) (some 1) (Frame.state n hn fixed a) ⟨corner n i,boxes n hn a∪fixed⟩ ∧
    Reachable (board n hn goals) (some 1) ⟨corner n i,boxes n hn a∪fixed⟩ (Frame.state n hn fixed a) := by
  fin_cases i
  · exact chain_corners n hn fixed hf goals a 0
  · exact flip_corners n hn fixed hf goals a 1
  · exact chain_corners n hn fixed hf goals a 2
  · exact flip_corners n hn fixed hf goals a 3

end Walking

/-- The four exact corner walks also replay with the complete actual ambient foreign collar inventory. -/
theorem corners_placed {W H : ℕ} (a : Phases) (i : Fin 4) (fixed : Finset (C n)) (hf : fixed⊆allNeighbors n)
    (e : GridEmbedding (n+25) 21 W H) {B : Board W H} {outside : Finset (Cell W H)}
    (hw : e.WallsAgree (board n hn ∅) B) (hinside : ∀p,e.cells p∈outside → p∈fixed)
    (hfixed : ∀p∈fixed,e.cells p∈outside) (he : Disjoint outside B.walls) :
    Reachable B (some 1) (e.extend outside (state n hn a)) (e.extend outside ⟨corner n i,boxes n hn a⟩) ∧
    Reachable B (some 1) (e.extend outside ⟨corner n i,boxes n hn a⟩) (e.extend outside (state n hn a)) := by
  have hh:=Walking.corners n hn fixed hf ∅ a i
  exact ⟨e.reachable_withFixed hw hinside hfixed he hh.1,e.reachable_withFixed hw hinside hfixed he hh.2⟩

end PushPuzzle.PushFS.Gadgets.Wires.FlippedChain
