/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.FlippedChain.Atlas
public import PushFS.Gadgets.Wires.Polyline.LSparse
public import PushFS.Gadgets.Wires.Soundness.Local

/-! All true FlippedChain goals are sparse; every actual active displacement stays on the same real row. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.FlippedChain


set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

variable (n : ℕ) (hn : 2301≤n)

theorem boxes_row (a : Phases) {p : C n} (hp : p∈boxes n hn a) : p.2.val=10 := by
  rcases Finset.mem_union.mp hp with hp|hp
  · obtain ⟨q,hq,rfl⟩:=Finset.mem_map.mp hp
    rw [chain_y]
    exact Chain.boxes_row n hn _ hq
  · obtain ⟨q,hq,rfl⟩:=Finset.mem_map.mp hp
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hq
    rw [flip_y]
    exact (flip_bounds a.2 i).1

theorem boxes_floor (a : Phases) (goals : Finset (C n)) : Disjoint (boxes n hn a) (board n hn goals).walls := by
  apply Finset.disjoint_left.mpr
  intro p hp hw
  rcases Finset.mem_union.mp hp with hp|hp
  · obtain ⟨q,hq,rfl⟩:=Finset.mem_map.mp hp
    exact Finset.disjoint_left.mp (Chain.boxes_floor n hn _) hq ((chain_walls n hn goals q).mp hw)
  · obtain ⟨q,hq,rfl⟩:=Finset.mem_map.mp hp
    exact Finset.disjoint_left.mp (Flip.checked.boxes_floor _) hq ((flip_walls n hn goals q).mp hw)

theorem rail_guard (x : Fin (n+25)) : (x,9)∈walls n hn ∨ (x,11)∈walls n hn := by
  by_cases hx : x.val<n+5
  · let q : Fin (n+5):=⟨x.val,hx⟩
    have he (y : Fin 21) : (chainPlacement n).cells (q,y)=(x,y) := by
      apply Prod.ext <;> apply Fin.ext
      · exact chain_x n (q,y)
      · exact chain_y n (q,y)
    rcases Chain.rail_guard n hn q with hw|hw
    · exact Or.inl (he 9 ▸ (chain_walls n hn ∅ (q,9)).mpr hw)
    · exact Or.inr (he 11 ▸ (chain_walls n hn ∅ (q,11)).mpr hw)
  · let q : Fin 25:=⟨x.val-n,by have := x.isLt; omega⟩
    have he (y : Fin 21) : (flipPlacement n).cells (q,y)=(x,y) := by
      apply Prod.ext <;> apply Fin.ext
      · change n+(x.val-n)=x.val
        omega
      · exact flip_y n (q,y)
    rcases Flip.rail_guard q with hw|hw
    · exact Or.inl (he 9 ▸ (flip_walls n hn ∅ (q,9)).mpr ((Flip.template.mem_walls _).mpr hw))
    · exact Or.inr (he 11 ▸ (flip_walls n hn ∅ (q,11)).mpr ((Flip.template.mem_walls _).mpr hw))

theorem displacement_row (goals : Finset (C n)) {p q : C n} (hp : p.2.val=10)
    (hd : Displacement (board n hn goals) p q) : q.2.val=10 := by
  obtain ⟨_,d,rear,hr,hq,hrw,hqw⟩:=hd
  have hg:=rail_guard n hn p.1
  cases d with
  | east=>exact congrArg Fin.val hq.2 |>.trans hp
  | west=>exact congrArg Fin.val hq.2 |>.trans hp
  | north=>
    have hdest : q=(p.1,9) := by refine Prod.ext hq.1 ?_; apply Fin.ext; change q.2.val=9; simp only [Adjacent] at hq; omega
    have hrear : rear=(p.1,11) := by refine Prod.ext hr.1.symm ?_; apply Fin.ext; change rear.2.val=11; simp only [Adjacent] at hr; omega
    rcases hg with hg|hg
    · exact False.elim (hqw (hdest ▸ hg))
    · exact False.elim (hrw (hrear ▸ hg))
  | south=>
    have hdest : q=(p.1,11) := by refine Prod.ext hq.1 ?_; apply Fin.ext; change q.2.val=11; simp only [Adjacent] at hq; omega
    have hrear : rear=(p.1,9) := by refine Prod.ext hr.1.symm ?_; apply Fin.ext; change rear.2.val=9; simp only [Adjacent] at hr; omega
    rcases hg with hg|hg
    · exact False.elim (hrw (hrear ▸ hg))
    · exact False.elim (hqw (hdest ▸ hg))

def axisName (p : C n) : AxisTrack := if p.2.val=10 then .horizontal 10 else .outside

private theorem adjacent_bounds {d : Direction} {p q : C n} (ha : Adjacent d p q) :
    p.1.val≤q.1.val+1 ∧ q.1.val≤p.1.val+1 ∧ p.2.val≤q.2.val+1 ∧ q.2.val≤p.2.val+1 := by
  cases d <;> simp only [Adjacent] at ha <;> omega

theorem sparse_targets (phase : Bool) {p q : C n} (hp : p∈boxes n hn (uniform phase))
    (hq : q∈boxes n hn (uniform phase)) (d : Direction) : ¬Adjacent d p q := by
  rcases Finset.mem_union.mp hp with hp|hp
  · rcases Finset.mem_union.mp hq with hq|hq
    · obtain ⟨p,hpLocal,rfl⟩:=Finset.mem_map.mp hp
      obtain ⟨q,hqLocal,rfl⟩:=Finset.mem_map.mp hq
      rw [Chain.boxes_image] at hpLocal hqLocal
      obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hpLocal
      obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hqLocal
      exact fun ha=>Chain.sparse_targets n hn phase i j d ((Polyline.translate_adjacent_iff 0 0 _ _ d _ _).mp ha)
    · obtain ⟨p,hpLocal,rfl⟩:=Finset.mem_map.mp hp
      obtain ⟨q,hqLocal,rfl⟩:=Finset.mem_map.mp hq
      rw [Chain.boxes_image] at hpLocal
      obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hpLocal
      obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hqLocal
      intro ha
      have hb:=adjacent_bounds n ha
      have hi:=Polyline.chain_phase_bounds n hn phase i
      have hj:=flip_bounds phase j
      simp only [chain_x,flip_x,uniform] at hb
      omega
  · rcases Finset.mem_union.mp hq with hq|hq
    · exact fun ha=>sparse_targets_reverse hp hq ha
    · obtain ⟨p,hpLocal,rfl⟩:=Finset.mem_map.mp hp
      obtain ⟨q,hqLocal,rfl⟩:=Finset.mem_map.mp hq
      obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hpLocal
      obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hqLocal
      exact fun ha=>Flip.sparse_slots phase i j d ((Polyline.translate_adjacent_iff n 0 _ _ d _ _).mp ha)
where
  sparse_targets_reverse {p q : C n} (hp : p∈flipBoxes n phase) (hq : q∈chainBoxes n hn phase) (ha : Adjacent d p q) : False := by
    obtain ⟨p,hpLocal,rfl⟩:=Finset.mem_map.mp hp
    obtain ⟨q,hqLocal,rfl⟩:=Finset.mem_map.mp hq
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hpLocal
    rw [Chain.boxes_image] at hqLocal
    obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp hqLocal
    have hb:=adjacent_bounds n ha
    have hi:=flip_bounds phase i
    have hj:=Polyline.chain_phase_bounds n hn phase j
    simp only [chain_x,flip_x] at hb
    omega

/-- All C1–C3 data are derived from every actual source/target slot and the real two-piece wall union. -/
def axisTracks (a b : Bool) : AxisTracks (storageInstance n hn a b) where
  name:=axisName n
  supported p:=by
    unfold axisName
    split
    · assumption
    · trivial
  active p hp:=by
    change p∈(atlas n hn (uniform a) (uniform b)).initial.boxes at hp
    rw [initial_boxes] at hp
    simp [axisName,boxes_row n hn _ hp]
  displacement p q hd:=by
    by_cases hp : p.2.val=10
    · change Displacement (atlas n hn (uniform a) (uniform b)).board p q at hd
      rw [board_eq] at hd
      have hq:=displacement_row n hn _ hp hd
      exact Or.inl (by simp [axisName,hp,hq])
    · by_cases hq : q.2.val=10
      · exact Or.inr (by simp [axisName,hp,hq,AxisTrack.level])
      · exact Or.inl (by simp [axisName,hp,hq])
  separated p hp q hq _ d:=by
    change p∈(atlas n hn (uniform a) (uniform b)).board.goals at hp
    change q∈(atlas n hn (uniform a) (uniform b)).board.goals at hq
    rw [goals_eq] at hp hq
    exact sparse_targets n hn b hp hq d

end PushPuzzle.PushFS.Gadgets.Wires.FlippedChain
