/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Polyline.LAxisGeometry
public import PushFS.Gadgets.Wires.Polyline.LMovement

/-! True goal separation at every physical L joint, including its two long complete train inventories. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Polyline


variable {w h W H u v : ℕ}

/-- A translated rectangle reflects its direction-labelled unit adjacencies. -/
theorem translate_adjacent_iff (dx dy : ℕ) (hx : dx+w≤W) (hy : dy+h≤H) (d : Direction) (p q : Cell w h) :
    Adjacent d ((GridEmbedding.translate dx dy hx hy).cells p) ((GridEmbedding.translate dx dy hx hy).cells q) ↔
      Adjacent d p q := by
  cases d <;> simp [Adjacent,GridEmbedding.translate,Fin.ext_iff] <;> omega

/-- Unit adjacency in the ambient grid is a genuine unit adjacency before the actual D4 transformation. -/
theorem isometry_translate_adjacent (e : GridIsometry w h u v) (dx dy : ℕ)
    (hx : dx+u≤W) (hy : dy+v≤H) {d : Direction} {p q : Cell w h}
    (ha : Adjacent d ((GridEmbedding.translate dx dy hx hy).cells (e.cells p))
      ((GridEmbedding.translate dx dy hx hy).cells (e.cells q))) :
    Adjacent (e.directions.symm d) p q := by
  have hh := (translate_adjacent_iff dx dy hx hy d (e.cells p) (e.cells q)).mp ha
  apply (e.adjacent (e.directions.symm d) p q).mp
  simpa only [Equiv.apply_symm_apply] using hh

private theorem adjacent_bounds {d : Direction} {p q : Cell w h} (ha : Adjacent d p q) :
    p.1.val≤q.1.val+1 ∧ q.1.val≤p.1.val+1 ∧ p.2.val≤q.2.val+1 ∧ q.2.val≤p.2.val+1 := by
  cases d <;> simp only [Adjacent] at ha <;> refine ⟨?_,?_,?_,?_⟩ <;> omega

namespace L

set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

variable (m n : ℕ) (hm : 2301 ≤ m) (hn : 2301 ≤ n)

private theorem in_phase_region (phase : Bool) {p : C m n} (hp : p∈inBoxes m n hm hn phase) :
    p.2.val=10 ∧ 42≤p.1.val+phase.toNat := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
  rw [Chain.boxes_image] at hq
  obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hq
  have hb := chain_phase_bounds m hm phase l
  have hn1 : phase.toNat≤1 := by cases phase <;> decide
  rw [in_x,in_y,Chain.position_row]
  omega

private theorem turn_phase_region (phase : Bool) {p : C m n} (hp : p∈turnBoxes m n hm hn phase) :
    (p.2.val=10 ∧ p.1.val+phase.toNat≤40) ∨ (p.1.val=10 ∧ p.2.val≤39+phase.toNat) := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hq
  have check : ∀ (phase : Bool) (i : Fin 29),
      ((Turn.template.position phase i).2.val=9 ∧ (Turn.template.position phase i).1.val+phase.toNat≤40) ∨
      ((Turn.template.position phase i).1.val=10 ∧ 1+(Turn.template.position phase i).2.val≤39+phase.toNat) := by decide +kernel
  rw [turn_x,turn_y]
  have hh := check phase i
  omega

private theorem out_phase_region (phase : Bool) {p : C m n} (hp : p∈outBoxes m n hm hn phase) :
    p.1.val=10 ∧ 41+phase.toNat≤p.2.val := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hp
  rw [Chain.boxes_image] at hq
  obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hq
  have hb := chain_phase_bounds n hn phase l
  rw [out_x,out_y,Chain.position_row]
  omega

private theorem in_sparse (phase : Bool) {p q : C m n} (hp : p∈inBoxes m n hm hn phase)
    (hq : q∈inBoxes m n hm hn phase)
    (d : Direction) : ¬Adjacent d p q := by
  obtain ⟨p,hpLocal,rfl⟩ := Finset.mem_map.mp hp
  obtain ⟨q,hqLocal,rfl⟩ := Finset.mem_map.mp hq
  rw [Chain.boxes_image] at hpLocal hqLocal
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hpLocal
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hqLocal
  intro ha
  exact Chain.sparse_targets m hm phase i j _
    (isometry_translate_adjacent (inIso m) 38 0 (by omega : 38+(m+5)≤m+43) (by omega : 0+21≤n+44) ha)

private theorem turn_sparse (phase : Bool) {p q : C m n} (hp : p∈turnBoxes m n hm hn phase)
    (hq : q∈turnBoxes m n hm hn phase)
    (d : Direction) : ¬Adjacent d p q := by
  obtain ⟨p,hpLocal,rfl⟩ := Finset.mem_map.mp hp
  obtain ⟨q,hqLocal,rfl⟩ := Finset.mem_map.mp hq
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hpLocal
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hqLocal
  intro ha
  exact Turn.sparse_slots phase i j d
    ((translate_adjacent_iff 0 1 (by omega : 0+45≤m+43) (by omega : 1+41≤n+44) d _ _).mp ha)

private theorem out_sparse (phase : Bool) {p q : C m n} (hp : p∈outBoxes m n hm hn phase)
    (hq : q∈outBoxes m n hm hn phase)
    (d : Direction) : ¬Adjacent d p q := by
  obtain ⟨p,hpLocal,rfl⟩ := Finset.mem_map.mp hp
  obtain ⟨q,hqLocal,rfl⟩ := Finset.mem_map.mp hq
  rw [Chain.boxes_image] at hpLocal hqLocal
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hpLocal
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hqLocal
  intro ha
  exact Chain.sparse_targets n hn phase i j _
    (isometry_translate_adjacent (outIso n) 0 39 (by omega : 0+21≤m+43) (by omega : 39+(n+5)≤n+44) ha)

private theorem in_turn_sparse (phase : Bool) {p q : C m n} (hp : p∈inBoxes m n hm hn phase)
    (hq : q∈turnBoxes m n hm hn phase)
    (d : Direction) : ¬Adjacent d p q := by
  intro ha
  have hs := adjacent_bounds ha
  have hi := in_phase_region m n hm hn phase hp
  have ht := turn_phase_region m n hm hn phase hq
  have hip := inBoxes_region m n hm hn phase hp
  omega

private theorem turn_out_sparse (phase : Bool) {p q : C m n} (hp : p∈turnBoxes m n hm hn phase)
    (hq : q∈outBoxes m n hm hn phase)
    (d : Direction) : ¬Adjacent d p q := by
  intro ha
  have hs := adjacent_bounds ha
  have ht := turn_phase_region m n hm hn phase hp
  have ho := out_phase_region m n hm hn phase hq
  omega

private theorem in_out_sparse (phase : Bool) {p q : C m n} (hp : p∈inBoxes m n hm hn phase)
    (hq : q∈outBoxes m n hm hn phase)
    (d : Direction) : ¬Adjacent d p q := by
  intro ha
  have hs := adjacent_bounds ha
  have hi := inBoxes_region m n hm hn phase hp
  have ho := outBoxes_region m n hm hn phase hq
  omega

/-- The true all-box target set has no adjacent pair anywhere, including across both physical seams. -/
theorem sparse_targets (phase : Bool) {p q : C m n} (hp : p∈boxes m n hm hn (uniform phase))
    (hq : q∈boxes m n hm hn (uniform phase)) (d : Direction) : ¬Adjacent d p q := by
  rcases Finset.mem_union.mp hp with hp|hp
  · rcases Finset.mem_union.mp hp with hp|hp
    · rcases Finset.mem_union.mp hq with hq|hq
      · rcases Finset.mem_union.mp hq with hq|hq
        · exact in_sparse m n hm hn phase hp hq d
        · exact in_turn_sparse m n hm hn phase hp hq d
      · exact in_out_sparse m n hm hn phase hp hq d
    · rcases Finset.mem_union.mp hq with hq|hq
      · rcases Finset.mem_union.mp hq with hq|hq
        · exact fun ha => in_turn_sparse m n hm hn phase hq hp d.opposite ha.reverse
        · exact turn_sparse m n hm hn phase hp hq d
      · exact turn_out_sparse m n hm hn phase hp hq d
  · rcases Finset.mem_union.mp hq with hq|hq
    · rcases Finset.mem_union.mp hq with hq|hq
      · exact fun ha => in_out_sparse m n hm hn phase hq hp d.opposite ha.reverse
      · exact fun ha => turn_out_sparse m n hm hn phase hq hp d.opposite ha.reverse
    · exact out_sparse m n hm hn phase hp hq d

/-- Every source box belongs to one actual active rail, for every mixed phase assignment. -/
theorem boxes_active (a : Phases) {p : C m n} (hp : p∈boxes m n hm hn a) : axisName m n p≠.outside := by
  rcases Finset.mem_union.mp hp with hp|hp
  · rcases Finset.mem_union.mp hp with hp|hp
    · have hh := inBoxes_region m n hm hn _ hp
      simp [axisName,hh.1,show p.1.val≠10 by omega,show 10<p.1.val by omega]
    · have hh := turnBoxes_region m n hm hn _ hp
      rcases hh with hh|hh
      · simp [axisName,hh.1,show p.1.val≠10 by omega,show 10<p.1.val by omega]
      · simp [axisName,hh.1,show p.2.val≠10 by omega,show 10<p.2.val by omega]
  · have hh := outBoxes_region m n hm hn _ hp
    simp [axisName,hh.1,show p.2.val≠10 by omega,show 10<p.2.val by omega]

/-- The actual complete L instance has its full source/target SCC transfer certificate. -/
def axisTracks (a b : Bool) : AxisTracks (atlas m n hm hn (uniform a) (uniform b)).puzzle where
  name := axisName m n
  supported := (classifier m n hm hn (boxes m n hm hn (uniform b))).supported
  active p hp := by
    change p∈(atlas m n hm hn (uniform a) (uniform b)).initial.boxes at hp
    rw [initial_boxes] at hp
    exact boxes_active m n hm hn _ hp
  displacement p q hd := by
    change Displacement (atlas m n hm hn (uniform a) (uniform b)).board p q at hd
    rw [board_eq] at hd
    exact (classifier m n hm hn _).displacement p q hd
  separated p hp q hq _ d := by
    change p∈(atlas m n hm hn (uniform a) (uniform b)).board.goals at hp
    change q∈(atlas m n hm hn (uniform a) (uniform b)).board.goals at hq
    rw [goals_eq] at hp hq
    exact sparse_targets m n hm hn b hp hq d

/-- C1–C3 are proved from all real slots, all real walls and both exact physical joints. -/
theorem certificate (a b : Bool) : Certificate (atlas m n hm hn (uniform a) (uniform b)).puzzle :=
  (axisTracks m n hm hn a b).toStaticTracks.certificate (atlas m n hm hn (uniform a) (uniform b)).slotMatching

end L
end PushPuzzle.PushFS.Gadgets.Wires.Polyline
