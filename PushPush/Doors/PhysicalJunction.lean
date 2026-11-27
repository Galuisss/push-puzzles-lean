/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.PhysicalCollision
public import PushPush.Doors.JunctionColumn

/-! Successful input-room slides select exactly the actual protected endpoint caps. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open PushFS (Cell Direction Adjacent)

private theorem Protected.junction_neighbors_empty {storage : Bool} {I : Instance}
    {s : PushFS.State (layout storage I).width (layout storage I).height}
    (hs : Protected storage I s) (v j : ℕ) (hv : v < (labels I).length) (hj : j < slots I)
    (p : Cell (layout storage I).width (layout storage I).height)
    (hx : p.1.val = (layout storage I).rackX - 1)
    (hy : p.2.val = roomBase I v j + (layout storage I).shift + 1 ∨
      p.2.val + 1 = roomBase I v j + (layout storage I).shift + chamberHeight I) : p ∉ s.boxes := by
  have hgn := junction_divider_mem storage I v j hv hj
  have hgs := junction_south_divider_mem storage I v j hv hj
  rcases hy with hy | hy
  · let divider := workCell storage I (roomBase I v j) (dividers_fit storage I hgn)
    have hg := hs.dividers _ hgn divider rfl rfl
    apply hg.2 p
    exact Or.inr ⟨Fin.ext hx, hy⟩
  · let divider := workCell storage I (roomBase I v j + chamberHeight I) (dividers_fit storage I hgs)
    have hg := hs.dividers _ hgs divider rfl rfl
    apply hg.2 p
    apply Or.inl
    exact ⟨Fin.ext hx, by change p.2.val + 1 = roomBase I v j + chamberHeight I + (layout storage I).shift; omega⟩

namespace Stock

variable {storage : Bool} {I : Instance}

private theorem junction_input_length_one (S : Stock I) (v j p : ℕ)
    (hp : p < slots I)
    (hsignal : S.signal = atRow storage I (inputRow I v j p))
    {s : PushFS.State (layout storage I).width (layout storage I).height}
    (hstock : S.Realizes storage s) {d : Direction} {n k : ℕ}
    (r : Slide d s n k) (hn : 0 < n)
    (hfirst : ((r.cell ⟨1, by omega⟩).1.val, (r.cell ⟨1, by omega⟩).2.val) = S.signal)
    (hd : d = .north ∨ d = .south) : n = 1 := by
  have hinventory : s.boxes = insert (r.cell ⟨1, by omega⟩) (S.stationary storage) :=
    hstock.trans (S.boxes_at_signal storage _ hfirst.symm)
  have hxy := hfirst.trans hsignal
  have hx : (r.cell ⟨1, by omega⟩).1.val = (layout storage I).rackX - 1 := congrArg Prod.fst hxy
  have hy : (r.cell ⟨1, by omega⟩).2.val = inputRow I v j p + (layout storage I).shift :=
    congrArg Prod.snd hxy
  have hinput := inputRow_interior I v j p hp
  apply slide_length_one r hn
  intro q ha hbox
  rw [hinventory] at hbox
  rcases Finset.mem_insert.mp hbox with he | hq
  · exact ha.ne he.symm
  · apply S.stationary_junction_clear storage v j q ?_ ?_ ?_ hq
    all_goals
      rcases hd with rfl | rfl <;> simp only [PushFS.Adjacent] at ha
      · have hqx := congrArg Fin.val ha.1
        omega
      · have hqx := congrArg Fin.val ha.1
        omega

theorem junction_input_stop (S : Stock I) (v j p : ℕ)
    (hvertex : v < (labels I).length) (hj : j < slots I) (hp : p < slots I)
    (hsignal : S.signal = atRow storage I (inputRow I v j p))
    {s t : PushFS.State (layout storage I).width (layout storage I).height}
    (hstock : S.Realizes storage s) (ht : Protected storage I t)
    {d : Direction} {k : ℕ} (r : Slide d s 1 k) (hk : 0 < k) (hb : t.boxes = r.boxes)
    (hfirst : ((r.cell ⟨1, by omega⟩).1.val, (r.cell ⟨1, by omega⟩).2.val) = S.signal)
    (hd : d = .north ∨ d = .south) :
    (d = .north ∧ upperUsed I v j = true ∧
      (r.cell ⟨1 + k, by omega⟩).2.val = upperRow I v j + (layout storage I).shift) ∨
    (d = .south ∧ lowerUsed I v j = true ∧
      (r.cell ⟨1 + k, by omega⟩).2.val = lowerRow I v j + (layout storage I).shift) := by
  have hinventory : s.boxes = insert (r.cell ⟨1, by omega⟩) (S.stationary storage) :=
    hstock.trans (S.boxes_at_signal storage _ hfirst.symm)
  have hxy := hfirst.trans hsignal
  have hx : (r.cell ⟨1, by omega⟩).1.val = (layout storage I).rackX - 1 := congrArg Prod.fst hxy
  have hy : (r.cell ⟨1, by omega⟩).2.val = inputRow I v j p + (layout storage I).shift :=
    congrArg Prod.snd hxy
  have hinput := inputRow_interior I v j p hp
  have hh := chamberHeight_ge I
  have hfit := dividers_fit storage I (junction_south_divider_mem storage I v j hvertex hj)
  have hlastmem : r.cell ⟨1 + k, by omega⟩ ∈ t.boxes := hb ▸ r.last_mem_boxes (by omega)
  rcases hd with rfl | rfl
  · let offset : ℕ := if upperUsed I v j then 2 else 0
    have hoff : offset ≤ 2 := by dsimp [offset]; split <;> omega
    let stop := workCell storage I (roomBase I v j + offset) (by omega)
    have hpl := r.lane ⟨1, by omega⟩
    change (r.cell ⟨1, by omega⟩).1.val = s.player.1.val at hpl
    have hfirstpos := r.position ⟨1, by omega⟩
    change -((r.cell ⟨1, by omega⟩).2.val : ℤ) = -(s.player.2.val : ℤ) + 1 at hfirstpos
    have hstopbox : stop ∈ s.boxes := by
      rw [hinventory]
      apply Finset.mem_insert_of_mem
      apply (S.stationary_junction_column storage v j hvertex hj stop rfl
        (by dsimp [stop, workCell, Layout.point]; omega) (by dsimp [stop, workCell, Layout.point]; omega)).mpr
      by_cases hu : upperUsed I v j = true
      · exact Or.inr (Or.inr (Or.inl ⟨hu, by simp only [stop, workCell, Layout.point, offset, hu, ite_true]⟩))
      · apply Or.inl
        simp [stop, workCell, Layout.point, offset, hu]
    let distance := inputRow I v j p - (roomBase I v j + offset) - 1
    have hdistance : k = distance := by
      apply slide_distance_eq r stop distance
      · change (layout storage I).rackX - 1 = s.player.1.val
        omega
      · change -((stop.2.val : ℕ) : ℤ) = -(s.player.2.val : ℤ) + (1 + distance + 1 : ℕ)
        dsimp [stop, distance, workCell, Layout.point]
        omega
      · exact hstopbox
      · intro q hq_lane hlo hhi hqbox
        simp only [Direction.position, Direction.lane] at hq_lane hlo hhi
        dsimp [stop, workCell, Layout.point] at hhi
        rw [hinventory] at hqbox
        rcases Finset.mem_insert.mp hqbox with he | hq
        · subst q
          omega
        · have hqx : q.1.val = (layout storage I).rackX - 1 := by omega
          have hc := (S.stationary_junction_column storage v j hvertex hj q hqx
            (by omega) (by omega)).mp hq
          rcases hc with hc | hc | ⟨hu, hc⟩ | ⟨hl, hc⟩
          · omega
          · omega
          · have ho : offset = 2 := by simp [offset, hu]
            omega
          · omega
    have hlastpos := r.position ⟨1 + k, by omega⟩
    change -((r.cell ⟨1 + k, by omega⟩).2.val : ℤ) = -(s.player.2.val : ℤ) + (1 + k : ℕ) at hlastpos
    have hlasty : (r.cell ⟨1 + k, by omega⟩).2.val =
        roomBase I v j + (layout storage I).shift + offset + 1 := by
      dsimp [distance] at hdistance
      omega
    have hlastx : (r.cell ⟨1 + k, by omega⟩).1.val = (layout storage I).rackX - 1 := by
      have hl := r.lane ⟨1 + k, by omega⟩
      change (r.cell ⟨1 + k, by omega⟩).1.val = s.player.1.val at hl
      omega
    have hu : upperUsed I v j = true := by
      by_contra hu
      have ho : offset = 0 := by simp [offset, hu]
      exact ht.junction_neighbors_empty v j hvertex hj _ hlastx (Or.inl (by omega)) hlastmem
    apply Or.inl
    refine ⟨rfl, hu, ?_⟩
    have ho : offset = 2 := by simp [offset, hu]
    unfold upperRow
    omega
  · let offset : ℕ := if lowerUsed I v j then chamberHeight I - 2 else chamberHeight I
    have hoff : chamberHeight I - 2 ≤ offset ∧ offset ≤ chamberHeight I := by
      dsimp [offset]
      split <;> omega
    let stop := workCell storage I (roomBase I v j + offset) (by omega)
    have hpl := r.lane ⟨1, by omega⟩
    change (r.cell ⟨1, by omega⟩).1.val = s.player.1.val at hpl
    have hfirstpos := r.position ⟨1, by omega⟩
    change ((r.cell ⟨1, by omega⟩).2.val : ℤ) = (s.player.2.val : ℤ) + 1 at hfirstpos
    have hstopbox : stop ∈ s.boxes := by
      rw [hinventory]
      apply Finset.mem_insert_of_mem
      apply (S.stationary_junction_column storage v j hvertex hj stop rfl
        (by dsimp [stop, workCell, Layout.point]; omega) (by dsimp [stop, workCell, Layout.point]; omega)).mpr
      by_cases hl : lowerUsed I v j = true
      · apply Or.inr
        apply Or.inr
        apply Or.inr
        refine ⟨hl, ?_⟩
        simp only [stop, workCell, Layout.point, offset, hl, ite_true]
        omega
      · apply Or.inr
        apply Or.inl
        simp [stop, workCell, Layout.point, offset, hl]
        omega
    let distance := roomBase I v j + offset - inputRow I v j p - 1
    have hdistance : k = distance := by
      apply slide_distance_eq r stop distance
      · change (layout storage I).rackX - 1 = s.player.1.val
        omega
      · change ((stop.2.val : ℕ) : ℤ) = (s.player.2.val : ℤ) + (1 + distance + 1 : ℕ)
        dsimp [stop, distance, workCell, Layout.point]
        omega
      · exact hstopbox
      · intro q hq_lane hlo hhi hqbox
        simp only [Direction.position, Direction.lane] at hq_lane hlo hhi
        dsimp [stop, workCell, Layout.point] at hhi
        rw [hinventory] at hqbox
        rcases Finset.mem_insert.mp hqbox with he | hq
        · subst q
          omega
        · have hqx : q.1.val = (layout storage I).rackX - 1 := by omega
          have hc := (S.stationary_junction_column storage v j hvertex hj q hqx
            (by omega) (by omega)).mp hq
          rcases hc with hc | hc | ⟨hu, hc⟩ | ⟨hl, hc⟩
          · omega
          · omega
          · omega
          · have ho : offset = chamberHeight I - 2 := by simp [offset, hl]
            omega
    have hlastpos := r.position ⟨1 + k, by omega⟩
    change ((r.cell ⟨1 + k, by omega⟩).2.val : ℤ) = (s.player.2.val : ℤ) + (1 + k : ℕ) at hlastpos
    have hlasty : (r.cell ⟨1 + k, by omega⟩).2.val + 1 =
        roomBase I v j + (layout storage I).shift + offset := by
      dsimp [distance] at hdistance
      omega
    have hlastx : (r.cell ⟨1 + k, by omega⟩).1.val = (layout storage I).rackX - 1 := by
      have hl := r.lane ⟨1 + k, by omega⟩
      change (r.cell ⟨1 + k, by omega⟩).1.val = s.player.1.val at hl
      omega
    have hl : lowerUsed I v j = true := by
      by_contra hl
      have ho : offset = chamberHeight I := by simp [offset, hl]
      exact ht.junction_neighbors_empty v j hvertex hj _ hlastx (Or.inr (by omega)) hlastmem
    apply Or.inr
    refine ⟨rfl, hl, ?_⟩
    have ho : offset = chamberHeight I - 2 := by simp [offset, hl]
    unfold lowerRow
    omega

end Stock

/-- A real signal push from a location input selects exactly one present endpoint cap. -/
theorem Control.junction_push {storage : Bool} {I : Instance}
    (register : Fin I.doors.length → Register) (v j p : ℕ)
    (hvertex : v < (labels I).length) (hj : j < slots I) (hp : p < slots I)
    {s t : PushFS.State (layout storage I).width (layout storage I).height}
    (hs : Protected storage I s) (ht : Protected storage I t)
    (hstock : (⟨register, .working (inputRow I v j p)⟩ : Control storage I).stock.Realizes storage s)
    {d : Direction} {n k : ℕ} (r : Slide d s n k) (hn : 0 < n) (hk : 0 < k)
    (hv : s.player ∉ s.boxes) (hb : t.boxes = r.boxes)
    (hfirst : ((r.cell ⟨1, by omega⟩).1.val, (r.cell ⟨1, by omega⟩).2.val) =
      atRow storage I (inputRow I v j p)) :
    (⟨register, .working (inputRow I v j p)⟩ : Control storage I).PhysicalNext t := by
  let current : Control storage I := ⟨register, .working (inputRow I v j p)⟩
  let S := current.stock
  have hfirstS : ((r.cell ⟨1, by omega⟩).1.val, (r.cell ⟨1, by omega⟩).2.val) = S.signal := hfirst
  have hx : (r.cell ⟨1, by omega⟩).1.val = (layout storage I).rackX - 1 := congrArg Prod.fst hfirst
  have hy : (r.cell ⟨1, by omega⟩).2.val = inputRow I v j p + (layout storage I).shift :=
    congrArg Prod.snd hfirst
  have hfull := hs.input_rack_box (junction_input_rack_mem storage I hvertex hj hp)
    (r.cell ⟨1, by omega⟩) hx hy
  have hdv : d = .north ∨ d = .south := by
    by_contra h
    have hdh : d = .east ∨ d = .west := by cases d <;> simp_all
    exact hs.full_rack_no_horizontal ht r hn hk hv hb hfull hdh
  have hn1 := S.junction_input_length_one v j p hp rfl hstock r hn hfirstS hdv
  subst n
  have hstop := S.junction_input_stop v j p hvertex hj hp rfl hstock ht r hk hb hfirstS hdv
  have hinput := inputRow_interior I v j p hp
  have hclear : r.cell ⟨1, by omega⟩ ∉ S.stationary storage :=
    S.stationary_junction_clear storage v j _ hx (by omega) (by omega)
  have hlastx : (r.cell ⟨k + 1, by omega⟩).1.val = (layout storage I).rackX - 1 := by
    have hfl := r.lane ⟨1, by omega⟩
    have hll := r.lane ⟨k + 1, by omega⟩
    rcases hdv with rfl | rfl <;> simp only [Direction.lane] at hfl hll <;> omega
  have hi : (⟨k + 1, by omega⟩ : Fin (1 + k + 1)) = ⟨1 + k, by omega⟩ :=
    Fin.ext (by change k + 1 = 1 + k; omega)
  rcases hstop with ⟨rfl, hused, hlasty⟩ | ⟨rfl, hused, hlasty⟩
  · apply Control.signal_slide
      (Relation.ReflTransGen.single (Control.Step.upper (storage := storage)
        register v j p hvertex hj hp hused)) trivial rfl hstock r hb hfirstS hclear
    apply Prod.ext
    · exact hlastx.symm
    · rw [hi]
      exact hlasty.symm
  · apply Control.signal_slide
      (Relation.ReflTransGen.single (Control.Step.lower (storage := storage)
        register v j p hvertex hj hp hused)) trivial rfl hstock r hb hfirstS hclear
    apply Prod.ext
    · exact hlastx.symm
    · rw [hi]
      exact hlasty.symm

end PushPuzzle.PushPush.Doors.Source
