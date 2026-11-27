/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Chain.Targets
public import PushFS.AxisTracks

/-! Static classification of the actual arbitrary-length wire board. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Chain


set_option maxRecDepth 65536
set_option maxHeartbeats 500000

/-- The finite physical rectangles cover the entire assembled rectangle. -/
private theorem covered (n : ℕ) (hn : 2301 ≤ n) (p : C n) :
    ∃ i : Block n, ∃ q : Tile.C (kind n i), embed n hn i q = p := by
  have cover : ∀ t : ℕ, 0 < t → t ≤ blockCount n → ∀ x : ℕ, x < offset n t+5 →
      ∃ i : Block n, i.val < t ∧ offset n i.val ≤ x ∧ x < offset n i.val+Tile.width (kind n i) := by
    intro t
    induction t with
    | zero => omega
    | succ t ih =>
      intro ht htc x hx
      by_cases hz : t = 0
      · subst t
        refine ⟨⟨0,by omega⟩,by omega,?_,?_⟩
        · simp only [Spans.offset_zero]; omega
        · have hh := offset_next n 0
          have hz0 : offset n 0 = 0 := Spans.offset_zero n
          rw [hz0] at hh
          rw [Tile.width_eq]
          change x < offset n 0 + (Tile.span (Spans.kindAt n 0)+5)
          omega
      · by_cases hx' : x < offset n t+5
        · obtain ⟨i,hi,hlo,hhi⟩ := ih (by omega) (by omega) x hx'
          exact ⟨i,by omega,hlo,hhi⟩
        · refine ⟨⟨t,by omega⟩,by simp,(by change offset n t ≤ x; omega),?_⟩
          have hh := offset_next n t
          rw [Tile.width_eq]
          change x < offset n t+(Tile.span (Spans.kindAt n t)+5)
          omega
  obtain ⟨i,_,hlo,hhi⟩ := cover (blockCount n) (blockCount_pos n hn) le_rfl p.1.val
    (by have hh : offset n (blockCount n) = n := Spans.offset_finish n hn; rw [hh]; exact p.1.isLt)
  let q : Tile.C (kind n i) := (⟨p.1.val-offset n i.val,by omega⟩,p.2)
  refine ⟨i,q,?_⟩
  apply Prod.ext <;> apply Fin.ext
  · change offset n i.val+(p.1.val-offset n i.val) = p.1.val
    omega
  · exact embed_y n hn i q

private theorem tile_guard (k : Bool) (x : Fin (Tile.width k)) :
    (x,9) ∈ Tile.walls k ∨ (x,11) ∈ Tile.walls k := by
  cases k
  · change (x,9) ∈ Straight.template.walls ∨ (x,11) ∈ Straight.template.walls
    rcases Straight.rail_guard x with hh | hh
    · exact Or.inl ((Straight.template.mem_walls _).mpr hh)
    · exact Or.inr ((Straight.template.mem_walls _).mpr hh)
  · change (x,9) ∈ Parity.template.walls ∨ (x,11) ∈ Parity.template.walls
    rcases Parity.rail_guard x with hh | hh
    · exact Or.inl ((Parity.template.mem_walls _).mpr hh)
    · exact Or.inr ((Parity.template.mem_walls _).mpr hh)

/-- At every actual rail cell one perpendicular side is a literal wall. -/
theorem rail_guard (n : ℕ) (hn : 2301 ≤ n) (x : Fin (n+5)) :
    (x,9) ∈ walls n hn ∨ (x,11) ∈ walls n hn := by
  obtain ⟨i,q,he⟩ := covered n hn (x,10)
  have hx := congrArg (fun p : C n => p.1.val) he
  simp only [embed_x] at hx
  have eqy (y : Fin 21) : embed n hn i (q.1,y) = (x,y) := by
    apply Prod.ext <;> apply Fin.ext
    · exact hx
    · exact embed_y n hn i (q.1,y)
  rcases tile_guard (kind n i) q.1 with hw | hw
  · exact Or.inl (eqy 9 ▸ (walls_exact n hn i (q.1,9)).mpr hw)
  · exact Or.inr (eqy 11 ▸ (walls_exact n hn i (q.1,11)).mpr hw)

/-- A displacement from the complete rail stays on its actual row. -/
theorem displacement_row (n : ℕ) (hn : 2301 ≤ n) (goals : Finset (C n))
    {p q : C n} (hp : p.2.val = 10) (hd : Displacement (board n hn goals) p q) : q.2.val = 10 := by
  obtain ⟨_,d,rear,hr,hq,hrw,hqw⟩ := hd
  have hg := rail_guard n hn p.1
  cases d with
  | east => exact congrArg Fin.val hq.2 |>.trans hp
  | west => exact congrArg Fin.val hq.2 |>.trans hp
  | north =>
    have hdest : q = (p.1,9) := by refine Prod.ext hq.1 ?_; apply Fin.ext; change q.2.val = 9; simp only [Adjacent] at hq; omega
    have hrear : rear = (p.1,11) := by refine Prod.ext hr.1.symm ?_; apply Fin.ext; change rear.2.val = 11; simp only [Adjacent] at hr; omega
    rcases hg with hg | hg
    · exact False.elim (hqw (hdest ▸ hg))
    · exact False.elim (hrw (hrear ▸ hg))
  | south =>
    have hdest : q = (p.1,11) := by refine Prod.ext hq.1 ?_; apply Fin.ext; change q.2.val = 11; simp only [Adjacent] at hq; omega
    have hrear : rear = (p.1,9) := by refine Prod.ext hr.1.symm ?_; apply Fin.ext; change rear.2.val = 9; simp only [Adjacent] at hr; omega
    rcases hg with hg | hg
    · exact False.elim (hrw (hrear ▸ hg))
    · exact False.elim (hqw (hdest ▸ hg))

private theorem phase_bounds (k phase : Bool) (i : Fin (Tile.count k)) :
    2+phase.toNat ≤ (Tile.position k phase i).1.val ∧
      (Tile.position k phase i).1.val ≤ Tile.span k+phase.toNat := by
  have hh : ∀ k phase, ∀ i : Fin (Tile.count k),
      2+phase.toNat ≤ (Tile.position k phase i).1.val ∧
      (Tile.position k phase i).1.val ≤ Tile.span k+phase.toNat := by decide +kernel
  exact hh k phase i

private theorem tile_sparse (k phase : Bool) (i j : Fin (Tile.count k)) (d : Direction) :
    ¬Adjacent d (Tile.position k phase i) (Tile.position k phase j) := by
  cases k
  · exact Straight.sparse_slots phase i j d
  · exact Parity.sparse_slots phase i j d

private theorem block_gap (n : ℕ) (hn : 2301 ≤ n) (phase : Bool)
    (i j : Block n) (hij : i < j) (u : Fin (Tile.count (kind n i))) (v : Fin (Tile.count (kind n j))) :
    (position n hn (uniform n phase) ⟨i,u⟩).1.val+2 ≤
      (position n hn (uniform n phase) ⟨j,v⟩).1.val := by
  have ho := offset_mono n (i.val+1) j.val hij
  rw [offset_next] at ho
  have hu := phase_bounds (kind n i) phase u
  have hv := phase_bounds (kind n j) phase v
  change offset n i.val + (Tile.position (kind n i) phase u).1.val+2 ≤
    offset n j.val + (Tile.position (kind n j) phase v).1.val
  change offset n i.val+Tile.span (kind n i) ≤ offset n j.val at ho
  omega

/-- The uniform target phases have no adjacent pair, including every seam. -/
theorem sparse_targets (n : ℕ) (hn : 2301 ≤ n) (phase : Bool) (i j : Label n) (d : Direction) :
    ¬Adjacent d (position n hn (uniform n phase) i) (position n hn (uniform n phase) j) := by
  rcases i with ⟨i,u⟩
  rcases j with ⟨j,v⟩
  intro ha
  by_cases hij : i = j
  · subst j
    have hh : Adjacent d (Tile.position (kind n i) phase u) (Tile.position (kind n i) phase v) := by
      cases d <;> simp only [Adjacent, Fin.ext_iff] at ha ⊢ <;>
        simp only [position, embed_x, embed_y, uniform] at ha <;> omega
    exact tile_sparse (kind n i) phase u v d hh
  · have hyi := position_row n hn (uniform n phase) ⟨i,u⟩
    have hyj := position_row n hn (uniform n phase) ⟨j,v⟩
    rcases lt_or_gt_of_ne hij with hij | hij
    · have hg := block_gap n hn phase i j hij u v
      cases d <;> simp only [Adjacent] at ha <;> omega
    · have hg := block_gap n hn phase j i hij v u
      cases d <;> simp only [Adjacent] at ha <;> omega

/-- The entire row has one global geometric name. -/
def axisName (n : ℕ) (p : C n) : AxisTrack := if p.2.val = 10 then .horizontal 10 else .outside

/-- C2 and C3 are derived from the actual long-chain wall union. -/
def axisTracks (n : ℕ) (hn : 2301 ≤ n) (a b : Bool) : AxisTracks (puzzle n hn a b) where
  name := axisName n
  supported p := by unfold axisName; split <;> simp_all [AxisTrack.Supports]
  active p hp := by
    have hh := boxes_row n hn (uniform n a) hp
    simp [axisName,hh]
  displacement p q hd := by
    by_cases hp : p.2.val = 10
    · have hq := displacement_row n hn _ hp hd
      exact Or.inl (by simp [axisName,hp,hq])
    · by_cases hq : q.2.val = 10
      · exact Or.inr (by simp [axisName,hp,hq,AxisTrack.level])
      · exact Or.inl (by simp [axisName,hp,hq])
  separated p hp q hq _ d := by
    change p ∈ boxes n hn (uniform n b) at hp
    change q ∈ boxes n hn (uniform n b) at hq
    rw [boxes_image] at hp hq
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hq
    exact sparse_targets n hn b i j d

end PushPuzzle.PushFS.Gadgets.Wires.Chain
