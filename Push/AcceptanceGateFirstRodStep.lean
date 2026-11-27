/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceFrontTrainErasure
public import Push.AcceptanceGateLowerPrefixStep
public import Push.AcceptanceAxisNoExport
import all Push.AcceptanceGateLowerPrefixStep
import all Push.AcceptanceGateAxisNoInput
import all Push.AcceptanceAxisNoExport
import all PushS.PortSignalLocality
import all PushS.PortWalkBudget
import all PushS.PortStreetSeparation

/-! On the whole gate middle column, every inventory edit occurs beyond the complete original upper first rod. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout PushS.RowLabels AcceptanceProgram AcceptanceFrontTrain

private theorem fullAxis_insert {w h : ℕ} {s t : State w h} (R : Finset (Cell w h)) (a z : Cell w h)
    (boxes : t.boxes = insert z (s.boxes.erase a)) (ha : a ∉ R) (hz : z ∈ R) :
    t.boxes ∩ R = insert z (s.boxes ∩ R) := by
  rw [boxes]
  ext q
  simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
  constructor
  · rintro ⟨he | ⟨_, hq⟩, hr⟩
    · exact Or.inl he
    · exact Or.inr ⟨hq, hr⟩
  · rintro (rfl | ⟨hq, hr⟩)
    · exact ⟨Or.inl rfl, hz⟩
    · exact ⟨Or.inr ⟨fun he => ha (he ▸ hr), hq⟩, hr⟩

private theorem fullAxis_erase {w h : ℕ} {s t : State w h} (R : Finset (Cell w h)) (a z : Cell w h)
    (boxes : t.boxes = insert z (s.boxes.erase a)) (hz : z ∉ R) :
    t.boxes ∩ R = (s.boxes ∩ R).erase a := by
  rw [boxes, Finset.insert_inter_of_notMem hz, Finset.erase_inter]

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ []) {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
  (upper : Endpoint) (hu : upper ∈ l.endpoints) (hs : upper.side = .upper) (hport : upper.port = middle)

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate hi hu hs hport

private theorem gate_fullAxis_horizontal_first {u v t : State (p.W + 1) (p.H + 1)} {d : Direction} {n : ℕ}
    (hsu : Reachable (I).board none (I).initial u) (step : Step (I).board none u v)
    (hvt : Reachable (I).board none v t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (run : Run (w := p.W + 1) (h := p.H + 1) (I).board d u n) (hn : 0 < n)
    (hp : v.player = run.cell 1)
    (hb : v.boxes = insert (run.cell ⟨n + 1, by omega⟩) (u.boxes.erase (run.cell 1)))
    (hd : d = .east ∨ d = .west) (hf : run.cell 1 ∈ ordinaryAxis p middle) :
    p.H - readDepth p 1 ≤ (run.cell 1).2.val := by
  let first : Cell (p.W + 1) (p.H + 1) := run.cell 1
  change p.H - readDepth p 1 ≤ first.2.val
  have data := (Finset.mem_filter.mp hf).2
  change first.1.val = p.x middle ∧ 0 < first.2.val ∧ first.2.val < p.H at data
  by_contra hnot
  have hadj := run.adjacent 0
  change Adjacent d (run.cell 0) (run.cell 1) at hadj
  rw [run.start] at hadj
  change Adjacent d u.player first at hadj
  have heven := x_even p middle
  have supported := canonical_player_on_original l p hl hM haxes initial target hsu
    ((Relation.ReflTransGen.single step).trans hvt) accepted
  have row : first.2 ∈ l.workingRowSet p := by
    rcases supported with hc | hr
    · have he := l.streetColumnSet_even p hc
      rcases hd with rfl | rfl <;> simp only [Adjacent] at hadj <;> omega
    · rcases hd with rfl | rfl <;> exact hadj.2 ▸ hr
  rcases (l.workingRowSet_iff p first.2).mp row with hzero | hH | ⟨depth, hv, hy | hy⟩
  · omega
  · omega
  · apply endpoint_axis_horizontal_impossible l p hl hM haxes initial target hgate upper hu
      hsu step hvt accepted run hn hp hb hd hv
    · simpa only [hport] using data.1
    · simpa only [hs, ite_true] using hy
  · have hmax := workingRows_le_last l p hv
    have hmargin := last_depth_margin p
    have hH : p.H = 2 * p.D := rfl
    apply lower_horizontal_first_impossible l p hl hM haxes initial target hgate hi hsu step hvt accepted run hn hp hb hd
    change first ∈ AcceptanceColumnPrefix.band (p.x middle) p.D (p.H - readDepth p 1)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, data.1, by omega, by omega⟩

/-- Every actual gate middle-column step preserves its first train while allowing sufficiently distant lower inventory edits. -/
theorem canonical_gate_fullAxis_editing_step {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (step : Step (I).board none u v)
    (hvt : Reachable (I).board none v t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t)) :
    EditingStep (w := p.W + 1) (h := p.H + 1) (I).board none .south (p.x middle)
      (readDepth p upper.level - 1) p.D
      (BoxMask.keep u (ordinaryAxis p middle)) (BoxMask.keep v (ordinaryAxis p middle)) := by
  let R : Finset (Cell (p.W + 1) (p.H + 1)) := ordinaryAxis p middle
  have hut := (Relation.ReflTransGen.single step).trans hvt
  have hon : ∀ q ∈ R, Direction.south.lane q = p.x middle := fun _ hq => (Finset.mem_filter.mp hq).2.1
  have mask (s : State (p.W + 1) (p.H + 1)) :
      (lineBoxes .south (p.x middle) (BoxMask.keep s R) : Finset (Cell (p.W + 1) (p.H + 1))) = s.boxes ∩ R :=
    BoxMask.lineBoxes_keep hon s
  have hxW := x_add_readLength_lt_W p ((gate_center_lt l hl hi).trans_le haxes) 0
  have hD := p.outer_distance
  have hH : p.H = 2 * p.D := rfl
  let cutCell : Cell (p.W + 1) (p.H + 1) := (⟨p.x middle, by omega⟩, ⟨p.D, by omega⟩)
  have cutFull := canonical_main_central_occupied l p hl hM haxes initial target (gate_center_lt l hl hi)
    (q := cutCell) rfl ⟨by dsimp only [cutCell]; omega, by dsimp only [cutCell]; omega⟩ hsu hut accepted
  have cutRail : cutCell ∈ R := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, rfl, by dsimp only [cutCell]; omega, by dsimp only [cutCell]; omega⟩
  refine ⟨⟨cutCell, by rw [mask]; exact Finset.mem_inter.mpr ⟨cutFull, cutRail⟩, le_rfl⟩, ?_⟩
  have balanced (eqcount : Inventory.count R u = Inventory.count R v) :
      LineAdmissible (I).board none .south (p.x middle) (BoxMask.keep u R) (BoxMask.keep v R) :=
    BoxMask.keep_admissible (ordinaryAxis_runClosed p middle) hon step eqcount
  have initialFrame : Boundary.frame ⊆ holes u := fun _ hf =>
    (canonical_publicWalkInvariant l p hl hM haxes initial target hgate accepted _ hsu hut) (Finset.mem_union_left _ hf)
  have afterFrame : Boundary.frame ⊆ holes v := fun _ hf =>
    (canonical_publicWalkInvariant l p hl hM haxes initial target hgate accepted _ (hsu.tail step) hvt) (Finset.mem_union_left _ hf)
  have bY : p.Y p.levels ≤ p.b p.levels := by
    have hmul := Nat.mul_le_mul_right (p.Y p.levels + p.L p.levels + 10) (show 1 ≤ 8 * (p.axes + 1) by omega)
    unfold Scales.Parameters.b
    omega
  have huY := readDepth_le_last p upper.level
  have h1Y := readDepth_le_last p 1
  have farWork : (p.D : ℤ) + (readDepth p upper.level - 1 : ℕ) ≤ (p.H - readDepth p 1 : ℕ) := by omega
  have actualStep := step
  have frozen : Step (w := p.W + 1) (h := p.H + 1) (I).board none u v := step
  obtain ⟨d, move⟩ := frozen
  cases move with
  | walk _ _ _ _ boxes => exact Or.inl (balanced (by simp only [Inventory.count, boxes]))
  | @push n _ hn _ run hp boxes =>
    have count := Inventory.push_accounting (R := R) run hn boxes
    have noFrameFirst : run.cell 1 ∉ Boundary.frame := fun hf => (mem_holes _).mp (initialFrame hf) (run.first_occupied hn)
    have noFrameLast : run.cell ⟨n + 1, by omega⟩ ∉ Boundary.frame := by
      intro hf
      apply (mem_holes _).mp (afterFrame hf)
      rw [boxes]
      exact Finset.mem_insert_self _ _
    have vertical_transfer (hd : d = .north ∨ d = .south) :
        run.cell 1 ∈ R ↔ run.cell ⟨n + 1, by omega⟩ ∈ R := by
      have col : (run.cell 1).1.val = (run.cell ⟨n + 1, by omega⟩).1.val := by
        rcases hd with rfl | rfl <;> exact (run.lane 1).trans (run.lane ⟨n + 1, by omega⟩).symm
      have interior (q : Cell (p.W + 1) (p.H + 1)) (hf : q ∉ Boundary.frame) :
          q ∈ R ↔ q.1.val = p.x middle := by
        constructor
        · exact fun h => (Finset.mem_filter.mp h).2.1
        · intro hx
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, hx, ?_, ?_⟩
          · by_contra hy
            exact hf ((Boundary.mem_frame q).mpr ⟨.north, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩)
          · by_contra hy
            have hqH := q.2.isLt
            exact hf ((Boundary.mem_frame q).mpr ⟨.south, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩)
      rw [interior _ noFrameFirst, interior _ noFrameLast, col]
    by_cases hf : run.cell 1 ∈ R
    · by_cases hz : run.cell ⟨n + 1, by omega⟩ ∈ R
      · left
        apply balanced
        have hc : Inventory.count R v + 1 = Inventory.count R u + 1 := by simpa only [hf, hz, ite_true] using count
        omega
      · have horizontal : d = .east ∨ d = .west := by
          cases d with
          | east => exact Or.inl rfl
          | west => exact Or.inr rfl
          | north => exact (hz ((vertical_transfer (Or.inl rfl)).mp hf)).elim
          | south => exact (hz ((vertical_transfer (Or.inr rfl)).mp hf)).elim
        have low := gate_fullAxis_horizontal_first l p hl hM haxes initial target hgate hi upper hu hs hport
          hsu actualStep hvt accepted run hn hp boxes horizontal hf
        exact Or.inr (Or.inr ⟨run.cell 1, by change (p.D : ℤ) + (readDepth p upper.level - 1 : ℕ) ≤ ((run.cell 1).2.val : ℤ); omega,
          by rw [mask, mask]; exact fullAxis_erase R _ _ boxes hz⟩)
    · by_cases hz : run.cell ⟨n + 1, by omega⟩ ∈ R
      · have horizontal : d = .east ∨ d = .west := by
          cases d with
          | east => exact Or.inl rfl
          | west => exact Or.inr rfl
          | north => exact (hf ((vertical_transfer (Or.inl rfl)).mpr hz)).elim
          | south => exact (hf ((vertical_transfer (Or.inr rfl)).mpr hz)).elim
        have low : p.H - readDepth p 1 ≤ (run.cell ⟨n + 1, by omega⟩).2.val := by
          by_contra hy
          apply gate_axis_horizontal_impossible l p hl hM haxes initial target hgate hi upper hu hs hport
            hsu actualStep hvt accepted run hn hp boxes horizontal
          have hr := (Finset.mem_filter.mp hz).2
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr.1, hr.2.1, by omega⟩
        exact Or.inr (Or.inl ⟨run.cell ⟨n + 1, by omega⟩, by change (p.D : ℤ) ≤ ((run.cell ⟨n + 1, by omega⟩).2.val : ℤ); omega,
          by rw [mask, mask]; exact fullAxis_insert R _ _ boxes hf hz⟩)
      · left
        apply balanced
        have hc : Inventory.count R v + 0 = Inventory.count R u + 0 := by simpa only [hf, hz, ite_false] using count
        omega

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
