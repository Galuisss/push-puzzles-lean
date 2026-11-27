/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceFrontTrain
public import Push.AcceptanceAxisNoExport
public import Push.AcceptanceSoundnessUpperAxisNoInput
public import Push.AcceptanceMainCut
public import PushS.PortAxisTrains
import all PushS.PortWireGeometry
import all PushS.PortSegments

/-! Before axis inventory cancellation, every real ordinary-axis update preserves its first train or inserts below the central cut. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout PushS.RowLabels AcceptanceProgram AcceptanceFrontTrain

private theorem imported_inter {w h : ℕ} {s t : State w h} (R : Finset (Cell w h)) (a z : Cell w h)
    (boxes : t.boxes = insert z (s.boxes.erase a)) (ha : a ∉ R) (hz : z ∈ R) :
    t.boxes ∩ R = insert z (s.boxes ∩ R) := by
  rw [boxes]
  ext q
  simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_erase]
  constructor
  · rintro ⟨h | ⟨_, h⟩, hr⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, hr⟩
  · rintro (rfl | ⟨h, hr⟩)
    · exact ⟨Or.inl rfl, hz⟩
    · exact ⟨Or.inr ⟨fun he => ha (he ▸ hr), h⟩, hr⟩

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate

private theorem upper_horizontal_input_below_cut (upper : Endpoint) (hu : upper ∈ l.endpoints)
    (hs : upper.side = .upper) {u v t : State (p.W + 1) (p.H + 1)} {d : Direction} {n : ℕ}
    (hsu : Reachable (I).board none (I).initial u) (step : Step (I).board none u v)
    (hvt : Reachable (I).board none v t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (run : Run (w := p.W + 1) (h := p.H + 1) (I).board d u n) (hn : 0 < n) (hp : v.player = run.cell 1)
    (hb : v.boxes = insert (run.cell ⟨n + 1, by omega⟩) (u.boxes.erase (run.cell 1)))
    (hd : d = .east ∨ d = .west) (hz : run.cell ⟨n + 1, by omega⟩ ∈ ordinaryAxis p upper.port) :
    p.D < (run.cell ⟨n + 1, by omega⟩).2.val := by
  let q : Cell (p.W + 1) (p.H + 1) := run.cell ⟨n, by omega⟩
  let z : Cell (p.W + 1) (p.H + 1) := run.cell ⟨n + 1, by omega⟩
  change p.D < z.2.val
  have hadj : Adjacent d q z := run.adjacent ⟨n, by omega⟩
  have hxy := (Finset.mem_filter.mp hz).2
  change z.1.val = p.x upper.port ∧ 0 < z.2.val ∧ z.2.val < p.H at hxy
  have haxisEven := x_even p upper.port
  have hqOdd : q.1.val % 2 = 1 := by
    rcases hd with rfl | rfl <;> simp only [Adjacent] at hadj <;> omega
  have hqy : q.2.val = z.2.val := by
    rcases hd with rfl | rfl <;> exact (congrArg Fin.val hadj.2).symm
  have supported := canonical_push_run_on_original l p hl hM haxes initial target hsu run hn hp hb hvt accepted ⟨n, by omega⟩
  change q ∈ (supportCoordinates l p).original at supported
  have hrow : q.2 ∈ l.workingRowSet p := by
    rcases supported with hc | hr
    · have he := l.streetColumnSet_even p hc
      omega
    · exact hr
  rcases (l.workingRowSet_iff p q.2).mp hrow with hzero | hH | ⟨depth, hdmem, hy | hy⟩
  · omega
  · omega
  · exact (canonical_upper_axis_no_horizontal_input l p hl hM haxes initial target hgate upper hu hs
      hsu step hvt accepted run hn hp hb hd hdmem hxy.1 (hqy ▸ hy)).elim
  · have hmax := workingRows_le_last l p hdmem
    have hlast := last_depth_margin p
    have hH : p.H = 2 * p.D := rfl
    omega

/-- Every actual ordinary-axis step is a genuine admissible line update or an insertion below its occupied central cut. -/
theorem canonical_ordinaryAxis_growing_step {upper lower : Endpoint}
    (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hslSide : lower.side = .lower) (hport : lower.port = upper.port)
    {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (step : Step (I).board none u v)
    (hvt : Reachable (I).board none v t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t)) :
    GrowingStep (w := p.W + 1) (h := p.H + 1) (I).board none .south (p.x upper.port) p.D
      (BoxMask.keep u (ordinaryAxis p upper.port)) (BoxMask.keep v (ordinaryAxis p upper.port)) := by
  let R : Finset (Cell (p.W + 1) (p.H + 1)) := ordinaryAxis p upper.port
  have hut := (Relation.ReflTransGen.single step).trans hvt
  have hon : ∀ q ∈ R, Direction.south.lane q = p.x upper.port := fun q hq => (Finset.mem_filter.mp hq).2.1
  have hxW := x_add_readLength_lt_W p ((l.endpoints_port_lt hl hu).trans_le haxes) 0
  have hD := p.outer_distance
  have hH : p.H = 2 * p.D := rfl
  let cutCell : Cell (p.W + 1) (p.H + 1) := (⟨p.x upper.port, by omega⟩, ⟨p.D, by omega⟩)
  have cutFull := canonical_main_central_occupied l p hl hM haxes initial target
    (l.endpoints_port_lt hl hu) (q := cutCell) rfl ⟨by dsimp only [cutCell]; omega, by dsimp only [cutCell]; omega⟩ hsu hut accepted
  have cutRail : cutCell ∈ R := Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, by dsimp only [cutCell]; omega, by dsimp only [cutCell]; omega⟩
  have mask (s : State (p.W + 1) (p.H + 1)) :
      (lineBoxes .south (p.x upper.port) (BoxMask.keep s R) : Finset (Cell (p.W + 1) (p.H + 1))) = s.boxes ∩ R :=
    BoxMask.lineBoxes_keep hon s
  refine ⟨⟨cutCell, by rw [mask]; exact Finset.mem_inter.mpr ⟨cutFull, cutRail⟩, le_rfl⟩, ?_⟩
  have balanced (eqcount : Inventory.count R u = Inventory.count R v) :
      LineAdmissible (I).board none .south (p.x upper.port) (BoxMask.keep u R) (BoxMask.keep v R) :=
    BoxMask.keep_admissible (ordinaryAxis_runClosed p upper.port) hon step eqcount
  have actualStep := step
  have frozen : Step (w := p.W + 1) (h := p.H + 1) (I).board none u v := step
  obtain ⟨d, move⟩ := frozen
  cases move with
  | walk _ _ _ _ boxes =>
    exact Or.inl (balanced (by simp only [Inventory.count, boxes]))
  | @push n _ hn _ run hp boxes =>
    have hcount := Inventory.push_accounting (R := R) run hn boxes
    have noExport :=  (canonical_ordinaryAxis_no_export l p hl hM haxes initial target hgate
      hu hlow hsuSide hslSide hport hsu actualStep hvt accepted).2 d n run hn hp boxes
    by_cases hfirst : run.cell 1 ∈ R
    · have hlast : run.cell ⟨n + 1, by omega⟩ ∈ R := noExport hfirst
      exact Or.inl (balanced (by
        have hc : Inventory.count R v + 1 = Inventory.count R u + 1 := by simpa only [hfirst, hlast, ite_true] using hcount
        omega))
    · by_cases hlast : run.cell ⟨n + 1, by omega⟩ ∈ R
      · have horizontal : d = .east ∨ d = .west := by
          have hfirstFrame : run.cell 1 ∉ Boundary.frame := by
            intro hf
            have empty := canonical_ordinaryReaders_empty l p hl hM haxes initial target hgate upper hu hsu hut accepted
            exact (mem_holes _).mp (empty (Finset.mem_union_left _ hf)) (run.first_occupied hn)
          have hl1 := run.lane 1
          have hlN := run.lane ⟨n + 1, by omega⟩
          have hz := (Finset.mem_filter.mp hlast).2
          cases d with
          | east => exact Or.inl rfl
          | west => exact Or.inr rfl
          | north | south =>
            apply False.elim
            apply hfirst
            apply Finset.mem_filter.mpr
            refine ⟨Finset.mem_univ _, ?_, ?_, ?_⟩
            · exact (hl1.trans hlN.symm).trans hz.1
            · by_contra hnorth
              exact hfirstFrame ((Boundary.mem_frame _).mpr ⟨.north, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩)
            · by_contra hsouth
              have hbound := (run.cell 1).2.isLt
              exact hfirstFrame ((Boundary.mem_frame _).mpr ⟨.south, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩)
        have hbelow := upper_horizontal_input_below_cut l p hl hM haxes initial target hgate upper hu hsuSide
          hsu actualStep hvt accepted run hn hp boxes horizontal hlast
        exact Or.inr ⟨run.cell ⟨n + 1, by omega⟩, by change (p.D : ℤ) ≤ ((run.cell ⟨n + 1, by omega⟩).2.val : ℤ); omega,
          by rw [mask, mask]; exact imported_inter R _ _ boxes hfirst hlast⟩
      · exact Or.inl (balanced (by
          have hc : Inventory.count R v + 0 = Inventory.count R u + 0 := by simpa only [hfirst, hlast, ite_false] using hcount
          omega))

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
