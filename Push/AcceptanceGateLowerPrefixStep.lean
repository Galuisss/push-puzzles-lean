/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceColumnPrefix
public import Push.AcceptanceGateAxisNoInput
public import Push.AcceptanceMainCut
public import PushS.PortGateAxisTrains
import all Push.AcceptanceGateAxisNoInput
import all PushS.PortGatePrivateWalk
import all PushS.PortEndpointFStock
import all PushS.PortAxisNoExport
import all PushS.PortGatePageWindow
import all PushS.PortStreetSeparation
import all PushS.PortCoreCrossing
import all PushS.PortSegments

/-! Actual accepted lower gate-axis pushes preserve a box prefix followed by one terminal hole gap. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout PushS.RowLabels AcceptanceProgram AcceptanceColumnPrefix

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ []) {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate hi

private theorem lower_horizontal_first_impossible {u v t : State (p.W + 1) (p.H + 1)} {d : Direction} {n : ℕ}
    (hsu : Reachable (I).board none (I).initial u) (step : Step (I).board none u v)
    (hvt : Reachable (I).board none v t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (run : Run (w := p.W + 1) (h := p.H + 1) (I).board d u n) (hn : 0 < n)
    (hp : v.player = run.cell 1)
    (hb : v.boxes = insert (run.cell ⟨n + 1, by omega⟩) (u.boxes.erase (run.cell 1)))
    (hd : d = .east ∨ d = .west)
    (hf : run.cell 1 ∈ band (p.x middle) p.D (p.H - readDepth p 1)) : False := by
  let first : Cell (p.W + 1) (p.H + 1) := run.cell 1
  have hx : first.1.val = p.x middle := (Finset.mem_filter.mp hf).2.1
  have hy : p.D < first.2.val ∧ first.2.val < p.H - readDepth p 1 := (Finset.mem_filter.mp hf).2.2
  have hadj := players_adjacent (show Move (I).board none d u v from
    .push (hsu.valid (I).initial_valid) hn trivial run hp hb)
  rw [hp] at hadj
  change Adjacent d u.player first at hadj
  have hxeven := x_even p middle
  have supported := canonical_player_on_original l p hl hM haxes initial target hsu
    ((Relation.ReflTransGen.single step).trans hvt) accepted
  have hrow : first.2 ∈ l.workingRowSet p := by
    rcases supported with hc | hr
    · have he := l.streetColumnSet_even p hc
      rcases hd with rfl | rfl <;> simp only [Adjacent] at hadj <;> omega
    · rcases hd with rfl | rfl <;> exact hadj.2 ▸ hr
  rcases (l.workingRowSet_iff p first.2).mp hrow with hzero | hH | ⟨depth, hv, hrow | hrow⟩
  · omega
  · have hY := readDepth_ge p le_rfl p.levels_pos
    omega
  · have hmax := workingRows_le_last l p hv
    have hmargin := last_depth_margin p
    omega
  · have hdepth : readDepth p 1 < depth := by omega
    rcases l.workingDepthCoordinates_bands p le_rfl p.levels_pos hv with hshallow | hbranch | ⟨hlevels, hdeep⟩
    · omega
    · have hx0 := readLength_add_lt_x p middle 0
      have hxW := x_add_readLength_lt_W p ((gate_center_lt l hl hi).trans_le haxes) 0
      let left : Cell (p.W + 1) (p.H + 1) := (⟨p.x middle - 1, by omega⟩, first.2)
      have hblock := private_bottom l p hl hM haxes hi (q := left) (Or.inl rfl) (by
        change first.2.val = p.H - (readDepth p 1 + 2)
        omega)
      obtain ⟨i, he⟩ := horizontal_neighbor_hit run hn hd left rfl (by
        dsimp only [left]
        rw [hx]
        simp only [Nat.dist]
        omega)
      have avoid := canonical_gate_private_step_avoiding l p hl hM haxes initial target hgate hi hsu step hvt accepted
      exact avoid.2 d n run hn hp hb i (he.symm ▸ hblock)
    · have hmax := workingRows_le_last l p hv
      have hband : first ∈ axisDeepBand p .lower middle 1 := by
        refine ⟨by rw [hx, Nat.dist_self]; omega, ?_⟩
        simp only [reduceCtorEq, ite_false]
        omega
      exact (canonical_gate_deep_unvisited l p hl hM haxes initial target hgate hi hlevels hband
        (hsu.tail step) hvt accepted) hp

/-- The genuine accepted lower gate interval retains box-prefix order on every actual next step. -/
theorem canonical_gate_lower_prefix_step {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (step : Step (I).board none u v)
    (hvt : Reachable (I).board none v t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (closed : Closed (p.x middle) p.D (p.H - readDepth p 1) u) :
    Closed (p.x middle) p.D (p.H - readDepth p 1) v := by
  have hut := (Relation.ReflTransGen.single step).trans hvt
  have cutPlayer : ¬(u.player.1.val = p.x middle ∧ u.player.2.val = p.D) := by
    rintro ⟨hx, hy⟩
    exact canonical_main_central_unvisited l p hl hM haxes initial target (gate_center_lt l hl hi)
      hx (by rw [hy]; exact ⟨by omega, by omega⟩) hsu hut accepted rfl
  have frozen : Step (w := p.W + 1) (h := p.H + 1) (I).board none u v := step
  obtain ⟨d, move⟩ := frozen
  apply closed.move move cutPlayer
  · intro n run hn hp hb hd
    refine ⟨fun hf => lower_horizontal_first_impossible l p hl hM haxes initial target hgate hi hsu step hvt accepted run hn hp hb hd hf, ?_⟩
    intro hz
    obtain ⟨upper, hu, hs, hport⟩ := l.endpoints_upper_exists hl (gate_center_lt l hl hi)
    apply gate_axis_horizontal_impossible l p hl hM haxes initial target hgate hi upper hu hs hport
      hsu step hvt accepted run hn hp hb hd
    obtain ⟨_, hx, hlo, hhi⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx, by omega, hhi⟩
  · intro n run hn hp hb hz
    have hnoInput := (canonical_gateAxis_no_input l p hl hM haxes initial target hgate hi hsu step hvt accepted).2
      .north n run hn hp hb
    have hzR : run.cell ⟨n + 1, by omega⟩ ∈ gateAxis p middle := by
      obtain ⟨_, hx, hlo, hhi⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx, by omega, hhi⟩
    have hfR : run.cell 1 ∈ gateAxis p middle := by
      by_contra hn
      exact (Finset.mem_compl.mp (hnoInput (Finset.mem_compl.mpr hn))) hzR
    have hfirst := (Finset.mem_filter.mp hfR).2
    have hlast := (Finset.mem_filter.mp hz).2
    have hp1 := run.position 1
    have hpN := run.position ⟨n + 1, by omega⟩
    simp only [Direction.position, Fin.val_one] at hp1 hpN
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfirst.1, by omega, hfirst.2.2⟩

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
