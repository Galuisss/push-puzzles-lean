/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGatePrivateWalk
import all PushS.PortGatePrivateWalk
import all PushS.PortGatePageWindow
import all PushS.PortGateTails
import all PushS.PortEndpointSeparation
import all PushS.PortSegments

/-! The two genuine player entrances to the actual five-cell private gate branch. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS

/-- The private cap and its four-cell horizontal branch, without the public frame. -/
@[expose] def gatePrivateCells (p : Scales.Parameters) (middle : ℕ) : Finset (Cell (p.W + 1) (p.H + 1)) :=
  Finset.univ.filter fun q =>
    (q.1.val = p.x middle + 4 ∧ q.2.val = p.H - (readDepth p 1 + 1)) ∨
      (q.2.val = p.H - (readDepth p 1 + 2) ∧ p.x middle + 1 ≤ q.1.val ∧ q.1.val ≤ p.x middle + 4)

private theorem mem_private_cells (p : Scales.Parameters) (middle : ℕ) (q : Cell (p.W + 1) (p.H + 1)) :
    q ∈ gatePrivateCells p middle ↔ PrivatePosition p middle (q.1.val, q.2.val) := by
  simp only [gatePrivateCells, PrivatePosition, Finset.mem_filter, Finset.mem_univ, true_and]

/-- On an actual gate, these five cells are precisely the established private walk with its frame removed. -/
theorem gatePrivateCells_eq_walk_sdiff (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (ha : l.portCount ≤ p.axes) {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates) :
    gatePrivateCells p middle = gatePrivateWalk p middle \ Boundary.frame := by
  ext q
  rw [mem_private_cells, Finset.mem_sdiff, mem_gatePrivateWalk]
  have hfar : PrivatePosition p middle (q.1.val, q.2.val) → q ∉ Boundary.frame := by
    intro hp hf
    have hx0 := readLength_add_lt_x p middle 0
    have hxW := x_add_readLength_lt_W p ((gate_center_lt l hl hi).trans_le ha) 0
    have hY := readDepth_ge p (show 1 ≤ 1 by omega) p.levels_pos
    have hH := readDepth_add_lt_H p 1
    obtain ⟨d, hd⟩ := (Boundary.mem_frame q).mp hf
    cases d <;> simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and] at hd <;>
      simp only [PrivatePosition] at hp <;> omega
  exact ⟨fun hp => ⟨Or.inr hp, hfar hp⟩, fun ⟨hp, hf⟩ => hp.resolve_left hf⟩

private theorem outside_neighbor (p : Scales.Parameters) (middle : ℕ) {d : Direction}
    {q r : Cell (p.W + 1) (p.H + 1)} (hadj : Adjacent d q r)
    (hout : q ∉ gatePrivateCells p middle) (hin : r ∈ gatePrivateCells p middle) :
    ((q.1.val = p.x middle + 4 ∧ q.2.val = p.H - readDepth p 1) ∨
      (q.1.val = p.x middle ∧ q.2.val = p.H - (readDepth p 1 + 2))) ∨
    ((p.x middle < q.1.val ∧ q.1.val < p.x middle + 6) ∧ q.1.val ≠ p.x middle + 4 ∧
      (q.2.val = p.H - (readDepth p 1 + 1) ∨ q.2.val = p.H - (readDepth p 1 + 3))) ∨
    (q.1.val = p.x middle + 4 ∧ q.2.val = p.H - (readDepth p 1 + 3)) ∨
      (q.1.val = p.x middle + 5 ∧ q.2.val = p.H - (readDepth p 1 + 2)) := by
  have hH := readDepth_add_lt_H p 1
  simp only [gatePrivateCells, Finset.mem_filter, Finset.mem_univ, true_and] at hout hin
  cases d <;> simp only [Adjacent] at hadj <;> omega

private theorem avoiding_box {w h : ℕ} {B : Board w h} {cap : Option ℕ} {G : Finset (Cell w h)}
    {s t : State w h} (hr : Relation.ReflTransGen (Freeze.AvoidingStep B cap G) s t)
    {q : Cell w h} (hq : q ∈ G) (hb : q ∈ s.boxes) : q ∈ t.boxes := by
  induction hr with
  | refl => exact hb
  | @tail u v _ hm ih =>
    obtain ⟨d, hmove⟩ := hm.1
    cases hmove with
    | walk _ _ _ _ hboxes => simpa only [hboxes] using ih
    | @push n _ hn _ run hp hboxes =>
      rw [hboxes]
      exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨fun heq => hm.2 d n run hn hp hboxes 1 (heq ▸ hq), ih⟩)

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)
  {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)

local notation "I" => l.physicalInstance p hl hM ha initial target

include hi

private theorem boundary_initial_box {q : Cell (p.W + 1) (p.H + 1)}
    (hx : p.x middle < q.1.val ∧ q.1.val ≤ p.x middle + 5)
    (hy : p.H - (readDepth p 1 + 3) ≤ q.2.val ∧ q.2.val ≤ p.H - (readDepth p 1 + 1))
    (hout : q ∉ gatePrivateCells p middle) : q ∈ (I).initial.boxes := by
  have hY := readDepth_ge p (show 1 ≤ 1 by omega) p.levels_pos
  have hD := readDepth_add_lt_D p 1
  have hH : p.H = 2 * p.D := rfl
  have hw : q ∈ gatePageWindow p middle := by
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    simp only [Nat.dist]
    omega
  have hout' : ¬PrivatePosition p middle (q.1.val, q.2.val) := fun h => hout ((mem_private_cells p middle q).mpr h)
  by_contra hb
  have hh := (mem_holes q).mpr hb
  change q ∈ (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p initial))ᶜᶜ at hh
  rw [compl_compl] at hh
  cases l.encodedSegments_gatePageWindow p hl hM ha initial hi hw hh with
  | fixed hs =>
    cases gateFixedSegments_location p middle hs with
    | publicStreet _ hr => omega
    | privateCap hc hr => exact hout' (Or.inl ⟨hc, hr⟩)
    | privateBranch hr hc => exact hout' (Or.inr ⟨hr, hc⟩)
    | halfDepth hr => omega
    | marker hlevels _ hr =>
      have hgap := readDepth_interlevel_margin p (show 1 ≤ 1 by omega) hlevels
      simp only [Nat.reduceAdd] at hgap
      omega
  | @signal kind first internal _ hcenter hs =>
    cases gateSegments_location p initial kind first internal hs with
    | horizontal hr => omega
    | axis hc _ => simp only [hcenter] at hc; omega

/-- A real successful player step entering the five private cells comes from work-row four or the adjacent axis hole. -/
theorem physicalInstance_gate_private_entry {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals)
    (hout : u.player ∉ gatePrivateCells p middle) (hin : v.player ∈ gatePrivateCells p middle) :
    (u.player.1.val = p.x middle + 4 ∧ u.player.2.val = p.H - readDepth p 1) ∨
      (u.player.1.val = p.x middle ∧ u.player.2.val = p.H - (readDepth p 1 + 2)) := by
  have hadj := players_adjacent hm.choose_spec
  have hpaths := l.physicalInstance_gate_private_avoiding_prefix p hl hM ha initial target hi hsu
    ((Relation.ReflTransGen.single hm).trans hvt) ht
  have blocked (hmem : u.player ∈ l.gatePrivateBlockers p hl hM ha hi)
      (hx : p.x middle < u.player.1.val ∧ u.player.1.val ≤ p.x middle + 5)
      (hy : p.H - (readDepth p 1 + 3) ≤ u.player.2.val ∧ u.player.2.val ≤ p.H - (readDepth p 1 + 1)) : False :=
    hm.choose_spec.valid_source.2.2 (avoiding_box hpaths hmem (boundary_initial_box l p hl hM ha initial target hi hx hy hout))
  rcases outside_neighbor p middle hadj hout hin with hentry | ⟨hx, hfour, hy⟩ | ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact hentry
  · have hguard : u.player ∈ l.gatePrivateBlockers p hl hM ha hi := by
      rcases hy with hy | hy
      · exact private_near_background l p hl hM ha hi hx hfour (Or.inl rfl) hy
      · exact private_near_background l p hl hM ha hi hx hfour (Or.inr rfl) hy
    exact False.elim (blocked hguard ⟨hx.1, by omega⟩ (by rcases hy with h | h <;> omega))
  · exact False.elim (blocked (private_deep l p hl hM ha hi hx hy) (by omega) (by omega))
  · exact False.elim (blocked (private_bottom l p hl hM ha hi (Or.inr hx) hy) (by omega) (by omega))

end Solution
end PushPuzzle.PushS.PortLayout
