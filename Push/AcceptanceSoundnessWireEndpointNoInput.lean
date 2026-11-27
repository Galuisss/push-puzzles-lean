/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import Push.AcceptanceSoundnessUpperAxisNoInput
public import Push.AcceptanceGateWalks
public import PushS.PortUpperAxisNoInput
import all PushS.PortUpperAxisNoInput
public import PushS.PortAxisBlockers
public import PushS.PortDepthBands
public import PushS.PortColumnRadius
public import PushS.PortGatePublicWalk
import all PushS.PortWireIndexing
import all PushS.PortEndpointIndexing
import all PushS.PortOrdinaryAxis
import all PushS.PortEndpointReaderWalk
import all PushS.PortEndpointBranch
import all PushS.PortEndpointCounts
import all PushS.PortEndpointPageWindow
import all PushS.PortPublicWalkBudget
import all PushS.PortAxisClear
import all PushS.PortCentralStrip
import all PushS.PortSegments

/-! A balanced ordinary WIRE blocks horizontal axis input at either page endpoint. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness


open PushFS PushFS.Reduction PushS PushS.PortLayout SegmentRecipe AcceptanceProgram

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate

/-- A successful horizontal push cannot fill a selected main-axis cell of an actual ordinary WIRE endpoint. -/
theorem canonical_wire_endpoint_no_horizontal_input {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    (e : Endpoint) (he : e ∈ l.endpoints) (heq : e = wireWorkLeft g ∨ e = wireWorkRight g) {u v t : State (p.W + 1) (p.H + 1)} {d : Direction} {n depth : ℕ}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (run : Run (I).board d u n) (hn : 0 < n) (hp : v.player = run.cell 1)
    (hb : v.boxes = insert (run.cell ⟨n + 1, by omega⟩) (u.boxes.erase (run.cell 1)))
    (hd : d = .east ∨ d = .west) (hv : depth ∈ l.workingDepthCoordinates p)
    (hx : (run.cell ⟨n + 1, by omega⟩).1.val = p.x e.port)
    (hy : (run.cell ⟨n + 1, by omega⟩).2.val = if e.side = .upper then depth else p.H - depth) : False := by
  let q : Cell (p.W + 1) (p.H + 1) := run.cell ⟨n, by omega⟩
  let z : Cell (p.W + 1) (p.H + 1) := run.cell ⟨n + 1, by omega⟩
  change z.1.val = _ at hx
  change z.2.val = (if e.side = .upper then depth else p.H - depth) at hy
  have hadj := run.adjacent ⟨n, by omega⟩
  change Adjacent d q z at hadj
  have hqy : q.2.val = (if e.side = .upper then depth else p.H - depth) := by rcases hd with rfl | rfl <;> exact (congrArg Fin.val hadj.2).symm.trans hy
  have hqx : q.1.val = (if e.inward then p.x e.port - 1 else p.x e.port + 1) ∨
      q.1.val = (if e.inward then p.x e.port + 1 else p.x e.port - 1) := by
    rcases hd with rfl | rfl <;> cases hi : e.inward <;>
      simp only [Adjacent] at hadj <;> simp only [Bool.false_eq_true, ite_true, ite_false] <;> omega
  have havoid := canonical_ordinary_reader_step_avoiding l p hl hM haxes initial target hgate e he hsu hm hvt ha
  rcases l.workingDepthCoordinates_bands p (l.endpoints_level_bounds p hl hM he).1
      (l.endpoints_level_bounds p hl hM he).2 hv with hshallow | hbranch | ⟨heM, hdeep⟩
  · by_cases hown : depth = readDepth p e.level
    · rcases heq with rfl | rfl
      all_goals
        have hgy : (run.cell ⟨n + 1, by omega⟩).2.val =
            (if g.side = .upper then readDepth p g.level else p.H - readDepth p g.level) := by
          simpa only [wireWorkLeft, wireWorkRight, hown] using hy
        apply canonical_wire_axis_destination_impossible l p hl hM haxes initial target hgate hg hw hsu hm hvt ha run hn hp hb hd hgy
        first | exact Or.inl hx | exact Or.inr hx
    · rcases hqx with hout | hin
      · exact havoid.2 d n run hn hp hb ⟨n, by omega⟩
          (l.endpointOrdinaryBlockers_front_mem p hl hM haxes e he hv hshallow hout hqy)
      · have hreader := canonical_ordinaryReaders_empty l p hl hM haxes initial target hgate e he hsu
          ((Relation.ReflTransGen.single hm).trans hvt) ha
        have hshort : q ∈ l.endpointShortBranches p e := (mem_endpointShortBranches l p e q).mpr
          ⟨hin, depth, hv, by omega, hqy⟩
        exact (mem_holes q).mp (hreader (Finset.mem_union_right _ (Finset.mem_union_right _ hshort)))
          (run.occupied_at ⟨n, by omega⟩ hn le_rfl)
  · rcases hqx with hout | hin
    · have hqbranch : q ∈ endpointLongBranch p e := by
        apply (mem_endpointLongBranch p e q).mpr
        refine ⟨by simpa only [hbranch] using hqy, ?_⟩
        have hlen := readLength_ge p (l.endpoints_level_bounds p hl hM he).1 (l.endpoints_level_bounds p hl hM he).2
        have hx0 := readLength_add_lt_x p e.port e.level
        cases hi : e.inward <;> simp only [hi, Bool.false_eq_true, ite_true, ite_false, EndpointStreet.column_f] at hout ⊢ <;> omega
      have hpublic := (canonical_publicWalkInvariant l p hl hM haxes initial target hgate ha) _ hsu
        ((Relation.ReflTransGen.single hm).trans hvt)
      exact (mem_holes q).mp (hpublic (branch_subset_public l p hl hM e he hqbranch))
        (run.occupied_at ⟨n, by omega⟩ hn le_rfl)
    · exact havoid.2 d n run hn hp hb ⟨n, by omega⟩
        (l.endpointOrdinaryBlockers_branch_mem p hl hM haxes e he hin
          (by simpa only [hbranch] using hqy))
  · have hmax := workingRows_le_last l p hv
    have hband : z ∈ axisDeepBand p e.side e.port e.level := by
      refine ⟨?_, ?_⟩
      · rw [hx, Nat.dist_self]
        omega
      · have hH : p.H = 2 * p.D := rfl
        have hY := readDepth_add_lt_D p e.level
        have hDepth := readDepth_add_lt_D p depth
        cases hs : e.side <;> simp only [hs, ite_true, reduceCtorEq, ite_false] at hy ⊢ <;> omega
    have hgap := readDepth_interlevel_margin p (l.endpoints_level_bounds p hl hM he).1 heM
    have hfull := endpoint_axis_deep_initial_full l p hl hM haxes (l.canonical initial) (l.canonical target) e he hv (by omega) hx
      hy
    exact run.empty (canonical_endpoint_deep_occupied l p hl hM haxes initial target hgate e he heM hband hfull hsu
      ((Relation.ReflTransGen.single hm).trans hvt) ha)

end Solution
end PushPuzzle.Push.AcceptanceSoundness
