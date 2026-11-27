/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessProbeFixedSource
public import Push.AcceptanceSoundnessUpperAxisNoInput
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceProgramLayout
import all PushS.PortStreetSeparation
import all PushS.PortSegments

/-! Once non-main probe holes retain their source stock, no horizontal accepted push can meet a probe row. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate

/-- A real horizontal push ending on a probe row has either forbidden main-axis input or a permanently empty destination. -/
theorem canonical_probe_horizontal_impossible_of_source
    {u v t : State (p.W + 1) (p.H + 1)} {d : Direction} {n : ℕ}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (run : Run (I).board d u n) (hn : 0 < n) (hp : v.player = run.cell 1)
    (hb : v.boxes = insert (run.cell ⟨n + 1, by omega⟩) (u.boxes.erase (run.cell 1)))
    (hd : d = .east ∨ d = .west)
    (hrow : (run.cell ⟨n + 1, by omega⟩).2.val ∈ probeRows l p)
    (hsource : ∀ q : Cell (p.W + 1) (p.H + 1), q.2.val ∈ probeRows l p →
      q.1 ∉ l.mainColumnSet p → q ∈ PushS.holes u → q ∈ PushS.holes (I).initial) : False := by
  let z : Cell (p.W + 1) (p.H + 1) := run.cell ⟨n + 1, by omega⟩
  have hzV : z ∈ v.boxes := by rw [hb]; exact Finset.mem_insert_self _ _
  by_cases hmain : z.1 ∈ l.mainColumnSet p
  · rcases (l.mainColumnSet_iff p z.1).mp hmain with h0 | hW | ⟨i, hi, hix⟩
    · exact Finset.disjoint_left.mp (canonical_frame_empty_at l p hl hM haxes initial target hvt ha) hzV
        ((Boundary.mem_frame z).mpr ⟨.west, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩⟩)
    · exact Finset.disjoint_left.mp (canonical_frame_empty_at l p hl hM haxes initial target hvt ha) hzV
        ((Boundary.mem_frame z).mpr ⟨.east, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩)
    · obtain ⟨e, he, hs, hep⟩ := l.endpoints_upper_exists hl hi
      obtain ⟨ref, href, hy⟩ := List.mem_map.mp (List.mem_toFinset.mp hrow)
      obtain ⟨href, _⟩ := List.mem_filter.mp href
      obtain ⟨hj, hjm⟩ := l.endpoints_level_bounds p hl hM href
      have hv : readDepth p ref.level + 2 ∈ l.workingDepthCoordinates p := by
        have hv := (l.workingDepthCoordinates_mem p (ref.level - 1) (by omega)).2
        simpa only [Nat.sub_add_cancel hj] using hv
      apply canonical_upper_axis_no_horizontal_input l p hl hM haxes initial target hgate e he hs
        hsu hm hvt ha run hn hp hb hd hv
      · change z.1.val = p.x e.port
        rw [hep]
        exact hix
      · rw [readDepth_eq p hj hjm]
        exact hy.symm
  · have hz0 := hsource z hrow hmain ((PushS.mem_holes _).mpr run.empty)
    have hzE := canonical_upper_probe_source_empty l p hl hM haxes initial target hgate (hsu.tail hm) hvt ha hz0 hrow hmain
    exact (PushS.mem_holes _).mp hzE hzV

omit hgate

/-- The odd predecessor of a real vertical probe endpoint forces its column to be on the upper page. -/
theorem canonical_vertical_probe_page_column
    {u v t : State (p.W + 1) (p.H + 1)} {d : Direction} {n : ℕ}
    (hsu : Reachable (I).board none (I).initial u)
    (hvt : Reachable (I).board none v t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (run : Run (I).board d u n) (hn : 0 < n) (hp : v.player = run.cell 1)
    (hb : v.boxes = insert (run.cell ⟨n + 1, by omega⟩) (u.boxes.erase (run.cell 1)))
    (hd : d = .north ∨ d = .south) (i : Fin (n + 1))
    (hrow : (run.cell i.succ).2.val ∈ probeRows l p) :
    (run.cell i.succ).1 ∈ l.pageColumnSet p .upper := by
  let q := run.cell i.succ
  let r := run.cell i.castSucc
  obtain ⟨ref, href, hy⟩ := List.mem_map.mp (List.mem_toFinset.mp hrow)
  obtain ⟨href, _⟩ := List.mem_filter.mp href
  obtain ⟨hj, hjm⟩ := l.endpoints_level_bounds p hl hM href
  have hD := readDepth_add_lt_D p ref.level
  rw [readDepth_eq p hj hjm] at hD
  have heven : q.2.val % 2 = 0 := by
    have hY : p.Y ref.level % 2 = 0 := by simp [Scales.Parameters.Y, Scales.Parameters.A, Scales.Parameters.Q, Nat.mul_mod]
    change p.Y ref.level + 2 = q.2.val at hy
    omega
  have hadj := run.adjacent i
  change Adjacent d r q at hadj
  have hpage : r.2.val < p.D := by
    change p.Y ref.level + 2 = q.2.val at hy
    rcases hd with rfl | rfl <;> simp only [Adjacent] at hadj <;> omega
  have hsupp := canonical_push_run_on_pages l p hl hM haxes initial target hsu run hn hp hb hvt ha i.castSucc
  rcases (l.page_support_iff_side p hl .upper r hpage).mp hsupp with hwork | hcol
  · have hodd := l.workingRowSet_even p hwork
    rcases hd with rfl | rfl <;> simp only [Adjacent] at hadj <;> omega
  · rcases hd with rfl | rfl <;> exact hadj.1 ▸ hcol

end Canonical
end PushPuzzle.Push.AcceptanceSoundness
