/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.ForwardWalking

/-! A maximum slide with the player's complete approach and return walks. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Layout

open PushFS (Cell State Direction Adjacent)

private theorem walk_corner_insert (L : Layout) (fixed : Finset (Cell L.width L.height))
    (signal p : Cell L.width L.height)
    (hcolumns : ∀ q ∈ fixed, q.1.val ∈ L.columns)
    (htop : ∀ q : Cell L.width L.height, q.2.val = 0 → q ∉ fixed)
    (hcolumn : signal.1.val ∈ L.columns) (hy : 0 < signal.2.val)
    (hp : p ∉ insert signal fixed) :
    Finite.Reachable 1 (⟨p, insert signal fixed⟩ : State L.width L.height)
        ⟨L.corner, insert signal fixed⟩ ∧
      Finite.Reachable 1 (⟨L.corner, insert signal fixed⟩ : State L.width L.height)
        ⟨p, insert signal fixed⟩ := by
  apply L.walk_corner (insert signal fixed) _ _ p hp
  · intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hcolumn
    · exact hcolumns q hq
  · intro q hq hmem
    rcases Finset.mem_insert.mp hmem with rfl | hmem
    · omega
    · exact htop q hq hmem

/-- Execute one isolated maximum slide and restore the exact player corner. -/
theorem slide_from_corner (L : Layout) (fixed : Finset (Cell L.width L.height))
    (d : Direction) (source dest stop support : Cell L.width L.height)
    (hcolumns : ∀ p ∈ fixed, p.1.val ∈ L.columns)
    (htop : ∀ p : Cell L.width L.height, p.2.val = 0 → p ∉ fixed)
    (hsourcecol : source.1.val ∈ L.columns) (hdestcol : dest.1.val ∈ L.columns)
    (hsourcey : 0 < source.2.val) (hdesty : 0 < dest.2.val)
    (hsource : source ∉ fixed) (hsupport : support ∉ insert source fixed)
    (hfirst : Adjacent d support source) (hlane : d.lane dest = d.lane source)
    (hforward : d.position source < d.position dest)
    (hclear : ∀ p : Cell L.width L.height, d.lane p = d.lane source →
      d.position source < d.position p → d.position p ≤ d.position dest → p ∉ fixed)
    (hstop : Adjacent d dest stop) (hstop_mem : stop ∈ fixed) :
    Finite.Reachable 1 (⟨L.corner, insert source fixed⟩ : State L.width L.height)
      ⟨L.corner, insert dest fixed⟩ := by
  have hin := (walk_corner_insert L fixed source support hcolumns htop
    hsourcecol hsourcey hsupport).2
  have hclear_source : ∀ p : Cell L.width L.height, d.lane p = d.lane source →
      d.position source < d.position p → d.position p ≤ d.position dest →
      p ∉ insert source fixed := by
    intro p hl hlo hhi hmem
    rcases Finset.mem_insert.mp hmem with rfl | hmem
    · exact (lt_irrefl _) hlo
    · exact hclear p hl hlo hhi hmem
  have hm := Doors.push_single_finite d
    (⟨support, insert source fixed⟩ : State L.width L.height) source dest stop
    hsupport (Finset.mem_insert_self _ _) hfirst hlane hforward hclear_source
    hstop (Finset.mem_insert_of_mem hstop_mem)
  rw [Finset.erase_insert hsource] at hm
  have hout := (walk_corner_insert L fixed dest source hcolumns htop
    hdestcol hdesty hm.valid_target).1
  exact hin.trans ((Relation.ReflTransGen.single ⟨d, hm⟩).trans hout)

end PushPuzzle.PushPush.Doors.Layout
