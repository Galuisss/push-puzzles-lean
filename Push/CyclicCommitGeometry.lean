/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicCommitSource
public import Push.CyclicNorthwest
public import Push.ReflectedFrontier
public import Push.SealedDoor
import all Push.CornerDockReverse

/-! The same physical cyclic commitment permanently excludes every later original-source visit. -/

@[expose] public section
namespace PushPuzzle.Push.Cyclic

open PushFS PushS

private theorem embed_initial_box (r : ColumnScan.Input)
    (q : Cell (wideReader r).outputWidth (wideReader r).outputHeight) :
    (dock r).embed q ∈ (dock r).compile.initial.boxes ↔ q ∈ (wideReader r).compile.initial.boxes := by
  change (dock r).embed q ∈ ((dock r).extend (dock r).initial).emptyᶜ ↔ q ∈ (wideReader r).emptyᶜ
  simp only [Finset.mem_compl]
  exact not_congr ((dock r).embed_mem_extend (dock r).initial q)

private def readerPoint (r : ColumnScan.Input) (q : Cell (dock r).outputWidth (dock r).outputHeight)
    (hx : 2 ≤ q.1.val) (hy : q.2.val < (wideReader r).outputHeight) :
    Cell (wideReader r).outputWidth (wideReader r).outputHeight :=
  (⟨q.1.val - 2, by
    have hq : q.1.val < (wideReader r).outputWidth + 2 := q.1.isLt
    omega⟩, ⟨q.2.val, hy⟩)

private theorem readerPoint_embed (r : ColumnScan.Input)
    (q : Cell (dock r).outputWidth (dock r).outputHeight)
    (hx : 2 ≤ q.1.val) (hy : q.2.val < (wideReader r).outputHeight) :
    (dock r).embed (readerPoint r q hx hy) = q := by
  apply Prod.ext <;> apply Fin.ext
  · change q.1.val - 2 + 2 = q.1.val
    omega
  · rfl

private theorem east_initial_full (r : ColumnScan.Input)
    (q : Cell (dock r).outputWidth (dock r).outputHeight)
    (hx : r.width + 2 < q.1.val) (hy : q.2.val < r.height) : q ∈ (dock r).compile.initial.boxes := by
  have hhy : q.2.val < (wideReader r).outputHeight := by
    change q.2.val < r.height + (wideReader r).length
    omega
  rw [← readerPoint_embed r q (by omega) hhy]
  apply (embed_initial_box r _).mpr
  apply (wideReader r).east_full_on_source_rows
  · change r.width < q.1.val - 2
    omega
  · exact hy

private theorem northeast_initial_full (r : ColumnScan.Input)
    (q : Cell (dock r).outputWidth (dock r).outputHeight)
    (hx : r.width + 2 ≤ q.1.val) (hy : q.2.val + 1 < r.height) : q ∈ (dock r).compile.initial.boxes := by
  have hhy : q.2.val < (wideReader r).outputHeight := by
    change q.2.val < r.height + (wideReader r).length
    omega
  rw [← readerPoint_embed r q (by omega) hhy]
  apply (embed_initial_box r _).mpr
  apply (wideReader r).northeast_full_initial
  · change r.width ≤ q.1.val - 2
    omega
  · exact hy

/-- Every old source-row cell strictly east of the shifted source boundary stays occupied. -/
private theorem east_full (r : ColumnScan.Input) {t : State (dock r).outputWidth
    (dock r).outputHeight}
    (hr : Reachable (dock r).compile.board none (dock r).compile.initial t)
    (q : Cell (dock r).outputWidth (dock r).outputHeight)
    (hx : r.width + 2 < q.1.val) (hy : q.2.val < r.height) : q ∈ t.boxes := by
  apply Support.northeast_full (r.width + 3) (r.height - 1) hr ?_ q (by omega) (by omega)
  intro p hpx hpy
  exact east_initial_full r p (by omega) (by have := r.height_pos; omega)

/-- The shifted northeast source corner remains solid along the whole dock trajectory. -/
private theorem northeast_full (r : ColumnScan.Input) {t : State (dock r).outputWidth
    (dock r).outputHeight}
    (hr : Reachable (dock r).compile.board none (dock r).compile.initial t)
    (q : Cell (dock r).outputWidth (dock r).outputHeight)
    (hx : r.width + 2 ≤ q.1.val) (hy : q.2.val + 1 < r.height) : q ∈ t.boxes := by
  apply Support.northeast_full (r.width + 2) (r.height - 2) hr ?_ q hx (by omega)
  intro p hpx hpy
  exact northeast_initial_full r p hpx (by omega)

/-- New dock rows contain holes only in the added western columns, throughout every real trajectory. -/
theorem dock_source_support (r : ColumnScan.Input)
    {t : State (dock r).outputWidth (dock r).outputHeight}
    (hr : Reachable (dock r).compile.board none (dock r).compile.initial t)
    (q : Cell (dock r).outputWidth (dock r).outputHeight) (hq : q ∈ holes t) :
    q.1.val < 2 ∨ q.2.val < (wideReader r).outputHeight :=
  (dock r).hole_support hr q hq

namespace Commit

variable {r : ColumnScan.Input} {finish : State (dock r).outputWidth (dock r).outputHeight}
  (c : Commit r finish)

theorem before_real : Reachable (dock r).compile.board none (dock r).compile.initial c.state :=
  Relation.ReflTransGen.mono (fun _ _ hm => hm.1) _ _ c.before

/-- Once the original source door is filled at this commitment, it stays filled on every suffix. -/
private theorem door_full {t : State (dock r).outputWidth (dock r).outputHeight}
    (hr : Reachable (dock r).compile.board none c.state t) :
    (dock r).embed (wideReader r).door ∈ t.boxes := by
  induction hr with
  | refl => exact c.door_occupied
  | @tail u v hsu hm ih =>
    apply SealedDoor.move_full _ rfl ?_ (east_full r (c.before_real.trans hsu))
      (northeast_full r (c.before_real.trans hsu)) hm.choose_spec ih
    change r.height - 1 + 1 = r.height
    have := r.height_pos
    omega

private theorem left_holes_lower (q : Cell (dock r).outputWidth (dock r).outputHeight)
    (hq : q ∈ holes c.state) (hx : q.1.val < 2) : r.targetLevel ≤ q.2.val := by
  by_contra hy
  have hlt : q.2.val < (wideReader r).targetLevel := by change q.2.val < r.targetLevel; omega
  exact (mem_holes _).mp hq (dock_northwest_full r c.before_real q hx hlt)

/-- The real western strip has exactly the original source rows and its separated southern buffer. -/
private theorem buffer_split (q : Cell (dock r).outputWidth (dock r).outputHeight)
    (hq : q ∈ holes c.state) (hx : q.1.val < r.width + 2) :
    q.2.val < r.height ∨ r.targetLevel ≤ q.2.val := by
  by_cases hleft : q.1.val < 2
  · exact Or.inr (c.left_holes_lower q hq hleft)
  by_cases hy : q.2.val < r.height
  · exact Or.inl hy
  · right
    have hs := dock_source_support r c.before_real q hq
    have hhy : q.2.val < (wideReader r).outputHeight := by
      change q.1.val < 2 ∨ q.2.val < (wideReader r).outputHeight at hs
      omega
    let a := readerPoint r q (by omega) hhy
    have ha : a ∈ holes (readerState r c.state) := by
      apply ((dock r).sourceState_hole c.state a).mpr
      rw [readerPoint_embed]
      exact hq
    have hfx := congrArg (fun q => q.1.val) c.readerGoal
    have hfy := congrArg (fun q => q.2.val) c.readerGoal
    obtain ⟨i, hi⟩ := ((wideReader r).before_south_exact c.readerBefore c.readerSuffix hfx hfy.ge
      (show a.1.val < (wideReader r).width by change q.1.val - 2 < r.width; omega)
      (show (wideReader r).height ≤ a.2.val by change r.height ≤ q.2.val; omega)).mp ha
    have hlev := (wideReader r).targetLevel_le_needleLevel i
    have hyi := congrArg (fun q => q.2.val) hi
    change (wideReader r).needleLevel i = q.2.val at hyi
    exact hlev.trans_eq hyi

private theorem source_mask :
    (holes c.sourceState).image (unturnedSourceEmbed r) =
      ReflectedFrontier.source (r.width + 2) r.height c.state := by
  ext q
  constructor
  · intro hq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_filter.mpr ⟨(c.source_hole a).mp ha,
      by change a.1.val + 2 < r.width + 2; have := a.1.isLt; omega, a.2.isLt⟩
  · intro hq
    obtain ⟨hq, hx, hy⟩ := Finset.mem_filter.mp hq
    have hleft : 2 ≤ q.1.val := by
      by_contra hh
      have hlev := c.left_holes_lower q hq (by omega)
      have := r.targetLevel_lower
      omega
    let a : Cell r.width r.height := (⟨q.1.val - 2, by omega⟩, ⟨q.2.val, hy⟩)
    have he : unturnedSourceEmbed r a = q := by
      apply Prod.ext <;> apply Fin.ext
      · change q.1.val - 2 + 2 = q.1.val
        omega
      · rfl
    refine Finset.mem_image.mpr ⟨a, (c.source_hole a).mpr ?_, he⟩
    rwa [he]

/-- The complete dock's actual source-row inventory equals the original source hole budget. -/
private theorem source_card :
    (ReflectedFrontier.source (r.width + 2) r.height c.state).card = r.sourceHoles := by
  have hinj : Function.Injective (unturnedSourceEmbed r) := fun _ _ he =>
    (wideReader r).embed_injective ((dock r).embed_injective he)
  rw [← c.source_mask, Finset.card_image_of_injective _ hinj]
  exact c.source_holes_card

/-- The entire east side of every original source row remains filled after commitment. -/
theorem right_full {t : State (dock r).outputWidth (dock r).outputHeight}
    (hr : Reachable (dock r).compile.board none c.state t)
    (q : Cell (dock r).outputWidth (dock r).outputHeight)
    (hx : r.width + 2 ≤ q.1.val) (hy : q.2.val < r.height) : q ∈ t.boxes := by
  by_cases he : r.width + 2 < q.1.val
  · exact east_full r (c.before_real.trans hr) q he hy
  by_cases hn : q.2.val + 1 < r.height
  · exact northeast_full r (c.before_real.trans hr) q hx hn
  have hq : q = (dock r).embed (wideReader r).door := by
    apply Prod.ext <;> apply Fin.ext
    · change q.1.val = r.width + 2
      omega
    · change q.2.val = r.height - 1
      omega
  exact hq ▸ c.door_full hr

/-- No suffix of the actual dock trace can revisit the original source rows from its western strip. -/
theorem no_return {t : State (dock r).outputWidth (dock r).outputHeight}
    (hr : Reachable (dock r).compile.board none c.state t) :
    t.player.1.val < r.width + 2 → r.height ≤ t.player.2.val := by
  have hh : r.height ≤ (dock r).outputHeight := by
    change r.height ≤ (wideReader r).outputHeight + (dock r).distance
    change r.height ≤ r.height + (wideReader r).length + (dock r).distance
    omega
  have hl : r.targetLevel < (dock r).outputHeight := by
    have hreader := ((wideReader r).targetLevel_le_needleLevel ⟨0, r.width_pos⟩).trans_lt
      ((wideReader r).needleLevel_lt_height _)
    have hreader' : r.targetLevel < (wideReader r).outputHeight := hreader
    change r.targetLevel < (wideReader r).outputHeight + (dock r).distance
    omega
  apply ReflectedFrontier.no_source_return (w := (dock r).outputWidth) (h := (dock r).outputHeight)
    hh hl (c.before_real.valid (dock r).compile.initial_valid)
    c.buffer_split ?_ ?_ ?_ hr
  · intro hx
    have hp := congrArg (fun q => q.1.val) c.player
    change c.state.player.1.val = r.width + 2 at hp
    omega
  · rw [c.source_card]
    exact (Nat.add_le_add_left (Nat.le_max_left r.sourceHoles r.width) _).trans_lt r.targetLevel_lower
  · intro u hu q hx hy
    exact c.right_full hu q hx.ge hy

end Commit
end PushPuzzle.Push.Cyclic
