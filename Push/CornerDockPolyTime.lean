/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CornerDock
public import Push.Space.Goal
public import PushFS.BitmapIsometry

/-! Polynomial-time literal southwest-dock emission from the original dense source game. -/

@[expose] public section
namespace PushPuzzle.Push.CornerDock

open PushFS PushS Turing.MultiTapeTM
open scoped PushFS.Encoding

/-- The original dense source board and its left-boundary target row. -/
structure Data where
  source : PushFS.Encoding.Data
  goalY : ℕ

/-- Dense original source data followed by its unary left-goal row. -/
enc_structure encData : Data where
  source : PushFS.Encoding.encData, goalY : encUnary

namespace Input

theorem source_injective : Function.Injective source := by
  rintro ⟨w, h, ⟨p, E, hp⟩, g⟩ ⟨w', h', ⟨p', E', hp'⟩, g'⟩ heq
  have hw : w = w' := congrArg Push.Instance.width heq
  cases hw
  have hh : h = h' := congrArg Push.Instance.height heq
  cases hh
  have hg : g = g' := Fin.ext (congrArg (fun I => I.target.2.val) heq)
  cases hg
  have hr := congrArg (fun I => (PushFS.Encoding.data I.toStorage).rows) heq
  have hs := (PushFS.Encoding.rows_injective hr).2
  have hp : p = p' := congrArg State.player hs
  cases hp
  have hE : E = E' := compl_injective (congrArg State.boxes hs)
  cases hE
  rfl

/-- The original ordinary-game encoding, restricted to left-boundary targets. -/
def encoding : Input ↪ List Bool :=
  (⟨source, source_injective⟩ : Input ↪ Push.Instance).trans Push.encoding

@[fun_prop] theorem source_polyTime : ComputableInPolyTime source encoding Push.encoding :=
  ComputableInPolyTime.of_eq fun _ => rfl

private def data (r : Input) : Data := ⟨PushFS.Encoding.data r.source.toStorage, r.goalY.val⟩

@[fun_prop] private theorem data_polyTime : ComputableInPolyTime data encoding encData := by
  have hs : ComputableInPolyTime (fun r : Input => PushFS.Encoding.data r.source.toStorage)
      encoding PushFS.Encoding.encData :=
    PushFS.Encoding.data_polyTime.comp (Push.Machine.toStorage_polyTime.comp source_polyTime)
  have hg : ComputableInPolyTime (fun r : Input => r.goalY.val) encoding encUnary :=
    ((ComputableInPolyTime.snd _ _).comp Push.Machine.target_polyTime).comp source_polyTime
  unfold data
  fun_prop

end Input

namespace Data

private def outputWidth (d : Data) : ℕ := d.source.width + 2
private def outputHeight (d : Data) : ℕ := d.source.height + (d.source.height - d.goalY)

@[fun_prop] private theorem outputWidth_polyTime :
    ComputableInPolyTime outputWidth encData encUnary := by unfold outputWidth; fun_prop

@[fun_prop] private theorem outputHeight_polyTime :
    ComputableInPolyTime outputHeight encData encUnary := by unfold outputHeight; fun_prop

private abbrev encQuery : (Data × ℕ × ℕ) ↪ List Bool :=
  encPair encData (encPair encUnary encUnary)

/-- The single westward exit and the two new southern walkways. -/
private def auxiliaryTest (q : Data × ℕ × ℕ) : Bool :=
  decide ((q.2.1 = 1 ∧ q.2.2 = q.1.goalY) ∨
    (q.2.1 < 2 ∧ q.1.source.height ≤ q.2.2))

@[fun_prop] private theorem auxiliaryTest_polyTime :
    ComputableInPolyTime auxiliaryTest encQuery encBool := by
  unfold auxiliaryTest encQuery
  fun_prop

/-- Copy each source tile two columns east, and emit the ordinary box complement elsewhere. -/
private def tile (q : Data × ℕ × ℕ) : PushFS.Encoding.Tile :=
  if 2 ≤ q.2.1 ∧ q.2.1 < q.1.outputWidth ∧ q.2.2 < q.1.source.height then
    (q.1.source.rows.getD q.2.2 []).getD (q.2.1 - 2) Reduction.Bitmap.emptyTile
  else ⟨false, !(auxiliaryTest q), !(auxiliaryTest q), false⟩

@[fun_prop] private theorem tile_polyTime :
    ComputableInPolyTime tile encQuery PushFS.Encoding.encTile := by
  unfold tile encQuery
  fun_prop

/-- Emit the full explicit expanded rectangle. -/
private def emit (d : Data) : PushFS.Encoding.Data :=
  ⟨d.outputWidth, d.outputHeight, (List.range d.outputHeight).map fun y =>
    (List.range d.outputWidth).map fun x => tile (d, x, y)⟩

@[fun_prop] private theorem emit_polyTime :
    ComputableInPolyTime emit encData PushFS.Encoding.encData := by
  unfold emit
  fun_prop

end Data

namespace Input

@[simp] private theorem data_outputWidth (r : Input) : (data r).outputWidth = r.outputWidth := rfl
@[simp] private theorem data_outputHeight (r : Input) : (data r).outputHeight = r.outputHeight := rfl

private theorem auxiliaryTest_correct (r : Input) (q : Cell r.outputWidth r.outputHeight) :
    Data.auxiliaryTest (data r, q.1.val, q.2.val) = decide (q ∈ r.auxiliaryHoles) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Data.auxiliaryTest, decide_eq_true_eq, auxiliaryHoles, walkHoles,
    Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and,
    entry, Prod.ext_iff, Fin.ext_iff]
  rfl

private theorem source_tile (r : Input) (q : Cell r.width r.height) :
    PushFS.Encoding.tile r.compile.toStorage.board r.compile.initial (r.embed q) =
      PushFS.Encoding.tile r.source.toStorage.board r.source.initial q := by
  change PushFS.Encoding.tile ⟨∅, (r.extend r.initial).emptyᶜ⟩
      (r.extend r.initial).toState (r.embed q) =
    PushFS.Encoding.tile ⟨∅, r.initial.emptyᶜ⟩ r.initial.toState q
  simp only [PushFS.Encoding.tile, HoleState.toState, Finset.notMem_empty, decide_false,
    Finset.mem_compl, r.embed_mem_extend]
  simp only [extend, r.embed_injective.eq_iff]
  rfl

private theorem auxiliary_tile (r : Input) (q : Cell r.outputWidth r.outputHeight)
    (hi : ¬ (2 ≤ q.1.val ∧ q.1.val < r.outputWidth ∧ q.2.val < r.height)) :
    Data.tile (data r, q.1.val, q.2.val) =
      PushFS.Encoding.tile r.compile.toStorage.board r.compile.initial q := by
  have hpre (a : Cell r.width r.height) : r.embed a ≠ q := by
    intro he
    apply hi
    have hx := congrArg (fun q => q.1.val) he
    have hy := congrArg (fun q => q.2.val) he
    have ha := a.1.isLt
    have hay := a.2.isLt
    dsimp [embed, outputWidth] at hx hy ⊢
    omega
  have he : q ∉ r.initial.empty.image r.embed := by
    intro hh
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hh
    exact hpre a ha
  have hp : q ≠ r.embed r.initial.player := fun he => hpre _ he.symm
  rw [Data.tile, ite_eq_right (by exact hi), r.auxiliaryTest_correct q]
  change PushFS.Encoding.Tile.mk false (!(decide (q ∈ r.auxiliaryHoles)))
      (!(decide (q ∈ r.auxiliaryHoles))) false =
    PushFS.Encoding.tile ⟨∅, (r.extend r.initial).emptyᶜ⟩ (r.extend r.initial).toState q
  simp only [PushFS.Encoding.tile, HoleState.toState, Finset.notMem_empty, decide_false,
    Finset.mem_compl, extend, Finset.mem_union, he, false_or, hp, decide_not]

/-- The raw emitter copies precisely the actual translated source and added dock cells. -/
private theorem tile_eq (r : Input) (q : Cell r.outputWidth r.outputHeight) :
    Data.tile (data r, q.1.val, q.2.val) =
      PushFS.Encoding.tile r.compile.toStorage.board r.compile.initial q := by
  by_cases hi : 2 ≤ q.1.val ∧ q.1.val < r.outputWidth ∧ q.2.val < r.height
  · have hx : q.1.val - 2 < r.width := by have := hi.2.1; dsimp [outputWidth] at this; omega
    let a : Cell r.width r.height := (⟨q.1.val - 2, hx⟩, ⟨q.2.val, hi.2.2⟩)
    have ha : r.embed a = q := by
      apply Prod.ext <;> apply Fin.ext
      · change q.1.val - 2 + 2 = q.1.val
        omega
      · rfl
    rw [Data.tile, ite_eq_left (by exact hi)]
    change ((PushFS.Encoding.rows r.source.toStorage.board r.initial.toState).getD q.2.val []).getD
      (q.1.val - 2) Reduction.Bitmap.emptyTile = _
    have hlookup := PushFS.Encoding.lookup_rows (w := r.width) (h := r.height)
      r.source.toStorage.board r.initial.toState (q.1.val - 2) q.2.val hx hi.2.2
    exact hlookup.trans ((r.source_tile a).symm.trans (by rw [ha]))
  · exact r.auxiliary_tile q hi

/-- The full raw output is exactly the compiled game's standard dense data. -/
private theorem emit_eq (r : Input) :
    PushFS.Encoding.data r.compile.toStorage = Data.emit (data r) := by
  have hw : r.compile.toStorage.width = r.outputWidth := rfl
  have hh : r.compile.toStorage.height = r.outputHeight := rfl
  change PushFS.Encoding.Data.mk r.outputWidth r.outputHeight (PushFS.Encoding.rows _ _) =
    PushFS.Encoding.Data.mk (data r).outputWidth (data r).outputHeight _
  rw [data_outputWidth, data_outputHeight]
  congr 1
  apply List.ext_getElem
  · simp only [PushFS.Encoding.rows, List.length_ofFn, List.length_map, List.length_range, hh]
  · intro y hy _
    have hy' : y < r.outputHeight := by
      simpa only [PushFS.Encoding.rows, List.length_ofFn, hh] using hy
    simp only [PushFS.Encoding.rows, List.getElem_ofFn, List.getElem_map, List.getElem_range]
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_map, List.length_range, hw]
    · intro x hx _
      have hx' : x < r.outputWidth := by simpa only [List.length_ofFn, hw] using hx
      simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
      exact (r.tile_eq (⟨x, hx'⟩, ⟨y, hy'⟩)).symm

/-- The literal southwest-dock compiler has a standard polynomial-time implementation. -/
@[fun_prop] theorem compile_polyTime : ComputableInPolyTime compile encoding Push.encoding := by
  have h : ComputableInPolyTime
      (fun r : Input => (Data.emit (data r), 0, (data r).outputHeight - 1)) encoding
      (encPair PushFS.Encoding.encData (encPair encUnary encUnary)) := by
    fun_prop
  apply h.of_enc_eq
  intro r
  change encPair PushFS.Encoding.encData (encPair encUnary encUnary)
      (PushFS.Encoding.data r.compile.toStorage, r.compile.target.1.val,
        r.compile.target.2.val) = _
  rw [r.emit_eq, data_outputHeight]
  rfl

end Input
end PushPuzzle.Push.CornerDock
