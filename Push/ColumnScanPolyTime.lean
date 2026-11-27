/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ColumnScan
public import Push.Encoding
public import PushFS.Space.StateDecoding
public import PushFS.Space.Primitives
public import PushFS.UnarySum

/-! Explicit dense input and polynomial-time emission of the committed column reader. -/

@[expose] public section
namespace PushPuzzle.Push.ColumnScan

open PushFS PushS Turing.MultiTapeTM
open scoped PushFS.Encoding

/-- Proof-free source bitmap and unary column quotas. -/
structure Data where
  width : ℕ
  height : ℕ
  playerX : ℕ
  playerY : ℕ
  holes : List Bool
  quotas : List ℕ
  extraWidth : ℕ

enc_structure encData : Data where
  width : encUnary, height : encUnary, playerX : encUnary, playerY : encUnary,
  holes : encBits, quotas : (encList encUnary), extraWidth : encUnary

namespace Input

/-- Serialize the actual source holes in the common row-major order. -/
def data (r : Input) : Data where
  width := r.width
  height := r.height
  playerX := r.initial.player.1.val
  playerY := r.initial.player.2.val
  holes := List.ofFn fun i : Fin (r.height * r.width) =>
    decide (State.cellAt i ∈ r.initial.empty)
  quotas := r.quotas
  extraWidth := r.extraWidth

theorem data_injective : Function.Injective data := by
  rintro ⟨w, h, ⟨p, E, hp⟩, qs, hqs, hquota, extra⟩
    ⟨w', h', ⟨p', E', hp'⟩, qs', hqs', hquota', extra'⟩ heq
  have hw : w = w' := congrArg Data.width heq
  cases hw
  have hh : h = h' := congrArg Data.height heq
  cases hh
  have hqs : qs = qs' := congrArg Data.quotas heq
  cases hqs
  have hx : p.1 = p'.1 := Fin.ext (congrArg Data.playerX heq)
  have hy : p.2 = p'.2 := Fin.ext (congrArg Data.playerY heq)
  have hp : p = p' := Prod.ext hx hy
  cases hp
  have hb := congrArg Data.holes heq
  have hE : E = E' := by
    ext q
    have hi := congrFun (List.ofFn_injective hb) (finProdFinEquiv q.swap)
    simpa only [State.cellAt_index, decide_eq_decide] using hi
  cases hE
  have hextra : extra = extra' := congrArg Data.extraWidth heq
  cases hextra
  rfl

/-- Unary dimensions and player coordinates, the dense source bitmap, and unary quotas. -/
def encoding : Input ↪ List Bool :=
  (⟨data, data_injective⟩ : Input ↪ Data).trans encData

@[fun_prop] theorem data_polyTime : ComputableInPolyTime data encoding encData :=
  ComputableInPolyTime.of_eq fun _ => rfl

/-- Bitmap lookup at an actual source cell recovers its exact hole predicate. -/
private theorem bitmap_correct (r : Input) (q : Cell r.width r.height) :
    PushFS.Machine.bitAt ((data r).holes, q.2.val * r.width + q.1.val) =
      decide (q ∈ r.initial.empty) := by
  have hi := (finProdFinEquiv q.swap).isLt
  simp only [data, PushFS.Machine.bitAt]
  have hindex : q.2.val * r.width + q.1.val = (finProdFinEquiv q.swap).val := by
    simp [finProdFinEquiv, Nat.add_comm, Nat.mul_comm]
  rw [hindex]
  simp only [List.getElem?_ofFn, dite_eq_left hi, Option.getD_some, Fin.eta,
    State.cellAt_index]

/-- Counting the true bits computes the source's finite hole inventory. -/
private theorem bitmap_count (r : Input) : (data r).holes.countP id = r.sourceHoles := by
  rw [data, State.countP_ofFn]
  change (Finset.univ.filter fun i : Fin (r.height * r.width) =>
    decide (State.cellAt i ∈ r.initial.empty) = true).card = r.initial.empty.card
  apply Finset.card_bij (fun i _ => State.cellAt i)
  · intro i hi
    simpa using (Finset.mem_filter.mp hi).2
  · intro i hi j hj hij
    have he := congrArg (fun q => finProdFinEquiv q.swap) hij
    simpa only [State.index_cellAt] using he
  · intro q hq
    refine ⟨finProdFinEquiv q.swap, ?_, State.cellAt_index q⟩
    simp [hq]

end Input

namespace Data

def sourceHoles (d : Data) : ℕ := d.holes.countP id
def quota (d : Data) : ℕ := d.quotas.sum
def length (d : Data) : ℕ := max 7 (d.quota + max d.sourceHoles d.width + 4)
def outputWidth (d : Data) : ℕ := d.width + 2 + d.extraWidth
def outputHeight (d : Data) : ℕ := d.height + d.length
def firstLevel (d : Data) : ℕ := d.height - 1 + d.length - 2
def targetLevel (d : Data) : ℕ := d.firstLevel - d.quota

@[fun_prop] theorem sourceHoles_polyTime :
    ComputableInPolyTime sourceHoles encData encUnary := by
  unfold sourceHoles
  exact ComputableInPolyTime.countPWith
    (encP := encBool) (encA := encBool) (test := fun p => p.2)
    (ComputableInPolyTime.snd _ _) (ComputableInPolyTime.const false)
    (by fun_prop)

@[fun_prop] theorem quota_polyTime :
    ComputableInPolyTime quota encData encUnary := by
  unfold quota
  fun_prop

@[fun_prop] theorem length_polyTime :
    ComputableInPolyTime length encData encUnary := by
  unfold length
  fun_prop

@[fun_prop] theorem outputWidth_polyTime :
    ComputableInPolyTime outputWidth encData encUnary := by
  unfold outputWidth
  fun_prop

@[fun_prop] theorem outputHeight_polyTime :
    ComputableInPolyTime outputHeight encData encUnary := by
  unfold outputHeight
  fun_prop

@[fun_prop] theorem firstLevel_polyTime :
    ComputableInPolyTime firstLevel encData encUnary := by
  unfold firstLevel
  fun_prop

@[fun_prop] theorem targetLevel_polyTime :
    ComputableInPolyTime targetLevel encData encUnary := by
  unfold targetLevel
  fun_prop

abbrev encQuery : (Data × ℕ × ℕ) ↪ List Bool :=
  encPair encData (encPair encUnary encUnary)

/-- The source bitmap, three seal holes, empty room, and one quota needle per column. -/
def holeTest (q : Data × ℕ × ℕ) : Bool :=
  let d := q.1
  let x := q.2.1
  let y := q.2.2
  (decide (x < d.width ∧ y < d.height) &&
    PushFS.Machine.bitAt (d.holes, y * d.width + x)) ||
  decide (x = d.width ∧ (y = d.height - 1 ∨ y = d.height ∨ y = d.outputHeight - 1)) ||
  decide (d.width < x ∧ d.height ≤ y) ||
  decide (x < d.width ∧ y = d.firstLevel - (d.quotas.drop (x + 1)).sum)

@[fun_prop] theorem holeTest_polyTime :
    ComputableInPolyTime holeTest encQuery encBool := by
  unfold holeTest encQuery
  fun_prop

/-- Emit the exact initial occupancy twice, as required by the common dense encoding. -/
def tile (q : Data × ℕ × ℕ) : PushFS.Encoding.Tile :=
  ⟨false, !(holeTest q), !(holeTest q),
    decide (q.2.1 = q.1.playerX ∧ q.2.2 = q.1.playerY)⟩

@[fun_prop] theorem tile_polyTime :
    ComputableInPolyTime tile encQuery PushFS.Encoding.encTile := by
  unfold tile encQuery
  fun_prop

/-- Write every output cell explicitly in row-major order. -/
def emit (d : Data) : PushFS.Encoding.Data :=
  ⟨d.outputWidth, d.outputHeight, (List.range d.outputHeight).map fun y =>
    (List.range d.outputWidth).map fun x => tile (d, x, y)⟩

@[fun_prop] theorem emit_polyTime :
    ComputableInPolyTime emit encData PushFS.Encoding.encData := by
  unfold emit
  fun_prop

end Data

namespace Input

@[simp] theorem data_sourceHoles (r : Input) : (data r).sourceHoles = r.sourceHoles :=
  bitmap_count r

@[simp] theorem data_quota (r : Input) : (data r).quota = r.quota := rfl

@[simp] theorem data_length (r : Input) : (data r).length = r.length := by
  change max 7 ((data r).quota + max (data r).sourceHoles r.width + 4) = r.length
  rw [data_quota, data_sourceHoles]
  rfl

@[simp] theorem data_outputWidth (r : Input) : (data r).outputWidth = r.outputWidth := rfl

@[simp] theorem data_outputHeight (r : Input) : (data r).outputHeight = r.outputHeight := by
  change r.height + (data r).length = r.height + r.length
  rw [data_length]

@[simp] theorem data_firstLevel (r : Input) : (data r).firstLevel = r.firstLevel := by
  change r.height - 1 + (data r).length - 2 = r.firstLevel
  rw [data_length]
  rfl

@[simp] theorem data_targetLevel (r : Input) : (data r).targetLevel = r.targetLevel := by
  simp only [Data.targetLevel, data_firstLevel, data_quota, targetLevel]

private theorem source_test (r : Input) (q : Cell r.outputWidth r.outputHeight) :
    (q.1.val < r.width ∧ q.2.val < r.height ∧
      PushFS.Machine.bitAt ((data r).holes, q.2.val * r.width + q.1.val) = true) ↔
      q ∈ r.sourceEmpty := by
  constructor
  · rintro ⟨hx, hy, hb⟩
    let a : Cell r.width r.height := (⟨q.1.val, hx⟩, ⟨q.2.val, hy⟩)
    have ha : a ∈ r.initial.empty := by
      exact of_decide_eq_true ((r.bitmap_correct a).symm.trans hb)
    exact Finset.mem_image.mpr ⟨a, ha, by apply Prod.ext <;> apply Fin.ext <;> rfl⟩
  · intro hq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
    exact ⟨a.1.isLt, a.2.isLt, (r.bitmap_correct a).trans (by simp [ha])⟩

private theorem needle_test (r : Input) (q : Cell r.outputWidth r.outputHeight) :
    (q.1.val < r.width ∧
      q.2.val = r.firstLevel - (r.quotas.drop (q.1.val + 1)).sum) ↔ q ∈ r.needles := by
  constructor
  · rintro ⟨hx, hy⟩
    refine Finset.mem_image.mpr ⟨⟨q.1.val, hx⟩, Finset.mem_univ _, ?_⟩
    apply Prod.ext <;> apply Fin.ext
    · rfl
    · exact hy.symm
  · intro hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    exact ⟨i.isLt, rfl⟩

/-- The executable test agrees with every cell of the actual expanded hole set. -/
private theorem holeTest_correct (r : Input) (q : Cell r.outputWidth r.outputHeight) :
    Data.holeTest (data r, q.1.val, q.2.val) = decide (q ∈ r.empty) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Data.holeTest, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    data_outputHeight, data_firstLevel]
  change ((((q.1.val < r.width ∧ q.2.val < r.height) ∧
      PushFS.Machine.bitAt ((data r).holes, q.2.val * r.width + q.1.val) = true) ∨
      (q.1.val = r.width ∧
        (q.2.val = r.height - 1 ∨ q.2.val = r.height ∨ q.2.val = r.outputHeight - 1))) ∨
      (r.width < q.1.val ∧ r.height ≤ q.2.val)) ∨
      (q.1.val < r.width ∧
        q.2.val = r.firstLevel - (r.quotas.drop (q.1.val + 1)).sum) ↔ q ∈ r.empty
  rw [and_assoc, r.source_test, r.needle_test]
  simp only [empty, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    room, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [door, upper, bottom, Prod.ext_iff, Fin.ext_iff]
  tauto

/-- Every emitted tile is the corresponding tile of the actual no-wall game. -/
private theorem tile_eq (r : Input) (q : Cell r.outputWidth r.outputHeight) :
    Data.tile (data r, q.1.val, q.2.val) =
      PushFS.Encoding.tile r.compile.toStorage.board r.compile.initial q := by
  change Data.tile (data r, q.1.val, q.2.val) =
    PushFS.Encoding.tile ⟨∅, r.emptyᶜ⟩
      ⟨r.embed r.initial.player, r.emptyᶜ⟩ q
  rw [Data.tile, r.holeTest_correct q]
  simp only [PushFS.Encoding.tile, Finset.notMem_empty, decide_false, Finset.mem_compl,
    decide_not, Bool.decide_and, data, embed, Prod.ext_iff, Fin.ext_iff]
  congr 1

/-- The complete emitted bitmap is the actual compiler output's dense board data. -/
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

/-- The literal column-reader game compiler is polynomial-time in the dense source input. -/
@[fun_prop] theorem compile_polyTime :
    ComputableInPolyTime compile encoding Push.encoding := by
  have h : ComputableInPolyTime
      (fun r : Input => (Data.emit (data r), 0, (data r).targetLevel)) encoding
      (encPair PushFS.Encoding.encData (encPair encUnary encUnary)) := by
    fun_prop
  apply h.of_enc_eq
  intro r
  change encPair PushFS.Encoding.encData (encPair encUnary encUnary)
      (PushFS.Encoding.data r.compile.toStorage, r.compile.target.1.val,
        r.compile.target.2.val) = _
  rw [r.emit_eq, data_targetLevel]
  rfl

end Input
end PushPuzzle.Push.ColumnScan
