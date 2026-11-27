/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicInventory
public import Push.CyclicPolyTime

/-! Emit the complete next column-reader input from the actual widened dock bitmap. -/

public section
namespace PushPuzzle.Push.Cyclic

open PushFS PushS Turing.MultiTapeTM
open scoped PushPuzzle.Push.ColumnScan

private def holeBitmap (I : Push.Instance) : List Bool :=
  (PushFS.Machine.flags PushFS.Encoding.Tile.box I.toStorage).map Bool.not

private theorem holeBitmap_correct (I : Push.Instance) :
    (List.ofFn fun i : Fin (I.height * I.width) => decide (State.cellAt i ∈ holes I.initial)) =
      holeBitmap I := by
  rw [holeBitmap, PushFS.Machine.flags_eq_ofFn, List.map_ofFn]
  simp only [PushFS.Encoding.tile, holes, Finset.mem_compl, decide_not]
  rfl

@[local fun_prop] private theorem holeBitmap_polyTime :
    ComputableInPolyTime holeBitmap Push.encoding encBits := by
  have hf := (PushFS.Machine.flags_polyTime PushFS.Encoding.Tile.box).comp Push.Machine.toStorage_polyTime
  unfold holeBitmap
  exact ComputableInPolyTime.bitsMapWithInput hf (by fun_prop)

private def nextData (r : ColumnScan.Input) (rows : List ℕ) : ColumnScan.Data where
  width := (nextSource r).width
  height := (nextSource r).height
  playerX := r.initial.player.2.val
  playerY := (nextSource r).height - (r.initial.player.1.val + 3)
  holes := holeBitmap (nextSource r)
  quotas := nextQuotas r rows
  extraWidth := 0

private theorem nextData_polyTime : ComputableInPolyTime
    (fun q : ColumnScan.Input × List ℕ => nextData q.1 q.2)
    (encPair ColumnScan.Input.encoding (encList encUnary)) ColumnScan.encData := by
  have hn : ComputableInPolyTime (fun r => (nextSource r).toStorage)
      ColumnScan.Input.encoding PushFS.encoding := Push.Machine.toStorage_polyTime.comp nextSource_polyTime
  have hw : ComputableInPolyTime (fun r => (nextSource r).width)
      ColumnScan.Input.encoding encUnary := PushFS.Machine.width_polyTime.comp hn
  have hh : ComputableInPolyTime (fun r => (nextSource r).height)
      ColumnScan.Input.encoding encUnary := PushFS.Machine.height_polyTime.comp hn
  have hx : ComputableInPolyTime (fun r : ColumnScan.Input => r.initial.player.1.val)
      ColumnScan.Input.encoding encUnary := ColumnScan.encData_playerX_polyTime ColumnScan.Input.data_polyTime
  have hy : ComputableInPolyTime (fun r : ColumnScan.Input => r.initial.player.2.val)
      ColumnScan.Input.encoding encUnary := ColumnScan.encData_playerY_polyTime ColumnScan.Input.data_polyTime
  have hb := holeBitmap_polyTime.comp nextSource_polyTime
  have hf := ComputableInPolyTime.fst ColumnScan.Input.encoding (encList encUnary)
  have hwQ := hw.comp hf
  have hhQ := hh.comp hf
  have hxQ := hx.comp hf
  have hyQ := hy.comp hf
  have hbQ := hb.comp hf
  unfold nextData
  fun_prop

private theorem nextData_eq (r : ColumnScan.Input) (rows : List ℕ)
    (hlen : rows.length = r.height) (hb : rows.sum ≤ r.sourceHoles) :
    ColumnScan.Input.data (nextInput r rows hlen hb) = nextData r rows := by
  have hx : (nextSource r).initial.player.1.val = r.initial.player.2.val :=
    sourceEmbed_x r r.initial.player
  have hy : (nextSource r).initial.player.2.val =
      (nextSource r).height - (r.initial.player.1.val + 3) := sourceEmbed_y r r.initial.player
  dsimp only [ColumnScan.Input.data, nextInput, nextData]
  rw [hx, hy]
  congr 1
  exact holeBitmap_correct (nextSource r)

/-- The next valid reader input is emitted in standard polynomial time, including its complete bitmap. -/
@[fun_prop] theorem nextInput_polyTime {α : Type} {enc : α ↪ List Bool}
    {reader : α → ColumnScan.Input} {rows : α → List ℕ}
    (hr : ComputableInPolyTime reader enc ColumnScan.Input.encoding)
    (hq : ComputableInPolyTime rows enc (encList encUnary))
    (hlen : ∀ a, (rows a).length = (reader a).height)
    (hb : ∀ a, (rows a).sum ≤ (reader a).sourceHoles) :
    ComputableInPolyTime (fun a => nextInput (reader a) (rows a) (hlen a) (hb a))
      enc ColumnScan.Input.encoding :=
  (nextData_polyTime.comp (hr.prod hq)).of_enc_eq
    (fun a => congrArg ColumnScan.encData (nextData_eq (reader a) (rows a) (hlen a) (hb a)))

end PushPuzzle.Push.Cyclic
