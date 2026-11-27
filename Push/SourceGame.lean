/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.Encoding
public import PushS.Encoding
public import PushFS.Space.Primitives

/-! The same live wall-free storage source, with its ordinary player target at the southeast corner. -/

public section
namespace PushPuzzle.Push.SourceGame

open PushFS Turing.MultiTapeTM
open scoped PushPuzzle.PushFS.Encoding

/-- Keep every initial box and the starting player, and require the literal southeast corner. -/
@[expose] def ofStorage (I : PushS.Instance) : Push.Instance where
  width := I.width
  height := I.height
  initial := I.initial
  target := (⟨I.width - 1, by have := I.toInstance.width_pos; omega⟩,
    ⟨I.height - 1, by have := I.toInstance.height_pos; omega⟩)
  player_empty := by exact I.initial_valid.2.2

@[simp] theorem ofStorage_width (I : PushS.Instance) : (ofStorage I).width = I.width := rfl
@[simp] theorem ofStorage_height (I : PushS.Instance) : (ofStorage I).height = I.height := rfl
@[simp] theorem ofStorage_initial (I : PushS.Instance) : (ofStorage I).initial = I.initial := rfl

/-- The ordinary source and the storage source have exactly the same empty fixed-wall set. -/
@[simp] theorem ofStorage_walls (I : PushS.Instance) : (ofStorage I).board.walls = I.board.walls := I.walls_empty.symm

/-- The designated destination is exactly the source rectangle's southeast corner. -/
theorem ofStorage_target (I : PushS.Instance) :
    (ofStorage I).target.1.val + 1 = I.width ∧ (ofStorage I).target.2.val + 1 = I.height := by
  have hw := I.toInstance.width_pos
  have hh := I.toInstance.height_pos
  change I.width - 1 + 1 = I.width ∧ I.height - 1 + 1 = I.height
  omega

private def sourceTile (tile : PushFS.Encoding.Tile) : PushFS.Encoding.Tile :=
  ⟨false, tile.box, tile.box, tile.player⟩

private def sourceData (d : PushFS.Encoding.Data) : PushFS.Encoding.Data :=
  { d with rows := d.rows.map (fun row => row.map sourceTile) }

private theorem sourceData_correct (I : PushS.Instance) :
    PushFS.Encoding.data (ofStorage I).toStorage = sourceData (PushFS.Encoding.data I.toInstance) := by
  simp only [PushFS.Encoding.data, sourceData]
  congr 1
  simp only [PushFS.Encoding.rows, List.map_ofFn, Function.comp_def]
  apply congrArg List.ofFn
  funext y
  apply congrArg List.ofFn
  funext x
  simp only [PushFS.Encoding.tile, sourceTile, ofStorage, Push.Instance.toStorage]
  rfl

private abbrev encOutput : (PushFS.Encoding.Data × ℕ × ℕ) ↪ List Bool :=
  encPair PushFS.Encoding.encData (encPair encUnary encUnary)

@[local fun_prop] private theorem sourceTile_polyTime : ComputableInPolyTime sourceTile
    PushFS.Encoding.encTile PushFS.Encoding.encTile := ComputableInPolyTime.of_finite _

@[local fun_prop] private theorem sourceData_polyTime : ComputableInPolyTime sourceData
    PushFS.Encoding.encData PushFS.Encoding.encData := by
  unfold sourceData
  fun_prop

private theorem output_polyTime : ComputableInPolyTime
    (fun d : PushFS.Encoding.Data => (sourceData d, d.width - 1, d.height - 1))
    PushFS.Encoding.encData encOutput := by
  unfold encOutput
  fun_prop

private theorem storageData_polyTime : ComputableInPolyTime
    (fun I : PushS.Instance => PushFS.Encoding.data I.toInstance) PushS.encoding PushFS.Encoding.encData :=
  PushFS.Machine.data_polyTime.comp (ComputableInPolyTime.of_eq fun _ => rfl)

/-- Both dense board maps and the unary southeast destination are emitted in standard polynomial time. -/
@[fun_prop] theorem ofStorage_polyTime : ComputableInPolyTime ofStorage PushS.encoding Push.encoding :=
  (output_polyTime.comp storageData_polyTime).of_enc_eq (fun I => by
    change encOutput (PushFS.Encoding.data (ofStorage I).toStorage,
      (ofStorage I).target.1.val, (ofStorage I).target.2.val) =
        encOutput (sourceData (PushFS.Encoding.data I.toInstance), I.width - 1, I.height - 1)
    rw [sourceData_correct]
    rfl)

end PushPuzzle.Push.SourceGame
