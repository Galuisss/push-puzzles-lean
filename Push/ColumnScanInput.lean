/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ColumnScanPolyTime
public import Push.ColumnScanForward
public import Push.ColumnScanSourceCrop
public import Push.Space.Goal
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div

/-! Turn an actual ordinary game and a dense quota vector into the literal source reader recipe. -/

public section
namespace PushPuzzle.Push.ColumnScan.Input

open PushFS PushS Turing.MultiTapeTM
open scoped PushPuzzle.Push.ColumnScan

/-- Keep the complete initial ordinary-game state and attach the prescribed dense column vector. -/
@[expose] def ofInstance (I : Push.Instance) (quotas : List ℕ)
    (hlen : quotas.length = I.width) (hb : quotas.sum ≤ (holes I.initial).card) : ColumnScan.Input where
  width := I.width
  height := I.height
  initial := ⟨I.initial.player, holes I.initial, player_mem_holes I.initial_valid⟩
  quotas := quotas
  quotas_width := hlen
  quotas_le := hb
  extraWidth := 0

/-- The factory retains the exact original player and complete box set. -/
@[simp] theorem ofInstance_initial (I : Push.Instance) (quotas : List ℕ)
    (hlen : quotas.length = I.width) (hb : quotas.sum ≤ (holes I.initial).card) :
    (ofInstance I quotas hlen hb).initial.toState = I.initial := by
  apply State.ext
  · rfl
  · exact compl_compl _

/-- The original game and the factory's source board have the same empty wall set. -/
@[simp] theorem ofInstance_walls (I : Push.Instance) (quotas : List ℕ)
    (hlen : quotas.length = I.width) (hb : quotas.sum ≤ (holes I.initial).card) :
    (ofInstance I quotas hlen hb).sourceBoard.walls = I.board.walls := rfl

/-- The factory's complete source-hole inventory is the original game's actual initial inventory. -/
@[simp] theorem ofInstance_sourceHoles (I : Push.Instance) (quotas : List ℕ)
    (hlen : quotas.length = I.width) (hb : quotas.sum ≤ (holes I.initial).card) :
    (ofInstance I quotas hlen hb).sourceHoles = (holes I.initial).card := rfl

/-- A literal southeast game target is the factory's source corner. -/
theorem ofInstance_corner (I : Push.Instance) (quotas : List ℕ)
    (hlen : quotas.length = I.width) (hb : quotas.sum ≤ (holes I.initial).card)
    (hx : I.target.1.val + 1 = I.width) (hy : I.target.2.val + 1 = I.height) :
    (ofInstance I quotas hlen hb).sourceCorner = I.target := by
  apply Prod.ext <;> apply Fin.ext
  · change I.width - 1 = I.target.1.val; omega
  · change I.height - 1 = I.target.2.val; omega

private def holeBitmap (I : Push.Instance) : List Bool :=
  PushFS.Machine.flags (fun tile => !tile.box) I.toStorage

private theorem holeBitmap_correct (I : Push.Instance) :
    (List.ofFn fun i : Fin (I.height * I.width) => decide (State.cellAt i ∈ holes I.initial)) =
      holeBitmap I := by
  rw [holeBitmap, PushFS.Machine.flags_eq_ofFn]
  simp only [PushFS.Encoding.tile, holes, Finset.mem_compl, decide_not]
  rfl

@[local fun_prop] private theorem holeBitmap_polyTime :
    ComputableInPolyTime holeBitmap Push.encoding encBits :=
  (PushFS.Machine.flags_polyTime (fun tile => !tile.box)).comp Push.Machine.toStorage_polyTime

private theorem idxOf_single_marker {n : ℕ} (i : Fin n) :
    (List.ofFn fun j : Fin n => decide (j = i)).idxOf true = i.val := by
  let word := List.ofFn fun j : Fin n => decide (j = i)
  have hm : true ∈ word := List.mem_ofFn.mpr ⟨i, by simp⟩
  have hlt := List.idxOf_lt_length_of_mem hm
  have hget := List.getElem_idxOf hlt
  have he : (⟨word.idxOf true, by simpa only [word, List.length_ofFn] using hlt⟩ : Fin n) = i := by
    simpa only [word, List.getElem_ofFn, decide_eq_true_eq] using hget
  exact congrArg Fin.val he

private def playerIndex (I : Push.Instance) : ℕ :=
  (PushFS.Machine.flags PushFS.Encoding.Tile.player I.toStorage).idxOf true

private theorem playerIndex_correct (I : Push.Instance) :
    playerIndex I = (finProdFinEquiv I.initial.player.swap).val := by
  rw [playerIndex, PushFS.Machine.flags_eq_ofFn]
  simp only [PushFS.Encoding.tile, State.cellAt_eq_iff]
  exact idxOf_single_marker _

@[local fun_prop] private theorem playerIndex_polyTime : ComputableInPolyTime playerIndex Push.encoding encUnary := by
  have hf := (PushFS.Machine.flags_polyTime PushFS.Encoding.Tile.player).comp Push.Machine.toStorage_polyTime
  have hl := ((bits_encList_polyTime encBool).1).comp hf
  unfold playerIndex
  fun_prop

private theorem playerX_correct (I : Push.Instance) : playerIndex I % I.width = I.initial.player.1.val := by
  rw [playerIndex_correct]
  change (I.initial.player.1.val + I.width * I.initial.player.2.val) % I.width = I.initial.player.1.val
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt I.initial.player.1.isLt]

private theorem playerY_correct (I : Push.Instance) : playerIndex I / I.width = I.initial.player.2.val := by
  rw [playerIndex_correct]
  change (I.initial.player.1.val + I.width * I.initial.player.2.val) / I.width = I.initial.player.2.val
  have hw : 0 < I.width := I.toStorage.width_pos
  rw [Nat.add_mul_div_left _ _ hw, Nat.div_eq_of_lt I.initial.player.1.isLt, Nat.zero_add]

private def instanceData (I : Push.Instance) (quotas : List ℕ) : ColumnScan.Data where
  width := I.width
  height := I.height
  playerX := playerIndex I % I.width
  playerY := playerIndex I / I.width
  holes := holeBitmap I
  quotas := quotas
  extraWidth := 0

private theorem instanceData_polyTime : ComputableInPolyTime
    (fun p : Push.Instance × List ℕ => instanceData p.1 p.2)
    (encPair Push.encoding (encList encUnary)) ColumnScan.encData := by
  have hw : ComputableInPolyTime Push.Instance.width Push.encoding encUnary :=
    PushFS.Machine.width_polyTime.comp Push.Machine.toStorage_polyTime
  have hh : ComputableInPolyTime Push.Instance.height Push.encoding encUnary :=
    PushFS.Machine.height_polyTime.comp Push.Machine.toStorage_polyTime
  unfold instanceData
  fun_prop

private theorem instanceData_eq (I : Push.Instance) (quotas : List ℕ)
    (hlen : quotas.length = I.width) (hb : quotas.sum ≤ (holes I.initial).card) :
    ColumnScan.Input.data (ofInstance I quotas hlen hb) = instanceData I quotas := by
  simp only [ColumnScan.Input.data, ofInstance, instanceData, playerX_correct, playerY_correct]
  congr 1
  exact holeBitmap_correct I

/-- Emit the actual complete source bitmap and unary quota vector for any standard polynomial-time game family. -/
@[fun_prop] theorem ofInstance_polyTime {α : Type} {enc : α ↪ List Bool}
    {source : α → Push.Instance} {quotas : α → List ℕ}
    (hI : ComputableInPolyTime source enc Push.encoding)
    (hq : ComputableInPolyTime quotas enc (encList encUnary))
    (hlen : ∀ a, (quotas a).length = (source a).width)
    (hb : ∀ a, (quotas a).sum ≤ (holes (source a).initial).card) :
    ComputableInPolyTime (fun a => ofInstance (source a) (quotas a) (hlen a) (hb a))
      enc ColumnScan.Input.encoding :=
  (instanceData_polyTime.comp (hI.prod hq)).of_enc_eq
    (fun a => congrArg ColumnScan.encData (instanceData_eq (source a) (quotas a) (hlen a) (hb a)))

end PushPuzzle.Push.ColumnScan.Input
