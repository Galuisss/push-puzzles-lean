/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPushF.Basic
public import PushFS.Encoding

/-! Dense fixed-wall boards with unary player destination coordinates. -/

@[expose] public section
namespace PushPuzzle.PushPushF

open Turing.MultiTapeTM

/-- Number of explicitly represented cells. -/
def Instance.area (I : Instance) : ℕ := I.width * I.height

namespace Encoding

/-- The dense board word and the destination coordinates. -/
def data (I : Instance) : PushFS.Instance × ℕ × ℕ :=
  (I.toStorage, I.target.1.val, I.target.2.val)

theorem data_injective : Function.Injective data := by
  rintro ⟨w, h, walls, s, p, hv, hp⟩ ⟨w', h', walls', s', p', hv', hp'⟩ heq
  have hw : w = w' := congrArg (fun d => d.1.width) heq
  cases hw
  have hh : h = h' := congrArg (fun d => d.1.height) heq
  cases hh
  have hr := congrArg (fun d => (PushFS.Encoding.data d.1).rows) heq
  obtain ⟨hb, hs⟩ := PushFS.Encoding.rows_injective hr
  have hwall : walls = walls' := congrArg PushFS.Board.walls hb
  cases hwall
  cases hs
  have hx : p.1 = p'.1 := Fin.ext (congrArg (fun d => d.2.1) heq)
  have hy : p.2 = p'.2 := Fin.ext (congrArg (fun d => d.2.2) heq)
  have hpp : p = p' := Prod.ext hx hy
  cases hpp
  rfl

end Encoding

/-- Explicit dense cells and unary destination coordinates. -/
def encoding : Instance ↪ List Bool :=
  (⟨Encoding.data, Encoding.data_injective⟩ : Instance ↪ PushFS.Instance × ℕ × ℕ).trans
    (encPair PushFS.encoding (encPair encUnary encUnary))

end PushPuzzle.PushPushF
