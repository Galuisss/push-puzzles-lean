/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.Basic
public import PushFS.Encoding

/-! A dense wall-free board and unary coordinates for the player target. -/

@[expose] public section
namespace PushPuzzle.Push

open Turing.MultiTapeTM

/-- Number of explicitly represented cells. -/
def Instance.area (I : Instance) : ℕ := I.width * I.height

namespace Encoding

/-- The existing dense board word and the destination coordinates. -/
def data (I : Instance) : PushFS.Instance × ℕ × ℕ :=
  (I.toStorage, I.target.1.val, I.target.2.val)

theorem data_injective : Function.Injective data := by
  rintro ⟨w, h, s, p, hp⟩ ⟨w', h', s', p', hp'⟩ heq
  have hw : w = w' := congrArg (fun d => d.1.width) heq
  cases hw
  have hh : h = h' := congrArg (fun d => d.1.height) heq
  cases hh
  have hr := congrArg (fun d => (PushFS.Encoding.data d.1).rows) heq
  have hs : s = s' := (PushFS.Encoding.rows_injective hr).2
  cases hs
  have hx : p.1 = p'.1 := Fin.ext (congrArg (fun d => d.2.1) heq)
  have hy : p.2 = p'.2 := Fin.ext (congrArg (fun d => d.2.2) heq)
  have hpp : p = p' := Prod.ext hx hy
  cases hpp
  rfl

end Encoding

/-- A fixed explicit encoding with a dense board and a unary destination. -/
def encoding : Instance ↪ List Bool :=
  (⟨Encoding.data, Encoding.data_injective⟩ : Instance ↪ PushFS.Instance × ℕ × ℕ).trans
    (encPair PushFS.encoding (encPair encUnary encUnary))

end PushPuzzle.Push
