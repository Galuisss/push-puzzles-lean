/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicReaderBase
public import Push.CyclicNextPolyTime

/-! Standard polynomial-time composition for the actual one- and two-round reader base families. -/

public section
namespace PushPuzzle.Push.Cyclic

open Turing.MultiTapeTM
open scoped PushPuzzle.Push.ColumnScan

/-- Actual source and sparse request families uniformly emit their exact dense row vector. -/
@[fun_prop] theorem rowQuotas_family_polyTime {α : Type} {enc : α ↪ List Bool}
    {reader : α → ColumnScan.Input} {requests : α → List (ℕ × ℕ)}
    (hr : ComputableInPolyTime reader enc ColumnScan.Input.encoding)
    (hq : ComputableInPolyTime requests enc Scan.encRequests) :
    ComputableInPolyTime (fun a => rowQuotas (reader a) (requests a)) enc (encList encUnary) := by
  have hw : ComputableInPolyTime (fun a => (reader a).width) enc encUnary :=
    ColumnScan.encData_width_polyTime (ColumnScan.Input.data_polyTime.comp hr)
  have hh : ComputableInPolyTime (fun a => (reader a).height) enc encUnary :=
    ColumnScan.encData_height_polyTime (ColumnScan.Input.data_polyTime.comp hr)
  have hargs : ComputableInPolyTime
      (fun a => ((reader a).width, (reader a).height, requests a)) enc Scan.encDenseInput := by
    unfold Scan.encDenseInput
    fun_prop
  exact ((Scan.denseQuotas_polyTime .west).comp hargs).of_enc_eq (by intro a; rfl)

@[fun_prop] theorem rowQuotas_polyTime : ComputableInPolyTime
    (fun p : ColumnScan.Input × List (ℕ × ℕ) => rowQuotas p.1 p.2)
    (encPair ColumnScan.Input.encoding Scan.encRequests) (encList encUnary) :=
  rowQuotas_family_polyTime (ComputableInPolyTime.fst _ _) (ComputableInPolyTime.snd _ _)

/-- The no-future-block base family emits the literal current reader instance. -/
@[fun_prop] theorem reader_base_nil_polyTime {α : Type} {enc : α ↪ List Bool}
    {reader : α → ColumnScan.Input} (hr : ComputableInPolyTime reader enc ColumnScan.Input.encoding) :
    ComputableInPolyTime (fun a => (reader a).compile) enc Push.encoding :=
  ColumnScan.Input.compile_polyTime.comp hr

/-- A bounded next-vector family gives the complete actual second reader input, including its dense bitmap. -/
@[fun_prop] theorem reader_base_west_input_polyTime {α : Type} {enc : α ↪ List Bool}
    {reader : α → ColumnScan.Input} {requests : α → List (ℕ × ℕ)}
    (hr : ComputableInPolyTime reader enc ColumnScan.Input.encoding)
    (hq : ComputableInPolyTime requests enc Scan.encRequests)
    (hb : ∀ a, (rowQuotas (reader a) (requests a)).sum ≤ (reader a).sourceHoles) :
    ComputableInPolyTime
      (fun a => nextInput (reader a) (rowQuotas (reader a) (requests a))
        (rowQuotas_length (reader a) (requests a)) (hb a)) enc ColumnScan.Input.encoding :=
  nextInput_polyTime hr (rowQuotas_family_polyTime hr hq) (fun a => rowQuotas_length (reader a) (requests a)) hb

/-- The two-round base family emits the complete actual player-target game in standard polynomial time. -/
@[fun_prop] theorem reader_base_west_polyTime {α : Type} {enc : α ↪ List Bool}
    {reader : α → ColumnScan.Input} {requests : α → List (ℕ × ℕ)}
    (hr : ComputableInPolyTime reader enc ColumnScan.Input.encoding)
    (hq : ComputableInPolyTime requests enc Scan.encRequests)
    (hb : ∀ a, (rowQuotas (reader a) (requests a)).sum ≤ (reader a).sourceHoles) :
    ComputableInPolyTime
      (fun a => (nextInput (reader a) (rowQuotas (reader a) (requests a))
        (rowQuotas_length (reader a) (requests a)) (hb a)).compile) enc Push.encoding :=
  ColumnScan.Input.compile_polyTime.comp (reader_base_west_input_polyTime hr hq hb)

end PushPuzzle.Push.Cyclic
