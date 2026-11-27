/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicEraseRoundStep
public import Push.CyclicErasePolyTime
public import Push.CyclicRoundPolyTime

/-! Standard polynomial-time emission of the actual compact erase replacement and next reader input. -/

public section
namespace PushPuzzle.Push.CyclicErase

open PushFS PushS AcceptanceProgram Turing.MultiTapeTM
open scoped PushPuzzle.Push.AcceptanceProgram PushPuzzle.Push.ColumnScan

private theorem width_polyTime : ComputableInPolyTime ColumnScan.Input.width ColumnScan.Input.encoding encUnary :=
  ColumnScan.encData_width_polyTime ColumnScan.Input.data_polyTime

private theorem height_polyTime : ComputableInPolyTime ColumnScan.Input.height ColumnScan.Input.encoding encUnary :=
  ColumnScan.encData_height_polyTime ColumnScan.Input.data_polyTime

private theorem next_width_polyTime : ComputableInPolyTime
    (fun r => (nextSource r).width) ColumnScan.Input.encoding encUnary :=
  PushFS.Machine.width_polyTime.comp (Push.Machine.toStorage_polyTime.comp nextSource_polyTime)

/-- Emit the real next first vector, charging only data rows and explicitly padding every other lane with zero. -/
@[fun_prop] theorem firstQuotas_polyTime {α : Type} {enc : α ↪ List Bool}
    {reader : α → ColumnScan.Input} {rows : α → List ℕ}
    (hr : ComputableInPolyTime reader enc ColumnScan.Input.encoding)
    (hq : ComputableInPolyTime rows enc (encList encUnary)) :
    ComputableInPolyTime (fun a => firstQuotas (reader a) (rows a)) enc (encList encUnary) := by
  have hw := next_width_polyTime.comp hr
  have hh := height_polyTime.comp hr
  unfold firstQuotas
  fun_prop

/-- The complete actual turned source and padded first vector uniformly emit a valid next reader recipe. -/
@[fun_prop] theorem nextInput_polyTime {α : Type} {enc : α ↪ List Bool}
    {reader : α → ColumnScan.Input} {rows : α → List ℕ}
    (hr : ComputableInPolyTime reader enc ColumnScan.Input.encoding)
    (hq : ComputableInPolyTime rows enc (encList encUnary))
    (hlen : ∀ a, (rows a).length = (reader a).height)
    (hb : ∀ a, (rows a).sum ≤ (reader a).sourceHoles) :
    ComputableInPolyTime (fun a => nextInput (reader a) (rows a) (hlen a) (hb a))
      enc ColumnScan.Input.encoding :=
  ColumnScan.Input.ofInstance_polyTime (nextSource_polyTime.comp hr) (firstQuotas_polyTime hr hq)
    (fun a => firstQuotas_length (reader a) (rows a) (hlen a))
    (fun a => firstQuotas_budget (reader a) (rows a) (hb a))

private def boundedLanes (p : ColumnScan.Input × Finset ℕ) : Finset ℕ :=
  p.2.filter fun lane => lane < p.1.width

private theorem eraseRequests_total (r : ColumnScan.Input) (lanes : Finset ℕ) :
    eraseRequests r (selectColumns r lanes) =
      ((boundedLanes (r, lanes)).sort (· ≤ ·)).map (fun lane => (lane + 2, r.height)) := by
  have hb : ∀ lane ∈ boundedLanes (r, lanes), lane < r.width :=
    fun _ hm => (Finset.mem_filter.mp hm).2
  have he := eraseRequests_select r (boundedLanes (r, lanes)) hb
  have hs : selectColumns r (boundedLanes (r, lanes)) = selectColumns r lanes := by
    ext x
    simp [selectColumns, boundedLanes]
  rw [hs] at he
  exact he

/-- Raw clear sets emit exactly their actually selected finite source columns, using their canonical unary lane words. -/
@[fun_prop] theorem eraseRequests_select_polyTime : ComputableInPolyTime
    (fun p : ColumnScan.Input × Finset ℕ => eraseRequests p.1 (selectColumns p.1 p.2))
    (encPair ColumnScan.Input.encoding encLaneSet) Scan.encRequests := by
  have hw := width_polyTime
  have hh := height_polyTime
  have hk : ComputableInPolyTime
      (fun p : (ColumnScan.Input × Finset ℕ) × ℕ => decide (p.2 < p.1.1.width))
      (encPair (encPair ColumnScan.Input.encoding encLaneSet) encUnary) encBool := by fun_prop
  have hf : ComputableInPolyTime boundedLanes (encPair ColumnScan.Input.encoding encLaneSet) encLaneSet :=
    laneSet_filterDecide_polyTime (ComputableInPolyTime.snd _ _) hk
  have hs := laneSet_sort_polyTime.comp hf
  have hm : ComputableInPolyTime
      (fun p : ColumnScan.Input × Finset ℕ =>
        ((boundedLanes p).sort (· ≤ ·)).map (fun lane => (lane + 2, p.1.height)))
      (encPair ColumnScan.Input.encoding encLaneSet) Scan.encRequests := by
    unfold Scan.encRequests
    apply ComputableInPolyTime.mapWithInput hs
    fun_prop
  exact hm.of_enc_eq (fun p => congrArg Scan.encRequests (eraseRequests_total p.1 p.2))

private theorem auxiliaryRows_polyTime : ComputableInPolyTime Cyclic.auxiliaryRows
    ColumnScan.Input.encoding (encList encUnary) := by
  have hh := height_polyTime
  have hH : ComputableInPolyTime (fun r => (Cyclic.wideReader r).outputHeight)
      ColumnScan.Input.encoding encUnary :=
    ((ColumnScan.Data.outputHeight_polyTime.comp ColumnScan.Input.data_polyTime).comp Cyclic.wideReader_polyTime).of_enc_eq
      (fun r => congrArg encUnary (ColumnScan.Input.data_outputHeight (Cyclic.wideReader r)).symm)
  unfold Cyclic.auxiliaryRows
  fun_prop

private theorem dock_width_polyTime : ComputableInPolyTime (fun r => (eraseDock r).outputWidth)
    ColumnScan.Input.encoding encUnary :=
  PushFS.Machine.width_polyTime.comp
    (Push.Machine.toStorage_polyTime.comp (CornerDock.Input.compile_polyTime.comp eraseDock_polyTime))

private def prefixRounds (width : ℕ) (erase cleanup : List (ℕ × ℕ)) : List Round :=
  [.read .west (Cyclic.turnRequests width .north erase), .read .north [], .read .east [],
    .read .south cleanup, .read .west []]

private theorem prefixRounds_polyTime : ComputableInPolyTime
    (fun p : ℕ × List (ℕ × ℕ) × List (ℕ × ℕ) => prefixRounds p.1 p.2.1 p.2.2)
    (encPair encUnary (encPair Scan.encRequests Scan.encRequests)) encRounds := by
  unfold prefixRounds encRounds
  fun_prop

/-- Emit all five actual read blocks and the complete transported future program from their real source fields. -/
@[fun_prop] theorem suffixRounds_polyTime {α : Type} {enc : α ↪ List Bool}
    {reader : α → ColumnScan.Input} {lanes : α → Finset ℕ} {tail : α → List Round}
    (hr : ComputableInPolyTime reader enc ColumnScan.Input.encoding)
    (hl : ComputableInPolyTime lanes enc encLaneSet)
    (ht : ComputableInPolyTime tail enc encRounds) :
    ComputableInPolyTime (fun a => suffixRounds (reader a) (selectColumns (reader a) (lanes a)) (tail a))
      enc encRounds := by
  have hw : ComputableInPolyTime (fun a => (reader a).width) enc encUnary := width_polyTime.comp hr
  have hd : ComputableInPolyTime (fun a => (eraseDock (reader a)).outputWidth) enc encUnary :=
    dock_width_polyTime.comp hr
  have heRaw := eraseRequests_select_polyTime.comp (hr.prod hl)
  have he : ComputableInPolyTime
      (fun a => eraseRequests (reader a) (selectColumns (reader a) (lanes a))) enc Scan.encRequests :=
    heRaw.of_enc_eq (by intro a; rfl)
  have ha : ComputableInPolyTime (fun a => Cyclic.auxiliaryRows (reader a)) enc (encList encUnary) :=
    auxiliaryRows_polyTime.comp hr
  have hcleanup : ComputableInPolyTime
      (fun a => (Cyclic.auxiliaryRows (reader a)).map (fun lane => (lane, (reader a).width + 2)))
      enc Scan.encRequests := by
    unfold Scan.encRequests
    apply ComputableInPolyTime.mapWithInput ha
    exact (ComputableInPolyTime.snd enc encUnary).prod
      (ComputableInPolyTime.unary_add' (hw.comp (ComputableInPolyTime.fst enc encUnary))
        (ComputableInPolyTime.const 2))
  have hpRaw := prefixRounds_polyTime.comp (hd.prod (he.prod hcleanup))
  have hp : ComputableInPolyTime (fun a => prefixRounds (eraseDock (reader a)).outputWidth
      (eraseRequests (reader a) (selectColumns (reader a) (lanes a)))
      ((Cyclic.auxiliaryRows (reader a)).map fun lane => (lane, (reader a).width + 2))) enc encRounds :=
    hpRaw.of_enc_eq (by intro a; rfl)
  have htRaw := Cyclic.nextRounds_polyTime (asReader_polyTime.comp hr) ht
  have htail : ComputableInPolyTime (fun a => Cyclic.nextRounds (asReader (reader a)) (tail a)) enc encRounds :=
    htRaw.of_enc_eq (by intro a; rfl)
  have h : ComputableInPolyTime (fun a => prefixRounds (eraseDock (reader a)).outputWidth
      (eraseRequests (reader a) (selectColumns (reader a) (lanes a)))
      ((Cyclic.auxiliaryRows (reader a)).map fun lane => (lane, (reader a).width + 2)) ++
      Cyclic.nextRounds (asReader (reader a)) (tail a)) enc encRounds := by
    unfold encRounds at *
    fun_prop
  exact h.of_enc_eq (by intro a; rfl)

end PushPuzzle.Push.CyclicErase
