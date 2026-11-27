/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.QuotasAccept
public import PushPush.WholeNormalize
import all Push.AcceptanceProgramRounds
import all PushPush.Doors.QuotasAccept

/-! Parked physical stocks pay the actual emitted word with whole hole components. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors

open PushFS (Cell Direction Adjacent)
open Push.AcceptanceProgram

variable {w h : ℕ}

private theorem emit_reads_whole (side : Direction) (requests : List (ℕ × ℕ))
    (E : Finset (Cell w h))
    (hblocked : ∀ a ∈ requests, ∀ p : Cell w h,
      side.lane p = a.1 → prefixRank side p = a.2 → p ∉ E) :
    WholeScan.Exec (.read side (emitReads side requests E).quotas : Round).instructions
      E (emitReads side requests E).remaining := by
  induction requests generalizing E with
  | nil => exact .nil _
  | cons a requests ih =>
    rcases a with ⟨lane, span⟩
    let front := (Push.Scan.lineCells (w := w) (h := h) side lane).take span
    have hh : WholeScan.Read side lane (E.filter fun p => p ∈ front).card E (E \ front.toFinset) := by
      refine ⟨read_prefix side lane span E, ?_⟩
      intro p hp q hq ha
      obtain ⟨hpE, hpnot⟩ := Finset.mem_sdiff.mp hp
      have hpf : p ∈ front := by
        by_contra hn
        exact hpnot (Finset.mem_sdiff.mpr ⟨hpE, by simpa only [List.mem_toFinset] using hn⟩)
      obtain ⟨hpl, hpr⟩ := (mem_line_prefix side lane span p).mp hpf
      have hql : side.lane q = lane := by
        have hl := ha.lane
        have hl' : side.lane q = side.lane p := by
          cases side <;> simpa only [Direction.opposite, Direction.lane] using hl
        exact hl'.trans hpl
      have hqr : span ≤ prefixRank side q := by
        by_contra hn
        exact (Finset.mem_sdiff.mp hq).2 (List.mem_toFinset.mpr
          ((mem_line_prefix side lane span q).mpr ⟨hql, by omega⟩))
      exact Layout.prefix_no_split side lane span E
        (hblocked _ (List.mem_cons_self ..)) (Finset.mem_sdiff.mp hq).1 hql hpr hqr ha
    exact .cons hh (ih (E \ front.toFinset) (by
      intro a ha p hl hp hh
      exact hblocked a (List.mem_cons_of_mem _ ha) p hl hp (Finset.mem_sdiff.mp hh).1))

private theorem emit_whole (stages : List Template) (E : Finset (Cell w h))
    (hreads : ∀ side lanes, Template.clear side lanes ∉ stages)
    (hblocked : ∀ side requests, Template.read side requests ∈ stages →
      ∀ a ∈ requests, ∀ p : Cell w h, side.lane p = a.1 → prefixRank side p = a.2 → p ∉ E) :
    WholeScan.Exec (instructions (Push.AcceptanceProgram.emit stages E).rounds) E
      (Push.AcceptanceProgram.emit stages E).remaining := by
  induction stages generalizing E with
  | nil => exact .nil _
  | cons stage stages ih =>
    cases stage with
    | clear side lanes => exact False.elim (hreads side lanes (List.mem_cons_self ..))
    | read side requests =>
      have hhead := emit_reads_whole side requests E (hblocked side requests (List.mem_cons_self ..))
      have htail := ih (emitReads side requests E).remaining
        (by intro d lanes hm; exact hreads d lanes (List.mem_cons_of_mem _ hm)) (by
          intro d req hm a ha p hl hp hh
          exact hblocked d req (List.mem_cons_of_mem _ hm) a ha p hl hp
            (emitReads_remaining_subset side requests E hh))
      exact hhead.append htail

namespace Source.Stock

variable {I : Instance}

/-- The first six concrete rounds have complete hole-run boundaries in every parked stock. -/
private theorem quotaPrefix_whole (S : Stock I)
    (hs : S.signal = atRow false I (layout false I).stop) :
    WholeScan.Exec (instructions (Push.AcceptanceProgram.emit
      ((layout false I).quotaTemplates.take 6) (layout false I).referenceHoles).rounds)
      (S.boxes false)ᶜ (Push.AcceptanceProgram.emit
        ((layout false I).quotaTemplates.take 6) (S.boxes false)ᶜ).remaining := by
  have hword := S.quotaPrefix_rounds_equal (terminal false I) hs rfl
  have href : ((terminal false I).boxes false)ᶜ = (layout false I).referenceHoles :=
    congrArg (fun boxes : Finset (Cell (layout false I).width (layout false I).height) => boxesᶜ)
      (terminal_boxes false I)
  rw [href] at hword
  rw [← hword]
  apply emit_whole
  · intro d lanes hm
    have hm := List.mem_of_mem_take hm
    simp only [Layout.quotaTemplates, List.mem_cons, List.not_mem_nil, or_false,
      reduceCtorEq] at hm
  · intro d requests hm a ha p hl hp
    exact S.quota_cut_blocked hs d requests (List.mem_of_mem_take hm) ha p hl hp

/-- A complete parked physical stock pays the original sparse word by whole runs. -/
theorem quotaProgram_whole (S : Stock I)
    (hs : S.signal = atRow false I (layout false I).stop) :
    WholeScan.Exec (instructions (layout false I).quotaProgram.rounds) (S.boxes false)ᶜ ∅ := by
  let L := layout false I
  let emission :=  Push.AcceptanceProgram.emit (L.quotaTemplates.take 6) L.referenceHoles
  let remaining := (Push.AcceptanceProgram.emit (L.quotaTemplates.take 6) (S.boxes false)ᶜ).remaining
  let requests := (emitReads .north L.finalRequests emission.remaining).quotas
  have hword : instructions (w := L.width) (h := L.height) L.quotaProgram.rounds =
      instructions emission.rounds ++ Push.Scan.lines .north requests := by
    rw [L.quotaProgram_decomposition, instructions, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Round.instructions,
      Push.Scan.lines, instructions]
    rfl
  have hprefix := S.quotaPrefix_whole hs
  have haccept := S.quotaProgram_accepts hs
  rw [hword, Push.Scan.eval_append, hprefix.eval, Option.bind_some] at haccept
  have hnd : (requests.map Prod.fst).Nodup := by
    rw [quota_lanes]
    simpa [Layout.finalRequests, List.map_map, Function.comp_def] using List.nodup_range (n := L.width)
  have hlast : WholeScan.Exec (Push.Scan.lines .north requests) remaining ∅ :=
    WholeScan.Exec.lines_of_eval hnd haccept (by simp [WholeScan.NoSplit])
  rw [hword]
  exact hprefix.append hlast

end Source.Stock
end PushPuzzle.PushPush.Doors
