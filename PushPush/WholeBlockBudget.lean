/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.WholeBlockConstruct
public import PushPush.WholeDenormalize
public import Push.CyclicEraseInventoryProgram

/-! Full source budgets remove every parallel-block overpayment and recover the sparse word. -/

@[expose] public section
namespace PushPuzzle.PushPush

open PushFS (Cell Direction)
open Push.AcceptanceProgram

variable {w h : ℕ}

private theorem WholeScan.LooseExec.exact_of_card {program : List (Push.Scan.Instruction w h)}
    {E F : Finset (Cell w h)} (H : WholeScan.LooseExec program E F)
    (hq : F.card + Push.Scan.quota program = E.card) : WholeScan.Exec program E F := by
  induction H with
  | nil => exact .nil _
  | @cons side lane quota actual program E F G paid head tail ih =>
    have hc := head.card
    have hb := tail.budget_bound
    have hq' : G.card + (quota + Push.Scan.quota program) = E.card := by
      simpa only [Push.Scan.quota, List.map_cons, List.sum_cons, Push.Scan.Instruction.quota] using hq
    have he : actual = quota := by omega
    have ht : G.card + Push.Scan.quota program = F.card := by omega
    exact .cons (he ▸ head) (ih ht)

namespace WholeBlocks

private theorem Block.budget_bound {side : Direction} {requests : List (ℕ × ℕ)}
    {E F : Finset (Cell w h)} (H : Block side requests E F)
    (hbound : ∀ a ∈ requests, a.1 < Push.Scan.laneCount side w h) :
    F.card + (requests.map Prod.snd).sum ≤ E.card := by
  have hc := WholeScan.LooseExec.budget_bound H
  rw [Push.Scan.dense_lines_quota, Push.Scan.denseQuotas_sum side w h requests hbound] at hc
  exact hc

private theorem Block.exact_of_card {side : Direction} {requests : List (ℕ × ℕ)}
    {E F : Finset (Cell w h)} (H : Block side requests E F)
    (hbound : ∀ a ∈ requests, a.1 < Push.Scan.laneCount side w h)
    (hnd : ((requests.filter fun a => a.2 ≠ 0).map Prod.fst).Nodup)
    (hq : F.card + (requests.map Prod.snd).sum = E.card) :
    WholeScan.Exec (Push.Scan.lines side requests) E F := by
  apply WholeScan.Exec.denormalize (WholeScan.LooseExec.exact_of_card H ?_) hbound hnd
  rw [Push.Scan.dense_lines_quota, Push.Scan.denseQuotas_sum side w h requests hbound]
  exact hq

private theorem Exec.budget_bound {rounds : List Round} {E F : Finset (Cell w h)}
    (H : Exec rounds E F) (hbound : Push.Scan.Bounded (instructions (w := w) (h := h) rounds)) :
    F.card + Push.Scan.quota (instructions (w := w) (h := h) rounds) ≤ E.card := by
  induction H with
  | nil => simp [instructions, Push.Scan.quota]
  | @cons side requests rounds E F G head tail ih =>
    change Push.Scan.Bounded (Push.Scan.lines side requests ++ instructions rounds) at hbound
    have hhead := head.budget_bound (fun a ha => hbound _
      (List.mem_append_left _ (List.mem_map.mpr ⟨a, ha, rfl⟩)))
    have htail := ih (fun i hi => hbound i (List.mem_append_right _ hi))
    change G.card + Push.Scan.quota (Push.Scan.lines side requests ++ instructions rounds) ≤ E.card
    rw [Push.Scan.quota_append, Push.Scan.lines_quota]
    omega

/-- A complete finite-hole budget forces every physical parallel block to pay
its exact sparse quota, and all original source holes are consumed. -/
theorem Exec.exact_of_budget {rounds : List Round} {E F : Finset (Cell w h)}
    (H : Exec rounds E F) (hbound : Push.Scan.Bounded (instructions (w := w) (h := h) rounds))
    (hpositive : ∀ side requests, Round.read side requests ∈ rounds →
      ((requests.filter fun a => a.2 ≠ 0).map Prod.fst).Nodup)
    (hq : Push.Scan.quota (instructions (w := w) (h := h) rounds) = E.card) :
    WholeScan.Exec (instructions (w := w) (h := h) rounds) E F ∧ F = ∅ := by
  induction H with
  | nil E =>
    have he : E = ∅ := by
      apply Finset.card_eq_zero.mp
      simpa only [instructions, List.flatMap_nil, Push.Scan.quota, List.map_nil, List.sum_nil] using hq.symm
    exact ⟨.nil _, he⟩
  | @cons side requests rounds E F G head tail ih =>
    change Push.Scan.Bounded (Push.Scan.lines side requests ++ instructions rounds) at hbound
    have hheadBound : ∀ a ∈ requests, a.1 < Push.Scan.laneCount side w h := fun a ha =>
      hbound _ (List.mem_append_left _ (List.mem_map.mpr ⟨a, ha, rfl⟩))
    have htailBound : Push.Scan.Bounded (instructions (w := w) (h := h) rounds) :=
      fun i hi => hbound i (List.mem_append_right _ hi)
    have hb := head.budget_bound hheadBound
    have ht := tail.budget_bound htailBound
    have hq' : (requests.map Prod.snd).sum + Push.Scan.quota (instructions (w := w) (h := h) rounds) = E.card := by
      change Push.Scan.quota (Push.Scan.lines side requests ++ instructions rounds) = E.card at hq
      rwa [Push.Scan.quota_append, Push.Scan.lines_quota] at hq
    have hheadExact : F.card + (requests.map Prod.snd).sum = E.card := by omega
    have htailExact : Push.Scan.quota (instructions (w := w) (h := h) rounds) = F.card := by omega
    have hh := head.exact_of_card hheadBound
      (hpositive side requests (List.mem_cons_self ..)) hheadExact
    obtain ⟨hrest, hzero⟩ := ih htailBound
      (fun d rs hr => hpositive d rs (List.mem_cons_of_mem _ hr)) htailExact
    exact ⟨hh.append hrest, hzero⟩

end WholeBlocks
end PushPuzzle.PushPush
