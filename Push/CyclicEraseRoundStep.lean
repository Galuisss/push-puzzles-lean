/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicEraseRounds
public import Push.ColumnScanInput
import all Push.CyclicRoundStep
import all Push.CyclicErasePeelingCorrectness
import all Push.CyclicEraseRounds

/-! The actual compact erase replacement is a valid next reader with the same complete corner language. -/

@[expose] public section
namespace PushPuzzle.Push.CyclicErase

open PushFS PushS AcceptanceProgram

theorem firstQuotas_budget (r : ColumnScan.Input) (rows : List ℕ) (hb : rows.sum ≤ r.sourceHoles) :
    (firstQuotas r rows).sum ≤ (holes (nextSource r).initial).card := by
  have hinv := Cyclic.initial_inventory_lower (asReader r)
  rw [firstQuotas_sum]
  exact hb.trans ((Nat.le_add_right _ _).trans hinv)

/-- A live reader on the actual turned backed source, initially charging only data rows. -/
def nextInput (r : ColumnScan.Input) (rows : List ℕ)
    (hlen : rows.length = r.height) (hb : rows.sum ≤ r.sourceHoles) : ColumnScan.Input :=
  ColumnScan.Input.ofInstance (nextSource r) (firstQuotas r rows) (firstQuotas_length r rows hlen)
    (firstQuotas_budget r rows hb)

/-- Replacing a source-column clear by the literal six-read expansion preserves the full compact language. -/
theorem round_step_language_iff (r : ColumnScan.Input) (hk : r.height ≤ r.quota)
    (requests : List (ℕ × ℕ)) (hreq : ∀ a ∈ requests, a.1 < r.height)
    (lanes : Finset ℕ) (hlanes : ∀ lane ∈ lanes, lane < r.width) (rest : List Round)
    (hbound : ∀ i ∈ instructions rest, Cyclic.SourceBounded r i)
    (hb : (Cyclic.rowQuotas r requests).sum ≤ r.sourceHoles) :
    Cyclic.Language (nextInput r (Cyclic.rowQuotas r requests) (Cyclic.rowQuotas_length r requests) hb)
      (suffixRounds r (selectColumns r lanes) rest) ↔
    Cyclic.Language r (.read .west requests :: .clear .north lanes :: rest) := by
  let rows := Cyclic.rowQuotas r requests
  let r' := nextInput r rows (Cyclic.rowQuotas_length r requests) hb
  have hcorner : r'.sourceCorner = (nextSource r).target :=
    ColumnScan.Input.ofInstance_corner _ _ _ _
      (Cyclic.nextSource_target (asReader r)).1 (Cyclic.nextSource_target (asReader r)).2
  have hi : r'.initial.toState = (nextSource r).initial := ColumnScan.Input.ofInstance_initial ..
  have he := next_peeling_iff r hk rows (Cyclic.rowQuotas_length r requests)
    (selectColumns r lanes) (instructions rest) (fun i hi =>
      (Cyclic.sourceBounded_iff_bounded (asReader r) i).mpr
        ((Cyclic.sourceBounded_iff_bounded r i).mp (hbound i hi)))
  rw [clearColumns_select r lanes hlanes] at he
  constructor
  · rintro ⟨t, ht, hp, ha⟩
    have hreach : Reachable (nextSource r).board none (nextSource r).initial t := by
      rw [← hi]
      exact ht.reboard rfl
    have hp' := hp.trans hcorner
    have ha' := (suffixRounds_accepts_iff r rows (selectColumns r lanes) rest _).mp ha
    obtain ⟨s, hs, hsp, hsa⟩ := he.mp ⟨t, hreach, hp', ha'⟩
    refine ⟨s, hs, hsp, ?_⟩
    apply (Cyclic.sparse_west_accepts r requests hreq (.clear .north lanes :: rest) _).mpr
    simpa only [instructions, List.flatMap_cons, Round.instructions, List.singleton_append,
      List.append_assoc] using hsa
  · rintro ⟨s, hs, hsp, hsa⟩
    have ha' := (Cyclic.sparse_west_accepts r requests hreq (.clear .north lanes :: rest) _).mp hsa
    have hfull : Scan.Accepts (Scan.columns (Scan.ofQuotas r.quotas) ++
        Scan.lines .west (Scan.ofQuotas rows) ++ [.clear .north lanes] ++ instructions rest) (holes s) := by
      simpa only [instructions, List.flatMap_cons, Round.instructions, List.singleton_append,
        List.append_assoc] using ha'
    obtain ⟨t, ht, hp, ha⟩ := he.mpr ⟨s, hs, hsp, hfull⟩
    refine ⟨t, ?_, hp.trans hcorner.symm, ?_⟩
    · have ht' := ht.reboard (B' := r'.sourceBoard) rfl
      rwa [← hi] at ht'
    · exact (suffixRounds_accepts_iff r rows (selectColumns r lanes) rest _).mpr ha

end PushPuzzle.Push.CyclicErase
