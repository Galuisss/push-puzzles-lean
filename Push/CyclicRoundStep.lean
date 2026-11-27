/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicRounds

/-! One actual compact read round is removed while preserving the complete source language and budget. -/

public section
namespace PushPuzzle.Push.Cyclic

open PushFS PushS AcceptanceProgram

/-- The next row vector is the exact dense normalization of the original sparse west requests. -/
@[expose] def rowQuotas (r : ColumnScan.Input) (requests : List (ℕ × ℕ)) : List ℕ :=
  Scan.denseQuotas .west r.width r.height requests

theorem rowQuotas_length (r : ColumnScan.Input) (requests : List (ℕ × ℕ)) :
    (rowQuotas r requests).length = r.height := Scan.denseQuotas_length ..

/-- Every complete source-program budget includes the exact next dense row vector. -/
theorem rowQuotas_budget (r : ColumnScan.Input) (requests : List (ℕ × ℕ)) (rest : List Round)
    (hreq : ∀ a ∈ requests, a.1 < r.height) (hb : Budget r (.read .west requests :: rest)) :
    (rowQuotas r requests).sum ≤ r.sourceHoles := by
  have hs := Scan.denseQuotas_sum .west r.width r.height requests hreq
  change r.quotas.sum + Scan.quota
    (Scan.lines .west requests ++ instructions (w := r.width) (h := r.height) rest) ≤ r.sourceHoles at hb
  rw [Scan.quota_append, Scan.lines_quota] at hb
  change (Scan.denseQuotas .west r.width r.height requests).sum ≤ _
  rw [hs]
  omega

private theorem sparse_west_accepts (r : ColumnScan.Input) (requests : List (ℕ × ℕ))
    (hreq : ∀ a ∈ requests, a.1 < r.height) (rest : List Round)
    (E : Finset (Cell r.width r.height)) :
    Scan.Accepts (Scan.columns (Scan.ofQuotas r.quotas) ++
      instructions (.read .west requests :: rest)) E ↔
    Scan.Accepts (Scan.columns (Scan.ofQuotas r.quotas) ++
      Scan.lines .west (Scan.ofQuotas (rowQuotas r requests)) ++ instructions rest) E := by
  change Scan.Accepts (Scan.columns (Scan.ofQuotas r.quotas) ++
    (Scan.lines .west requests ++ instructions rest)) E ↔ _
  unfold Scan.Accepts
  rw [List.append_assoc]
  simp only [Scan.eval_append, Scan.eval_normalize .west r.width r.height requests hreq, rowQuotas]

/-- The actual next reader input preserves the complete corner language of every future compact program. -/
theorem round_step_language_iff (r : ColumnScan.Input) (requests : List (ℕ × ℕ))
    (hreq : ∀ a ∈ requests, a.1 < r.height) (rest : List Round)
    (hbound : ∀ i ∈ instructions rest, SourceBounded r i)
    (hb : (rowQuotas r requests).sum ≤ r.sourceHoles) :
    Language (nextInput r (rowQuotas r requests) (rowQuotas_length r requests) hb)
      (nextRounds r rest) ↔ Language r (.read .west requests :: rest) := by
  let rows := rowQuotas r requests
  let r' := nextInput r rows (rowQuotas_length r requests) hb
  have he := next_peeling_iff r rows (rowQuotas_length r requests) (instructions rest) hbound
  constructor
  · rintro ⟨t, hr, hp, ha⟩
    have hreach := hr.reboard (B' := (nextSource r).board) rfl
    rw [nextInput_initial] at hreach
    have hcorner : t.player = (nextSource r).target :=
      hp.trans (nextInput_corner r rows (rowQuotas_length r requests) hb)
    have ha' : Scan.Accepts (Scan.columns (Scan.ofQuotas (nextQuotas r rows)) ++
        nextTail r (instructions rest)) (holes t) :=
      (nextRounds_accepts_prefix r rest _ _).mp ha
    obtain ⟨s, hs, hsp, hsa⟩ := he.mp ⟨t, hreach, hcorner, ha'⟩
    exact ⟨s, hs, hsp, (sparse_west_accepts r requests hreq rest _).mpr hsa⟩
  · rintro ⟨s, hs, hsp, hsa⟩
    obtain ⟨t, ht, htp, hta⟩ := he.mpr
      ⟨s, hs, hsp, (sparse_west_accepts r requests hreq rest _).mp hsa⟩
    have hreach : Reachable r'.sourceBoard none r'.initial.toState t := by
      rw [nextInput_initial]
      exact ht.reboard rfl
    have hcorner : t.player = r'.sourceCorner :=
      htp.trans (nextInput_corner r rows (rowQuotas_length r requests) hb).symm
    refine ⟨t, hreach, hcorner, ?_⟩
    exact (nextRounds_accepts_prefix r rest _ _).mpr hta

end PushPuzzle.Push.Cyclic
