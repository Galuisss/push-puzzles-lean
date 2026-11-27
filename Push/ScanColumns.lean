/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ReaderResidualOrder

/-! Independent bottom-column quotas and exact remainder comparison for cyclic reads. -/

public section
namespace PushPuzzle.Push.Scan

open PushFS ReaderResidual

variable {w h : ℕ}

/-- A same-direction family of static line quotas. -/
@[expose] def lines (side : Direction) (requests : List (ℕ × ℕ)) : List (Instruction w h) :=
  requests.map fun (lane, q) => .read side lane q

/-- A static list of column quotas, each read from its southern end. -/
@[expose] def columns (requests : List (ℕ × ℕ)) : List (Instruction w h) := lines .south requests

/-- Enumerate a quota vector in its literal lane order. -/
@[expose] def ofQuotas (quotas : List ℕ) : List (ℕ × ℕ) :=
  List.ofFn fun i : Fin quotas.length => (i.val, quotas[i])

theorem ofQuotas_nodup (quotas : List ℕ) : ((ofQuotas quotas).map Prod.fst).Nodup := by
  simp only [ofQuotas, List.map_ofFn, List.nodup_ofFn]
  intro i j he
  exact Fin.ext he

theorem ofQuotas_mem (quotas : List ℕ) (i : Fin quotas.length) :
    (i.val, quotas[i]) ∈ ofQuotas quotas := List.mem_ofFn.mpr ⟨i, rfl⟩

private theorem other_lane {side : Direction} {lane quota x : ℕ} {E F : Finset (Cell w h)}
    (hr : (Instruction.read side lane quota).eval E = some F) (hx : x ≠ lane) :
    (F.filter fun p => side.lane p = x) = E.filter fun p => side.lane p = x := by
  ext p
  simp only [Finset.mem_filter]
  by_cases hp : side.lane p = x
  · exact and_congr_left (fun _ => Instruction.read_outside hr (by omega))
  · simp only [hp, and_false]

private theorem other_column {col quota x : ℕ} {E F : Finset (Cell w h)}
    (hr : (Instruction.read .south col quota).eval E = some F) (hx : x ≠ col) :
    (F.filter fun p => p.1.val = x) = E.filter fun p => p.1.val = x := other_lane hr hx

/-- Distinct lines can pay their quotas from the original simultaneous line inventories. -/
theorem lines_accepts (side : Direction) (requests : List (ℕ × ℕ)) (E : Finset (Cell w h))
    (hn : (requests.map Prod.fst).Nodup)
    (hq : ∀ a ∈ requests, a.2 ≤ (E.filter fun p => side.lane p = a.1).card) :
    Accepts (lines side requests) E := by
  induction requests generalizing E with
  | nil => exact ⟨E, rfl⟩
  | cons a rest ih =>
    obtain ⟨G, ha⟩ := (Instruction.read_accepts_iff side a.1 a.2 E).mpr (hq a (List.mem_cons_self ..))
    obtain ⟨hnot, hrest⟩ := List.nodup_cons.mp hn
    obtain ⟨F, ht⟩ := ih G hrest (by
      intro b hb
      have hba : b.1 ≠ a.1 := by
        intro he
        exact hnot (List.mem_map.mpr ⟨b, hb, he⟩)
      rw [other_lane ha hba]
      exact hq b (List.mem_cons_of_mem a hb))
    exact ⟨F, by simp only [lines, List.map_cons, eval, ha, Option.bind_some]; exact ht⟩

private theorem outside_columns {requests : List (ℕ × ℕ)} {x : ℕ} {E F : Finset (Cell w h)}
    (hr : eval (columns requests) E = some F) (hx : ∀ a ∈ requests, a.1 ≠ x) :
    (F.filter fun p => p.1.val = x) = E.filter fun p => p.1.val = x := by
  induction requests generalizing E with
  | nil =>
    have he : E = F := by simpa only [columns, lines, List.map_nil, eval, Option.some.injEq] using hr
    rw [← he]
  | cons a rest ih =>
    simp only [columns, lines, List.map_cons, eval, Option.bind_eq_some_iff] at hr
    obtain ⟨G, ha, ht⟩ := hr
    exact (ih ht (fun b hb => hx b (List.mem_cons_of_mem a hb))).trans
      (other_column ha (Ne.symm (hx a (List.mem_cons_self ..))))

/-- Distinct columns can pay all their quotas from their original simultaneous inventories. -/
theorem columns_accepts (requests : List (ℕ × ℕ)) (E : Finset (Cell w h))
    (hn : (requests.map Prod.fst).Nodup)
    (hq : ∀ a ∈ requests, a.2 ≤ (E.filter fun p => p.1.val = a.1).card) :
    Accepts (columns requests) E := by
  exact lines_accepts .south requests E hn hq

/-- Every successful static column program retains a northern prefix in each original column. -/
theorem columns_remainder {requests : List (ℕ × ℕ)} {E F : Finset (Cell w h)}
    (hr : eval (columns requests) E = some F) : BottomRemainder E F := by
  induction requests generalizing E with
  | nil =>
    have he : E = F := Option.some.inj hr
    exact he ▸ BottomRemainder.refl E
  | cons a rest ih =>
    simp only [columns, lines, List.map_cons, eval, Option.bind_eq_some_iff] at hr
    obtain ⟨G, ha, ht⟩ := hr
    exact (bottom_read_remainder a.1 a.2 ha).trans (ih ht)

/-- Each distinct requested column loses exactly its prescribed quota. -/
theorem columns_card {requests : List (ℕ × ℕ)} {E F : Finset (Cell w h)}
    (hn : (requests.map Prod.fst).Nodup) (hr : eval (columns requests) E = some F)
    {a : ℕ × ℕ} (ha : a ∈ requests) :
    (F.filter fun p => p.1.val = a.1).card + a.2 = (E.filter fun p => p.1.val = a.1).card := by
  induction requests generalizing E with
  | nil => simp only [List.not_mem_nil] at ha
  | cons b rest ih =>
    simp only [columns, lines, List.map_cons, eval, Option.bind_eq_some_iff] at hr
    obtain ⟨G, hb, ht⟩ := hr
    obtain ⟨hnot, hrest⟩ := List.nodup_cons.mp hn
    rcases List.mem_cons.mp ha with rfl | ha
    · rw [outside_columns ht (fun c hc he => hnot (List.mem_map.mpr ⟨c, hc, he⟩))]
      exact Instruction.read_line_card hb
    · have hab : a.1 ≠ b.1 := by
        intro he
        exact hnot (List.mem_map.mpr ⟨a, ha, he⟩)
      have htail := ih hrest ht ha
      rwa [other_column hb hab] at htail

/-- Extra physical bottom consumption leaves a subset of the exact prescribed column read. -/
private theorem columns_dominates_remainder {requests : List (ℕ × ℕ)} {E F G : Finset (Cell w h)}
    (hn : (requests.map Prod.fst).Nodup) (hr : eval (columns requests) E = some G)
    (hF : BottomRemainder E F)
    (hcover : ∀ x : Fin w, ∃ q, (x.val, q) ∈ requests)
    (hpaid : ∀ a ∈ requests, (F.filter fun p => p.1.val = a.1).card + a.2 ≤
      (E.filter fun p => p.1.val = a.1).card) : F ⊆ G := by
  apply hF.subset_of_column_card (columns_remainder hr)
  intro x
  obtain ⟨q, hq⟩ := hcover x
  have hG := columns_card hn hr hq
  have hF := hpaid (x.val, q) hq
  have hcard : (F.filter fun p => p.1.val = x.val).card ≤
      (G.filter fun p => p.1.val = x.val).card := by
    change (G.filter fun p => p.1.val = x.val).card + q = _ at hG
    change (F.filter fun p => p.1.val = x.val).card + q ≤ _ at hF
    omega
  simpa only [Fin.ext_iff] using hcard

/-- Any payable suffix after extra physical consumption is payable after the exact static quotas. -/
theorem columns_suffix_lifts {requests : List (ℕ × ℕ)} {E F : Finset (Cell w h)}
    (hn : (requests.map Prod.fst).Nodup) (hF : BottomRemainder E F)
    (hcover : ∀ x : Fin w, ∃ q, (x.val, q) ∈ requests)
    (hpaid : ∀ a ∈ requests, (F.filter fun p => p.1.val = a.1).card + a.2 ≤
      (E.filter fun p => p.1.val = a.1).card)
    {suffix : List (Instruction w h)} (hsuffix : Accepts suffix F) :
    Accepts (columns requests ++ suffix) E := by
  have hquota : ∀ a ∈ requests, a.2 ≤ (E.filter fun p => p.1.val = a.1).card := by
    intro a ha
    have := hpaid a ha
    omega
  obtain ⟨G, hread⟩ := columns_accepts requests E hn hquota
  have hs := accepts_mono (columns_dominates_remainder hn hread hF hcover hpaid) hsuffix
  obtain ⟨H, hH⟩ := hs
  refine ⟨H, ?_⟩
  have happend : ∀ (program : List (Instruction w h)) (S : Finset (Cell w h)),
      eval (program ++ suffix) S = (eval program S).bind (eval suffix) := by
    intro program
    induction program with
    | nil => intro S; rfl
    | cons i rest ih =>
      intro S
      simp only [List.cons_append, eval, Option.bind_assoc, ih]
  rw [happend, hread, Option.bind_some]
  exact hH

end PushPuzzle.Push.Scan
