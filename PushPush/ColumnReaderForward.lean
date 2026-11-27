/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.ColumnReaderSeal
public import PushPush.ReadSelected
public import Push.ColumnScanForwardColumns
import all Push.ColumnScanForwardColumns
import all Push.ColumnScan

/-! Whole-run source-column reads along the actual committed reader route. -/

@[expose] public section
namespace PushPuzzle.PushPush.ColumnReader

open PushFS (Cell State)
open Reader

variable (r : Push.ColumnScan.Input)

/-- The original holes in one embedded source column. -/
def sourceColumn (i : Fin r.width) : Finset (Cell r.outputWidth r.outputHeight) :=
  r.empty.filter fun q => q.1.val = i.val ∧ q.2.val < r.height

/-- The current holes in one embedded source column. -/
def remainingColumn (s : State r.outputWidth r.outputHeight) (i : Fin r.width) :
    Finset (Cell r.outputWidth r.outputHeight) :=
  s.boxesᶜ.filter fun q => q.1.val = i.val ∧ q.2.val < r.height

theorem sourceColumn_eq (i : Fin r.width) :
    sourceColumn r i = (r.columnSources i).image r.embed := by
  ext q
  constructor
  · intro hq
    obtain ⟨hq, hx, hy⟩ := Finset.mem_filter.mp hq
    let p : Cell r.width r.height := (⟨q.1.val, by omega⟩, ⟨q.2.val, hy⟩)
    have he : r.embed p = q := by apply Prod.ext <;> apply Fin.ext <;> rfl
    refine Finset.mem_image.mpr ⟨p, ?_, he⟩
    apply Finset.mem_filter.mpr
    exact ⟨(r.embed_mem_empty p).mp (he ▸ hq), Fin.ext hx⟩
  · intro hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hp, hx⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨(r.embed_mem_empty p).mpr hp,
      congrArg Fin.val hx, p.2.isLt⟩

private theorem sourceColumn_card_le (i : Fin r.width) :
    (sourceColumn r i).card ≤ r.sourceHoles := by
  rw [sourceColumn_eq, Finset.card_image_of_injective _ r.embed_injective]
  exact Finset.card_le_card (Finset.filter_subset _ _)

private theorem remainingColumn_eq_data (s : State r.outputWidth r.outputHeight) (i : Fin r.width)
    (hx : s.player.1.val = i.val) : remainingColumn r s i = northData s r.height := by
  ext q
  simp only [remainingColumn, northData, Finset.mem_filter, Fin.ext_iff, hx]

theorem data_eq_sourceColumn (s : State r.outputWidth r.outputHeight) (i : Fin r.width)
    (hx : s.player.1.val = i.val)
    (hc : ∀ p : Cell r.outputWidth r.outputHeight, p.1.val = i.val →
      (p ∉ s.boxes ↔ p ∈ r.empty)) : northData s r.height = sourceColumn r i := by
  rw [← remainingColumn_eq_data r s i hx]
  ext p
  simp only [remainingColumn, sourceColumn, Finset.mem_filter, Finset.mem_compl]
  by_cases hp : p.1.val = i.val
  · rw [hc p hp]
  · simp only [hp, false_and, and_false]

theorem needle_space (i : Fin r.width) :
    r.height + r.quotas.getD i.val 0 + (sourceColumn r i).card < r.needleLevel i := by
  have hi : i.val < r.quotas.length := r.quotas_width.symm ▸ i.isLt
  have hs : (r.quotas.drop i.val).sum =
      r.quotas.getD i.val 0 + (r.quotas.drop (i.val + 1)).sum := by
    rw [List.drop_eq_getElem_cons hi, List.sum_cons, List.getD_eq_getElem _ _ hi]
  have hsum := Push.ColumnScan.Input.drop_sum_le r.quotas i.val
  have hbound := r.separation
  have hcard := sourceColumn_card_le r i
  have hmax := Nat.le_max_left r.sourceHoles r.width
  unfold Push.ColumnScan.Input.needleLevel Push.ColumnScan.Input.firstLevel
  unfold Push.ColumnScan.Input.quota at hbound
  omega

/-- A selected whole-run remainder executes from the actual needle and returns to its quota level. -/
private theorem read_needle (i : Fin r.width) (F : Finset (Cell r.outputWidth r.outputHeight))
    (H : ExactNorthRead (sourceColumn r i) F)
    (hq : r.quotas.getD i.val 0 ≤ (sourceColumn r i \ F).card)
    (s : State r.outputWidth r.outputHeight) (hv : s.player ∉ s.boxes)
    (hp : s.player = r.needle i)
    (hc : ∀ p : Cell r.outputWidth r.outputHeight, p.1.val = i.val →
      (p ∉ s.boxes ↔ p ∈ r.empty)) :
    ∃ t : State r.outputWidth r.outputHeight, ReadPath s t ∧ t.player.1 = s.player.1 ∧
      t.player.2.val + r.quotas.getD i.val 0 = s.player.2.val ∧ remainingColumn r t i = F ∧
      ∀ p : Cell r.outputWidth r.outputHeight, p.1 ≠ s.player.1 → (p ∈ t.boxes ↔ p ∈ s.boxes) := by
  have hx : s.player.1.val = i.val := by rw [hp]; rfl
  have hy : s.player.2.val = r.needleLevel i := by rw [hp]; rfl
  have he := data_eq_sourceColumn r s i hx hc
  obtain ⟨t, ht, htx, hty, hf, hframe, _⟩ :=
    read_north_selected_path (r.quotas.getD i.val 0) s r.height F (he ▸ H) (he ▸ hq) hv
      (by rw [he, hy]; have := needle_space r i; omega) (by
        intro p hpx hlo hhi
        have hpx : p.1.val = i.val := (congrArg Fin.val hpx).trans hx
        by_contra hn
        exact r.column_gap i p hpx hlo (by omega) ((hc p hpx).mp hn))
  refine ⟨t, ht, htx, hty, ?_, hframe⟩
  rwa [remainingColumn_eq_data r t i ((congrArg Fin.val htx).trans hx)]

private theorem remainingColumn_frame (s t : State r.outputWidth r.outputHeight) (i : Fin r.width)
    (hf : ∀ p : Cell r.outputWidth r.outputHeight, p.1.val = i.val →
      (p ∈ t.boxes ↔ p ∈ s.boxes)) : remainingColumn r t i = remainingColumn r s i := by
  ext p
  simp only [remainingColumn, Finset.mem_filter, Finset.mem_compl]
  by_cases hx : p.1.val = i.val
  · rw [hf p hx]
  · simp only [hx, false_and, and_false]

private theorem advance_column (i : Fin r.width) (F : Finset (Cell r.outputWidth r.outputHeight))
    (H : ExactNorthRead (sourceColumn r i) F)
    (hq : r.quotas.getD i.val 0 ≤ (sourceColumn r i \ F).card)
    (s : State r.outputWidth r.outputHeight) (hv : s.player ∉ s.boxes)
    (hx : s.player.1.val = i.val + 1) (hy : s.player.2.val = r.readLevel (i.val + 1))
    (hc : ∀ p : Cell r.outputWidth r.outputHeight, p.1.val = i.val →
      (p ∉ s.boxes ↔ p ∈ r.empty)) :
    ∃ t : State r.outputWidth r.outputHeight, ReadPath s t ∧
      t.player.1.val = i.val ∧ t.player.2.val = r.readLevel i.val ∧ remainingColumn r t i = F ∧
      ∀ p : Cell r.outputWidth r.outputHeight, p.1.val ≠ i.val → (p ∈ t.boxes ↔ p ∈ s.boxes) := by
  have hm : r.needle i ∉ s.boxes := (hc _ rfl).mpr (r.needle_mem i)
  let a : State r.outputWidth r.outputHeight := ⟨r.needle i, s.boxes⟩
  have hwalk : Move .west s a := .walk hv
    ⟨hx.symm, Fin.ext hy.symm⟩ hm rfl
  obtain ⟨t, ht, htx, hty, hf, hframe⟩ := read_needle r i F H hq a hm rfl hc
  refine ⟨t, (Relation.ReflTransGen.single ⟨.west, hwalk, Or.inr rfl⟩).trans ht,
    congrArg Fin.val htx, Nat.add_right_cancel (hty.trans (r.readLevel_succ i)), hf, ?_⟩
  intro p hp
  exact hframe p (fun he => hp (congrArg Fin.val he))

private theorem read_columns
    (F : Fin r.width → Finset (Cell r.outputWidth r.outputHeight))
    (H : ∀ i, ExactNorthRead (sourceColumn r i) (F i))
    (hq : ∀ i, r.quotas.getD i.val 0 ≤ (sourceColumn r i \ F i).card)
    (k : ℕ) (hk : k ≤ r.width) (s : State r.outputWidth r.outputHeight)
    (hv : s.player ∉ s.boxes) (hx : s.player.1.val = k) (hy : s.player.2.val = r.readLevel k)
    (hc : ∀ p : Cell r.outputWidth r.outputHeight, p.1.val < k →
      (p ∉ s.boxes ↔ p ∈ r.empty)) :
    ∃ t : State r.outputWidth r.outputHeight, ReadPath s t ∧
      t.player.1.val = 0 ∧ t.player.2.val = r.targetLevel ∧
      (∀ p : Cell r.outputWidth r.outputHeight, k ≤ p.1.val → (p ∈ t.boxes ↔ p ∈ s.boxes)) ∧
      ∀ i : Fin r.width, i.val < k → remainingColumn r t i = F i := by
  induction k generalizing s with
  | zero => exact ⟨s, .refl, hx, by simpa only [Push.ColumnScan.Input.readLevel_zero] using hy,
      (fun _ _ => Iff.rfl), by intro i hi; omega⟩
  | succ k ih =>
    let i : Fin r.width := ⟨k, by omega⟩
    obtain ⟨t, hread, htx, hty, hF, hframe⟩ := advance_column r i (F i) (H i) (hq i)
      s hv hx hy (fun p hp => hc p (by change p.1.val = k at hp; omega))
    obtain ⟨u, hrun, hux, huy, hout, hFs⟩ := ih (by omega) t (hread.valid hv) htx hty (by
      intro p hp
      have he := hframe p (by dsimp [i]; omega)
      exact (not_congr he).trans (hc p (by omega)))
    refine ⟨u, hread.trans hrun, hux, huy, ?_, ?_⟩
    · intro p hp
      exact (hout p (by omega)).trans (hframe p (by dsimp [i]; omega))
    · intro j hj
      by_cases hjk : j.val < k
      · exact hFs j hjk
      · have hji : j = i := Fin.ext (by dsimp [i]; omega)
        subst j
        rw [remainingColumn_frame r t u i (fun p hp => hout p (by dsimp [i] at hp; omega))]
        exact hF

/-- The concrete reader realizes every selected whole-run remainder paying at least its quota. -/
theorem compile_run
    (hcorner : r.initial.player = r.sourceCorner)
    (F : Fin r.width → Finset (Cell r.outputWidth r.outputHeight))
    (H : ∀ i, ExactNorthRead (sourceColumn r i) (F i))
    (hq : ∀ i, r.quotas.getD i.val 0 ≤ (sourceColumn r i \ F i).card) :
    ∃ t : State r.outputWidth r.outputHeight, ReadPath r.compile.initial t ∧ t.player = r.target ∧
      ∀ i : Fin r.width, remainingColumn r t i = F i := by
  obtain ⟨t, hr, hx, hy, _, hF⟩ := read_columns r F H hq r.width le_rfl r.sealedState.toState
    (Finset.notMem_compl.mpr r.sealedState.player_empty) rfl (by
      change r.firstLevel = r.firstLevel - (r.quotas.drop r.width).sum
      rw [← r.quotas_width, List.drop_length, List.sum_nil, Nat.sub_zero]) (by
      intro p hp
      simpa only [PushS.HoleState.toState, Finset.mem_compl, not_not] using r.sealedState_source_columns p hp)
  exact ⟨t, (sealed_readPath r hcorner).trans hr, Prod.ext (Fin.ext hx) (Fin.ext hy),
    fun i => hF i i.isLt⟩

end PushPuzzle.PushPush.ColumnReader
