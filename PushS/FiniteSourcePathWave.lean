/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourcePathEvents

/-! A concrete finite phase wave prepares every real line and turn in its required order. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting
open scoped Classical

attribute [local irreducible] codes width height inventory

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} {P : PathSpec}

namespace PathEvent

private theorem rank_bound (a : PathEvent P) : a.rank < 2*P.segments.length := by
  cases a with
  | line i => have := i.isLt; change 2*i.val < _; omega
  | turn i hi => have := i.isLt; change 2*i.val+1 < _; omega

end PathEvent

namespace PathSite

variable (s : PathSite w hw v P) (G : P.Geometry w)

/-- The number of possible line/turn instruction slots in this actual path. -/
def waveLength : ℕ := 2*P.segments.length

/-- A high-to-low path runs in its emitted order; a low-to-high path runs in reverse. -/
def waveDone (cut : ℕ) (a : PathEvent P) : Prop :=
  if P.initial then a.rank < cut else waveLength (P := P)-cut ≤ a.rank

/-- The complete global owner phases at one explicit propagation cut. -/
noncomputable def wave (base : Fin (codes w v).length → Bool) (cut : ℕ)
    (i : Fin (codes w v).length) : Bool :=
  if ∃ a : PathEvent P, a.owner s = i ∧ waveDone cut a then true else base i

/-- Real owners outside this path retain their original phase throughout the wave. -/
theorem wave_outside (base : Fin (codes w v).length → Bool) (cut : ℕ) (i : Fin (codes w v).length)
    (hi : ∀ a : PathEvent P, a.owner s ≠ i) : s.wave base cut i = base i := by
  unfold wave
  rw [ite_eq_right]
  rintro ⟨a,ha,_⟩
  exact hi a ha

include G in
/-- Each literal path owner's phase is exactly the completed side of the propagation cut. -/
private theorem wave_owner (base : Fin (codes w v).length → Bool)
    (hbase : ∀ a : PathEvent P,base (a.owner s) = false) (cut : ℕ) (a : PathEvent P) :
    s.wave base cut (a.owner s) = decide (waveDone cut a) := by
  have he : (∃ b : PathEvent P,b.owner s = a.owner s ∧ waveDone cut b) ↔ waveDone cut a := by
    constructor
    · rintro ⟨b,hb,hd⟩
      exact (PathEvent.owner_injective s G hb) ▸ hd
    · exact fun h => ⟨a,rfl,h⟩
  simp only [wave,he,hbase]
  split_ifs <;> simp_all

/-- No real path owner has changed before the first instruction. -/
theorem wave_zero (base : Fin (codes w v).length → Bool) : s.wave base 0 = base := by
  funext i
  unfold wave
  apply ite_eq_right
  rintro ⟨a,_,ha⟩
  have hb := a.rank_bound
  unfold waveDone waveLength at ha
  cases P.initial <;> simp_all <;> omega

/-- The instruction processed at a cut is its literal forward or reverse rank. -/
def waveRank (cut : ℕ) : ℕ :=
  if P.initial then cut else waveLength (P := P)-1-cut

include G in
/-- Every instruction sees exactly the physical preparation front required by the line and turn macros. -/
theorem wave_frontier (base : Fin (codes w v).length → Bool)
    (hbase : ∀ a : PathEvent P,base (a.owner s) = false) (cut : ℕ)
    (hcut : cut < waveLength (P := P)) (a : PathEvent P) (ha : a.rank = waveRank (P := P) cut) :
    PathEvent.Frontier s (s.wave base cut) a := by
  constructor
  intro b
  rw [s.wave_owner G base hbase]
  unfold waveDone waveRank waveLength at *
  cases hp : P.initial <;> simp only [hp,Bool.false_eq_true,ite_false,ite_true] at *
  · have he : 2*P.segments.length-cut = a.rank+1 := by omega
    rw [he]
    congr 1
  · rw [ha]

include G in
/-- Advancing one actual instruction updates exactly its compiler owner in the complete global phase function. -/
theorem wave_step (base : Fin (codes w v).length → Bool)
    (hbase : ∀ a : PathEvent P,base (a.owner s) = false) (cut : ℕ)
    (hcut : cut < waveLength (P := P)) (a : PathEvent P) (ha : a.rank = waveRank (P := P) cut) :
    s.wave base (cut+1) = Function.update (s.wave base cut) (a.owner s) true := by
  funext i
  by_cases hi : ∃ b : PathEvent P,b.owner s = i
  · obtain ⟨b,rfl⟩ := hi
    by_cases he : b = a
    · subst b
      rw [Function.update_self,s.wave_owner G base hbase]
      have hd : waveDone (cut+1) a := by
        unfold waveDone waveRank waveLength at *
        cases hp : P.initial <;> simp only [hp,Bool.false_eq_true,ite_false,ite_true] at * <;> omega
      simp only [hd,decide_true]
    · have hn : b.owner s ≠ a.owner s := fun h => he (PathEvent.owner_injective s G h)
      rw [Function.update_of_ne hn,s.wave_owner G base hbase,s.wave_owner G base hbase]
      have hr : b.rank ≠ a.rank := fun h => he (PathEvent.rank_injective h)
      have hd : waveDone (cut+1) b ↔ waveDone cut b := by
        unfold waveDone waveRank waveLength at *
        cases hp : P.initial <;> simp only [hp,Bool.false_eq_true,ite_false,ite_true] at * <;> omega
      simp only [hd]
  · have hn : ∀ b : PathEvent P,b.owner s ≠ i := by simpa only [not_exists] using hi
    have hni : i ≠ a.owner s := fun h => hn a h.symm
    rw [Function.update_of_ne hni,s.wave_outside base (cut+1) i hn,s.wave_outside base cut i hn]

include G in
/-- A rank without a perpendicular turn consumes no move and leaves every actual box unchanged. -/
theorem wave_skip (base : Fin (codes w v).length → Bool)
    (hbase : ∀ a : PathEvent P,base (a.owner s) = false) (cut : ℕ)
    (hcut : cut < waveLength (P := P)) (ha : ¬∃ a : PathEvent P,a.rank = waveRank (P := P) cut) :
    s.wave base (cut+1) = s.wave base cut := by
  funext i
  by_cases hi : ∃ b : PathEvent P,b.owner s = i
  · obtain ⟨b,rfl⟩ := hi
    rw [s.wave_owner G base hbase,s.wave_owner G base hbase]
    have hr : b.rank ≠ waveRank (P := P) cut := fun h => ha ⟨b,h⟩
    have hd : waveDone (cut+1) b ↔ waveDone cut b := by
      unfold waveDone waveRank waveLength at *
      cases hp : P.initial <;> simp only [hp,Bool.false_eq_true,ite_false,ite_true] at * <;> omega
    simp only [hd]
  · have hn : ∀ b : PathEvent P,b.owner s ≠ i := by simpa only [not_exists] using hi
    rw [s.wave_outside base (cut+1) i hn,s.wave_outside base cut i hn]

/-- The final actual phase function updates every path instruction and preserves all other owners. -/
theorem wave_final (base : Fin (codes w v).length → Bool) (i : Fin (codes w v).length) :
    s.wave base (waveLength (P := P)) i = if ∃ a : PathEvent P,a.owner s = i then true else base i := by
  unfold wave
  congr 1
  apply propext
  constructor
  · rintro ⟨a,ha,_⟩
    exact ⟨a,ha⟩
  · rintro ⟨a,ha⟩
    refine ⟨a,ha,?_⟩
    have hb := a.rank_bound
    unfold waveDone waveLength
    cases P.initial <;> simp_all

end PathSite
end PushPuzzle.PushS.FiniteSourceInventory
