/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombSubdivisionSimulation
public import PushS.Source.ConstraintGraph.Subdivision.Cursor
import all CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.Subdivision

/-! Reaching actual subdivision configurations that only withdraw original core inputs. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

open NCL NCL.ConstraintGraph NCL.ConstraintGraph.Subdivision

private def cursorMix {m : ℕ} {n : Fin m → ℕ} (source target : Cursor n) (count : ℕ) : Cursor n where
  position edge := if edge.val < count then target.position edge else source.position edge

private theorem cursor_port_iff {E : Type} {n : E → ℕ} (left right : Cursor n) (p : Port E)
    (he : left.position p.edge = right.position p.edge) :
    (port n p).In left.directions ↔ (port n p).In right.directions := by
  cases p with
  | mk edge side =>
    cases side with
    | false =>
      change decide (0 < (left.position edge).val) = false ↔ decide (0 < (right.position edge).val) = false
      rw [he]
    | true =>
      change decide (n edge < (left.position edge).val) = true ↔ decide (n edge < (right.position edge).val) = true
      rw [he]

private theorem cursorMix_legal {V : Type} {m : ℕ} (G : ConstraintGraph V (Fin m)) (n w : Fin m → ℕ)
    (source target : Cursor n) (s : Fin m → Bool)
    (hc : source.directions = enc n s) (ht : (graph G n w).Legal target.directions)
    (hports : ∀ v p, p ∈ (G v).ports → (port n p.1).In target.directions → p.1.In s)
    (count : ℕ) : (graph G n w).Legal (cursorMix source target count).directions := by
  intro vertex
  cases vertex with
  | inr joint => exact PushPuzzle.NCL.ConstraintGraph.Subdivision.Cursor.joint_sat G w _ joint.1 joint.2
  | inl vertex =>
    apply Vertex.Sat.mono (s := target.directions) _ (ht (.inl vertex))
    intro p hp hin
    obtain ⟨original, hraw, rfl⟩ := List.mem_map.mp hp
    by_cases he : original.1.edge.val < count
    · exact (cursor_port_iff _ target original.1 (by simp only [cursorMix, he, ite_true])).mpr hin
    · apply (cursor_port_iff _ source original.1 (by simp only [cursorMix, he, ite_false])).mpr
      rw [hc, port_in_enc]
      exact hports vertex original hraw hin

private theorem cursorMix_set_source {m : ℕ} {n : Fin m → ℕ} (source target : Cursor n)
    (count : ℕ) (hc : count < m) :
    (cursorMix source target count).set ⟨count, hc⟩ (source.position ⟨count, hc⟩) =
      cursorMix source target count := by
  ext edge
  by_cases he : edge = ⟨count, hc⟩
  · subst edge
    simp only [PushPuzzle.NCL.ConstraintGraph.Subdivision.Cursor.set, Function.update_self, cursorMix, lt_self_iff_false, ite_false]
  · simp only [PushPuzzle.NCL.ConstraintGraph.Subdivision.Cursor.set, Function.update_of_ne he]

private theorem cursorMix_succ {m : ℕ} {n : Fin m → ℕ} (source target : Cursor n)
    (count : ℕ) (hc : count < m) :
    (cursorMix source target count).set ⟨count, hc⟩ (target.position ⟨count, hc⟩) =
      cursorMix source target (count + 1) := by
  ext edge
  by_cases he : edge = ⟨count, hc⟩
  · subst edge
    simp only [PushPuzzle.NCL.ConstraintGraph.Subdivision.Cursor.set, Function.update_self, cursorMix, Nat.lt_add_one, ite_true]
  · have hval : edge.val ≠ count := fun h => he (Fin.ext h)
    have hlt : edge.val < count + 1 ↔ edge.val < count := by omega
    simp only [PushPuzzle.NCL.ConstraintGraph.Subdivision.Cursor.set, Function.update_of_ne he, cursorMix, hlt]

/-- A legal subdivided configuration that only withdraws original core inputs is reachable from
the original canonical extension, through the same actual standard segment moves. -/
theorem subdivision_reachable_of_core_inputs {V : Type} {m : ℕ}
    (G : ConstraintGraph V (Fin m)) (n w : Fin m → ℕ) (hw : ∀ e, 0 < w e) (hl : G.LoopFree)
    (s : Fin m → Bool) (hs : G.Legal s) (t : Segment n → Bool) (ht : (graph G n w).Legal t)
    (hports : ∀ v p, p ∈ (G v).ports →
      (⟨if p.1.dir then last n p.1.edge else first n p.1.edge, p.1.dir⟩ : Port (Segment n)).In t → p.1.In s) :
    (graph G n w).Reachable (enc n s) t := by
  have hsource := (simulation G n w hw hl).legal_enc hs
  change (graph G n w).Legal (enc n s) at hsource
  obtain ⟨source, hc, _⟩ := PushPuzzle.NCL.ConstraintGraph.Subdivision.Cursor.existsUnique_of_joint_sat G w hw (fun j => hsource (.inr j))
  obtain ⟨target, hd, _⟩ := PushPuzzle.NCL.ConstraintGraph.Subdivision.Cursor.existsUnique_of_joint_sat G w hw (fun j => ht (.inr j))
  have hmix := cursorMix_legal G n w source target s hc (hd ▸ ht) (hd ▸ hports)
  have hpath (count : ℕ) (hcount : count ≤ m) :
      (graph G n w).Reachable (cursorMix source target 0).directions
        (cursorMix source target count).directions := by
    induction count with
    | zero => exact .refl
    | succ count ih =>
      have he : count < m := by omega
      have hstep := PushPuzzle.NCL.ConstraintGraph.Subdivision.Cursor.reachable_set G w hl (cursorMix source target count) ⟨count, he⟩
        (a := source.position ⟨count, he⟩) (b := target.position ⟨count, he⟩)
        (by rw [cursorMix_set_source]; exact hmix count)
        (by rw [cursorMix_succ]; exact hmix (count + 1))
      rw [cursorMix_set_source, cursorMix_succ] at hstep
      exact (ih (by omega)).trans hstep
  have hzero : cursorMix source target 0 = source := by ext edge; simp [cursorMix]
  have hend : cursorMix source target m = target := by ext edge; simp [cursorMix]
  simpa only [hzero, hend, hc, hd] using hpath m le_rfl

end PushPuzzle.PushS.Comb
