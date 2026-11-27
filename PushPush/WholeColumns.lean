/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.WholeScan
public import PushPush.ColumnReaderRuns
public import Push.ScanColumns
public import Push.ScanEmbedding

/-! Simultaneous whole northern remainders produce a complete loose column program. -/

@[expose] public section
namespace PushPuzzle.PushPush.WholeScan

open PushFS (Cell Direction Adjacent)
open Push.ReaderResidual

variable {w h : ℕ}

private theorem Exec.columns_of_eval {requests : List (ℕ × ℕ)} {E F : Finset (Cell w h)}
    (hnd : (requests.map Prod.fst).Nodup)
    (he : Push.Scan.eval (Push.Scan.columns requests) E = some F)
    (hwhole : ColumnReader.NoNorthSplit E F) : Exec (Push.Scan.columns requests) E F := by
  induction requests generalizing E with
  | nil =>
    have hf : E = F := Option.some.inj he
    exact hf ▸ Exec.nil E
  | cons a rest ih =>
    obtain ⟨hnot, hnd⟩ := List.nodup_cons.mp hnd
    simp only [Push.Scan.columns, Push.Scan.lines, List.map_cons, Push.Scan.eval,
      Option.bind_eq_some_iff] at he
    obtain ⟨G, hread, htail⟩ := he
    have hGE : G ⊆ E := Push.Scan.eval_subset (program := [.read .south a.1 a.2]) (by
      simp only [Push.Scan.eval, hread, Option.bind_some])
    have hFG : F ⊆ G := Push.Scan.eval_subset htail
    refine .cons ⟨hread, ?_⟩ (ih hnd htail ?_)
    · intro p hp q hq ha
      have hpx : p.1.val = a.1 := by
        by_contra hn
        exact (Finset.mem_sdiff.mp hp).2
          ((Push.Scan.Instruction.read_outside hread hn).mpr (Finset.mem_sdiff.mp hp).1)
      have hqx : q.1.val = a.1 := (congrArg Fin.val ha.1).trans hpx
      have hqF : q ∈ F := by
        apply (Push.Scan.eval_mem_outside htail ?_).mpr hq
        intro i hi
        obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hi
        intro z hz
        have heq : z = q := Finset.mem_singleton.mp hz
        rw [heq]
        intro hn
        apply hnot
        exact List.mem_map.mpr ⟨b, hb, hn.symm.trans hqx⟩
      exact hwhole p (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hp).1,
        fun hpF => (Finset.mem_sdiff.mp hp).2 (hFG hpF)⟩) q hqF ha
    · intro p hp q hq ha
      exact hwhole p (Finset.mem_sdiff.mpr ⟨hGE (Finset.mem_sdiff.mp hp).1,
        (Finset.mem_sdiff.mp hp).2⟩) q hq ha

private theorem Exec.loosen_columns {small large : List (ℕ × ℕ)} {E F : Finset (Cell w h)}
    (he : Exec (Push.Scan.columns large) E F)
    (hle : List.Forall₂ (fun a b : ℕ × ℕ => a.1 = b.1 ∧ a.2 ≤ b.2) small large) :
    LooseExec (Push.Scan.columns small) E F := by
  induction hle generalizing E with
  | nil => cases he; exact .nil _
  | @cons a b small large hab htail ih =>
    cases he with
    | cons head tail =>
      exact .cons hab.2 (by simpa only [hab.1] using head) (ih tail)

/-- A complete actual northern remainder pays every prescribed column quota by whole runs. -/
theorem loose_columns {requests : List (ℕ × ℕ)} {E F : Finset (Cell w h)}
    (hnd : (requests.map Prod.fst).Nodup)
    (hcover : ∀ x : Fin w, ∃ q, (x.val, q) ∈ requests)
    (hrem : BottomRemainder E F) (hwhole : ColumnReader.NoNorthSplit E F)
    (hpaid : ∀ a ∈ requests, a.2 + (F.filter fun p => p.1.val = a.1).card ≤
      (E.filter fun p => p.1.val = a.1).card) :
    LooseExec (Push.Scan.columns requests) E F := by
  let actual := requests.map fun a =>
    (a.1, (E.filter fun p => p.1.val = a.1).card - (F.filter fun p => p.1.val = a.1).card)
  have hactualnd : (actual.map Prod.fst).Nodup := by
    simpa only [actual, List.map_map, Function.comp_def] using hnd
  have hquota : ∀ a ∈ actual, a.2 ≤ (E.filter fun p => p.1.val = a.1).card := by
    intro a ha
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
    exact Nat.sub_le _ _
  obtain ⟨G, hread⟩ := Push.Scan.columns_accepts actual E hactualnd hquota
  have hG := Push.Scan.columns_remainder hread
  have hcard : ∀ x : Fin w,
      (F.filter fun p => p.1 = x).card = (G.filter fun p => p.1 = x).card := by
    intro x
    obtain ⟨q, hq⟩ := hcover x
    have ha : (x.val, (E.filter fun p => p.1.val = x.val).card -
        (F.filter fun p => p.1.val = x.val).card) ∈ actual := List.mem_map.mpr ⟨(x.val, q), hq, rfl⟩
    have hc := Push.Scan.columns_card hactualnd hread ha
    have hs : (F.filter fun p => p.1.val = x.val) ⊆ (E.filter fun p => p.1.val = x.val) := by
      intro p hp
      exact Finset.mem_filter.mpr ⟨hrem.subset (Finset.mem_filter.mp hp).1,
        (Finset.mem_filter.mp hp).2⟩
    have hle := Finset.card_le_card hs
    have heq : (F.filter fun p => p.1.val = x.val).card =
        (G.filter fun p => p.1.val = x.val).card := by dsimp only at hc; omega
    simpa only [Fin.ext_iff] using heq
  have heq : G = F := Finset.Subset.antisymm
    (hG.subset_of_column_card hrem (fun x => (hcard x).symm.le))
    (hrem.subset_of_column_card hG (fun x => (hcard x).le))
  subst G
  apply (Exec.columns_of_eval hactualnd hread hwhole).loosen_columns
  apply List.forall₂_map_right_iff.mpr
  apply List.forall₂_same.mpr
  intro a ha
  refine ⟨rfl, ?_⟩
  have hp := hpaid a ha
  dsimp only
  omega

end PushPuzzle.PushPush.WholeScan
