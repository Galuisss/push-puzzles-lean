/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.WholeScan
public import Push.CyclicTurnProgram

/-! Exact whole-run certificates transport through the reader's physical quarter turn. -/

@[expose] public section
namespace PushPuzzle.PushPush.WholeScan

open PushFS (Cell Direction Adjacent)
open Push.Cyclic

variable {w h : ℕ}

private theorem turn_adjacent (d : Direction) {p q : Cell w h} (ha : Adjacent d p q) :
    Adjacent (turnSide d) (turnEmbedding w h p) (turnEmbedding w h q) := by
  have he := ((turnGeometry w h).adjacent d p q).mpr ha
  cases d <;> exact he

private theorem Read.turn {side : Direction} {lane quota : ℕ}
    (hbound : lane < Push.Scan.laneCount side w h)
    {E F : Finset (Cell w h)} (H : Read side lane quota E F) :
    Read (turnSide side) (turnLane w side lane) quota
      (E.map (turnEmbedding w h)) (F.map (turnEmbedding w h)) := by
  constructor
  · exact (instruction_eval_turn_iff (Push.Scan.Instruction.read side lane quota) hbound E F).mpr H.eval
  · intro p hp q hq ha
    obtain ⟨hp, hpnot⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨p, hp0, rfl⟩ := Finset.mem_map.mp hp
    obtain ⟨q, hq0, rfl⟩ := Finset.mem_map.mp hq
    have hpnot' : p ∉ F := fun hf => hpnot (Finset.mem_map.mpr ⟨p, hf, rfl⟩)
    apply H.no_split p (Finset.mem_sdiff.mpr ⟨hp0, hpnot'⟩) q hq0
    have hs : turnSide side.opposite = (turnSide side).opposite := by cases side <;> rfl
    rw [← hs] at ha
    have he := ((turnGeometry w h).adjacent side.opposite p q).mp
      (by cases side <;> exact ha)
    exact he

theorem LooseExec.turn (program : List (Push.Scan.Instruction w h))
    (hbound : Push.Scan.Bounded program) {E F : Finset (Cell w h)}
    (H : LooseExec program E F) :
    LooseExec (turnProgram program) (E.map (turnEmbedding w h)) (F.map (turnEmbedding w h)) := by
  induction H with
  | nil => exact .nil _
  | cons paid head _ ih =>
    exact .cons paid (head.turn (hbound _ (List.mem_cons_self ..)))
      (ih (fun i hi => hbound i (List.mem_cons_of_mem _ hi)))

private theorem Read.unturn {side : Direction} {lane quota : ℕ}
    (hbound : lane < Push.Scan.laneCount side w h)
    {E : Finset (Cell w h)} {G : Finset (Cell h w)}
    (H : Read (turnSide side) (turnLane w side lane) quota (E.map (turnEmbedding w h)) G) :
    ∃ F, Read side lane quota E F ∧ G = F.map (turnEmbedding w h) := by
  have he := H.eval
  rw [show Push.Scan.Instruction.read (turnSide side) (turnLane w side lane) quota =
      turnInstruction (Push.Scan.Instruction.read side lane quota) from rfl,
    instruction_eval_turn (Push.Scan.Instruction.read (w := w) (h := h) side lane quota) hbound] at he
  obtain ⟨F, hF, hG⟩ := Option.map_eq_some_iff.mp he
  refine ⟨F, ⟨hF, ?_⟩, hG.symm⟩
  intro p hp q hq ha
  have hp' : turnEmbedding w h p ∈ E.map (turnEmbedding w h) \ G := by
    rw [← hG]
    obtain ⟨hp, hn⟩ := Finset.mem_sdiff.mp hp
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_map.mpr ⟨p, hp, rfl⟩, by
      intro hh
      obtain ⟨z, hz, he⟩ := Finset.mem_map.mp hh
      exact hn ((turnEmbedding w h).injective he ▸ hz)⟩
  have hq' : turnEmbedding w h q ∈ G := by
    rw [← hG]
    exact Finset.mem_map.mpr ⟨q, hq, rfl⟩
  apply H.no_split _ hp' _ hq'
  have ha' := turn_adjacent side.opposite ha
  have hs : turnSide side.opposite = (turnSide side).opposite := by cases side <;> rfl
  exact hs ▸ ha'

/-- Every physical turned overpayment projects with the same actual whole-run quota. -/
theorem LooseExec.unturn (program : List (Push.Scan.Instruction w h))
    (hbound : Push.Scan.Bounded program) (E : Finset (Cell w h))
    {G : Finset (Cell h w)} (H : LooseExec (turnProgram program) (E.map (turnEmbedding w h)) G) :
    ∃ F, LooseExec program E F ∧ G = F.map (turnEmbedding w h) := by
  induction program generalizing E with
  | nil => cases H; exact ⟨E, .nil _, rfl⟩
  | cons instruction program ih =>
    cases instruction with
    | clear side lanes => cases H
    | read side lane quota =>
      cases H with
      | cons paid head tail =>
        obtain ⟨F, hhead, hmap⟩ := head.unturn (hbound _ (List.mem_cons_self ..))
        rw [hmap] at tail
        obtain ⟨K, htail, hK⟩ := ih (fun i hi => hbound i (List.mem_cons_of_mem _ hi)) F tail
        exact ⟨K, .cons paid hhead htail, hK⟩

end PushPuzzle.PushPush.WholeScan
