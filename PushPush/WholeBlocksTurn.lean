/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.WholeBlocksSourceProgram
public import Push.CyclicRounds
import all PushPush.WholeTransport
import all Push.ScanNormalize

/-! Whole parallel blocks and complete future rounds transport through the actual quarter turn. -/

@[expose] public section
namespace PushPuzzle.PushPush.WholeBlocks

open PushFS (Cell Direction Adjacent)
open Push.Cyclic
open Push.AcceptanceProgram

variable {w h : ℕ}

private theorem turnRequests_quotaAt (side : Direction) (requests : List (ℕ × ℕ))
    (hbound : ∀ a ∈ requests, a.1 < Push.Scan.laneCount side w h)
    (lane : ℕ) (hlane : lane < Push.Scan.laneCount side w h) :
    Push.Scan.quotaAt (turnRequests w side requests) (turnLane w side lane) =
      Push.Scan.quotaAt requests lane := by
  induction requests with
  | nil => rfl
  | cons a rest ih =>
    simp only [turnRequests, List.map_cons, Push.Scan.quotaAt_cons,
      turnLane_eq_iff side (hbound a (List.mem_cons_self ..)) hlane]
    exact congrArg (fun n => (if a.1 = lane then a.2 else 0) + n)
      (ih (fun b hb => hbound b (List.mem_cons_of_mem _ hb)))

private theorem turn_lane_surjective (side : Direction) (lane : ℕ)
    (hlane : lane < Push.Scan.laneCount (turnSide side) h w) :
    ∃ old < Push.Scan.laneCount side w h, turnLane w side old = lane := by
  cases side with
  | north | south =>
    refine ⟨w - 1 - lane, by simp only [turnSide, Push.Scan.laneCount] at hlane ⊢; omega, ?_⟩
    simp only [turnLane, turnSide, Push.Scan.laneCount] at hlane ⊢
    omega
  | east | west => exact ⟨lane, hlane, rfl⟩

private theorem turn_lt (side : Direction) (p q : Cell w h) :
    (turnSide side).position (turnEmbedding w h p) < (turnSide side).position (turnEmbedding w h q) ↔
      side.position p < side.position q := by
  have hp := p.1.isLt
  have hq := q.1.isLt
  have hpx : (turnEmbedding w h p).1.val = p.2.val := rfl
  have hqx : (turnEmbedding w h q).1.val = q.2.val := rfl
  have hpy : (turnEmbedding w h p).2.val = w - (p.1.val + 1) := rfl
  have hqy : (turnEmbedding w h q).2.val = w - (q.1.val + 1) := rfl
  cases side <;> simp only [turnSide, Direction.position, hpx, hqx, hpy, hqy] <;> omega

private theorem turn_filter_map (side : Direction) (lane : ℕ)
    (hlane : lane < Push.Scan.laneCount side w h) (E : Finset (Cell w h)) :
    ((E.map (turnEmbedding w h)).filter fun q => (turnSide side).lane q = turnLane w side lane) =
      (E.filter fun p => side.lane p = lane).map (turnEmbedding w h) := by
  ext q
  constructor
  · intro hq
    obtain ⟨hq, hl⟩ := Finset.mem_filter.mp hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hq
    rw [lane_turn] at hl
    exact Finset.mem_map.mpr ⟨p, Finset.mem_filter.mpr ⟨hp,
      (turnLane_eq_iff side (Push.Scan.lane_lt_count side p) hlane).mp hl⟩, rfl⟩
  · intro hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hq
    obtain ⟨hp, hl⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_map.mpr ⟨p, hp, rfl⟩, by rw [lane_turn, hl]⟩

private theorem Block.turn {side : Direction} {requests : List (ℕ × ℕ)}
    {E F : Finset (Cell w h)} (H : Block side requests E F)
    (hbound : ∀ a ∈ requests, a.1 < Push.Scan.laneCount side w h) :
    Block (turnSide side) (turnRequests w side requests)
      (E.map (turnEmbedding w h)) (F.map (turnEmbedding w h)) := by
  have hc := H.characterization
  apply Block.of_characterization
  refine ⟨Finset.map_subset_map.mpr hc.subset, ?_, ?_, ?_⟩
  · intro p hp q hq hl
    obtain ⟨hp, hpnot⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨p, hp0, rfl⟩ := Finset.mem_map.mp hp
    obtain ⟨q, hq0, rfl⟩ := Finset.mem_map.mp hq
    have hnot : p ∉ F := fun hf => hpnot (Finset.mem_map.mpr ⟨p, hf, rfl⟩)
    apply (turn_lt side q p).mpr
    apply hc.front p (Finset.mem_sdiff.mpr ⟨hp0, hnot⟩) q hq0
    rw [lane_turn, lane_turn] at hl
    exact (turnLane_eq_iff side (Push.Scan.lane_lt_count side q) (Push.Scan.lane_lt_count side p)).mp hl
  · intro p hp q hq ha
    obtain ⟨hp, hpnot⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨p, hp0, rfl⟩ := Finset.mem_map.mp hp
    obtain ⟨q, hq0, rfl⟩ := Finset.mem_map.mp hq
    have hnot : p ∉ F := fun hf => hpnot (Finset.mem_map.mpr ⟨p, hf, rfl⟩)
    apply hc.no_split p (Finset.mem_sdiff.mpr ⟨hp0, hnot⟩) q hq0
    have hs : turnSide side.opposite = (turnSide side).opposite := by cases side <;> rfl
    rw [← hs] at ha
    exact ((turnGeometry w h).adjacent side.opposite p q).mp (by cases side <;> exact ha)
  · intro lane hlane
    obtain ⟨old, hold, rfl⟩ := turn_lane_surjective side lane hlane
    rw [turnRequests_quotaAt side requests hbound old hold, turn_filter_map side old hold E,
      turn_filter_map side old hold F, ← Finset.map_sdiff, Finset.card_map]
    exact hc.paid old hold

private theorem Block.unturn {side : Direction} {requests : List (ℕ × ℕ)}
    {E F : Finset (Cell w h)}
    (H : Block (turnSide side) (turnRequests w side requests)
      (E.map (turnEmbedding w h)) (F.map (turnEmbedding w h)))
    (hbound : ∀ a ∈ requests, a.1 < Push.Scan.laneCount side w h) : Block side requests E F := by
  have hc := H.characterization
  apply Block.of_characterization
  refine ⟨Finset.map_subset_map.mp hc.subset, ?_, ?_, ?_⟩
  · intro p hp q hq hl
    have hp' : turnEmbedding w h p ∈ E.map (turnEmbedding w h) \ F.map (turnEmbedding w h) := by
      rw [← Finset.map_sdiff]
      exact Finset.mem_map.mpr ⟨p, hp, rfl⟩
    apply (turn_lt side q p).mp
    exact hc.front _ hp' _ (Finset.mem_map.mpr ⟨q, hq, rfl⟩) (by rw [lane_turn, lane_turn, hl])
  · intro p hp q hq ha
    have hp' : turnEmbedding w h p ∈ E.map (turnEmbedding w h) \ F.map (turnEmbedding w h) := by
      rw [← Finset.map_sdiff]
      exact Finset.mem_map.mpr ⟨p, hp, rfl⟩
    apply hc.no_split _ hp' _ (Finset.mem_map.mpr ⟨q, hq, rfl⟩)
    have hs : turnSide side.opposite = (turnSide side).opposite := by cases side <;> rfl
    exact hs ▸ WholeScan.turn_adjacent side.opposite ha
  · intro lane hlane
    have hp := hc.paid (turnLane w side lane) (turnLane_lt side hlane)
    rw [turnRequests_quotaAt side requests hbound lane hlane, turn_filter_map side lane hlane E,
      turn_filter_map side lane hlane F, ← Finset.map_sdiff, Finset.card_map] at hp
    exact hp

private theorem Block.unturn_any {side : Direction} {requests : List (ℕ × ℕ)}
    {E : Finset (Cell w h)} {G : Finset (Cell h w)}
    (H : Block (turnSide side) (turnRequests w side requests) (E.map (turnEmbedding w h)) G)
    (hbound : ∀ a ∈ requests, a.1 < Push.Scan.laneCount side w h) :
    ∃ F, Block side requests E F ∧ G = F.map (turnEmbedding w h) := by
  let F := G.map (turnGeometry w h).cells.symm.toEmbedding
  have hF : F.map (turnEmbedding w h) = G := by
    ext q
    simp only [F, turnEmbedding, Finset.mem_map_equiv, Equiv.symm_apply_apply]
  rw [← hF] at H
  exact ⟨F, H.unturn hbound, hF.symm⟩

theorem Exec.turn (rounds : List Round) {E F : Finset (Cell w h)} (H : Exec rounds E F)
    (hbound : Push.Scan.Bounded (instructions (w := w) (h := h) rounds)) :
    Exec (rounds.map (turnRound w)) (E.map (turnEmbedding w h)) (F.map (turnEmbedding w h)) := by
  revert hbound
  induction H with
  | nil => exact fun _ => .nil _
  | @cons side requests rounds E G F head tail ih =>
    intro hbound
    have hrequest : ∀ a ∈ requests, a.1 < Push.Scan.laneCount side w h := by
      intro a ha
      exact hbound _ (List.mem_append_left _ (List.mem_map.mpr ⟨a, ha, rfl⟩))
    have htail : Push.Scan.Bounded (instructions (w := w) (h := h) rounds) :=
      fun i hi => hbound i (List.mem_append_right _ hi)
    exact .cons (head.turn hrequest) (ih htail)

theorem Exec.unturn (rounds : List Round) (E : Finset (Cell w h)) {G : Finset (Cell h w)}
    (H : Exec (rounds.map (turnRound w)) (E.map (turnEmbedding w h)) G)
    (hbound : Push.Scan.Bounded (instructions (w := w) (h := h) rounds)) :
    ∃ F, Exec rounds E F ∧ G = F.map (turnEmbedding w h) := by
  induction rounds generalizing E with
  | nil => cases H; exact ⟨E, .nil _, rfl⟩
  | cons round rounds ih =>
    cases round with
    | clear side lanes => cases H
    | read side requests =>
      cases H with
      | cons head tail =>
        have hrequest : ∀ a ∈ requests, a.1 < Push.Scan.laneCount side w h := by
          intro a ha
          exact hbound _ (List.mem_append_left _ (List.mem_map.mpr ⟨a, ha, rfl⟩))
        obtain ⟨F, hhead, hmap⟩ := head.unturn_any hrequest
        rw [hmap] at tail
        obtain ⟨K, htail, hK⟩ := ih F tail
          (fun i hi => hbound i (List.mem_append_right _ hi))
        exact ⟨K, .cons hhead htail, hK⟩

end PushPuzzle.PushPush.WholeBlocks
