/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicScanTransport
public import Push.ScanNormalize
import all Push.CyclicScanTransport

/-! Exact transport of bounded read/clear programs through the cyclic physical quarter turn. -/

public section
namespace PushPuzzle.Push.Scan

open PushFS

/-- Every cell lies on an actual lane of each side. -/
theorem lane_lt_count {w h : ℕ} (side : Direction) (q : Cell w h) :
    side.lane q < laneCount side w h := by
  cases side <;> first | exact q.1.isLt | exact q.2.isLt

/-- Every selected read or clear lane belongs to the actual rectangle. -/
@[expose] def Instruction.Bounded {w h : ℕ} : Instruction w h → Prop
  | .read side lane _ => lane < laneCount side w h
  | .clear side lanes => ∀ lane ∈ lanes, lane < laneCount side w h

/-- Every selected lane in the complete static program belongs to its rectangle. -/
@[expose] def Bounded {w h : ℕ} (program : List (Instruction w h)) : Prop :=
  ∀ i ∈ program, i.Bounded

end PushPuzzle.Push.Scan

namespace PushPuzzle.Push.Cyclic

open PushFS Scan

/-- The old boundary side after the physical turn `(x,y) ↦ (y,width−1−x)`. -/
@[expose] def turnSide : Direction → Direction
  | .north => .west
  | .west => .south
  | .south => .east
  | .east => .north

/-- The lane coordinate after the same physical turn. -/
@[expose] def turnLane (w : ℕ) : Direction → ℕ → ℕ
  | .north, lane | .south, lane => w - (lane + 1)
  | .east, lane | .west, lane => lane

/-- The actual finite family of clear lanes after turning. -/
@[expose] def turnLanes (w : ℕ) (side : Direction) (lanes : Finset ℕ) : Finset ℕ :=
  lanes.image (turnLane w side)

/-- Turn a literal read or clear instruction, retaining its read quota. -/
@[expose] def turnInstruction {w h : ℕ} : Instruction w h → Instruction h w
  | .read side lane quota => .read (turnSide side) (turnLane w side lane) quota
  | .clear side lanes => .clear (turnSide side) (turnLanes w side lanes)

/-- Turn every instruction of the same fixed static program. -/
@[expose] def turnProgram {w h : ℕ} (program : List (Instruction w h)) : List (Instruction h w) :=
  program.map turnInstruction

/-- The transformed lane coordinate agrees with the actual transformed cell. -/
theorem lane_turn {w h : ℕ} (side : Direction) (q : Cell w h) :
    (turnSide side).lane (turnEmbedding w h q) = turnLane w side (side.lane q) := by
  cases side <;> rfl

/-- The turn retains the number of actual parallel lanes for the corresponding side. -/
private theorem laneCount_turn (w h : ℕ) (side : Direction) :
    laneCount (turnSide side) h w = laneCount side w h := by
  cases side <;> rfl

/-- Actual lane coordinates remain actual after turning. -/
theorem turnLane_lt {w h lane : ℕ} (side : Direction) (hlane : lane < laneCount side w h) :
    turnLane w side lane < laneCount (turnSide side) h w := by
  rw [laneCount_turn]
  cases side <;> simp only [turnLane, laneCount] at hlane ⊢ <;> omega

/-- The actual bounded lanes are relabelled injectively by the turn. -/
theorem turnLane_eq_iff {w h a b : ℕ} (side : Direction)
    (ha : a < laneCount side w h) (hb : b < laneCount side w h) :
    turnLane w side a = turnLane w side b ↔ a = b := by
  cases side <;> simp only [turnLane, laneCount] at ha hb ⊢ <;> omega

/-- Turning a clear family preserves exactly its membership on the transformed cell. -/
private theorem mem_turnLanes {w h : ℕ} (side : Direction) (lanes : Finset ℕ)
    (hbound : ∀ lane ∈ lanes, lane < laneCount side w h) (q : Cell w h) :
    (turnSide side).lane (turnEmbedding w h q) ∈ turnLanes w side lanes ↔ side.lane q ∈ lanes := by
  rw [lane_turn]
  constructor
  · intro hx
    obtain ⟨lane, hlane, he⟩ := Finset.mem_image.mp hx
    have hl := (turnLane_eq_iff side (hbound lane hlane) (lane_lt_count side q)).mp he
    exact hl ▸ hlane
  · intro hx
    exact Finset.mem_image.mpr ⟨side.lane q, hx, rfl⟩

/-- Every actual selected read/clear lane remains bounded after turning. -/
theorem turnInstruction_bounded {w h : ℕ} (i : Instruction w h) (hi : i.Bounded) :
    (turnInstruction i).Bounded := by
  cases i with
  | read side lane quota => exact turnLane_lt side hi
  | clear side lanes =>
    intro lane hlane
    obtain ⟨old, hold, rfl⟩ := Finset.mem_image.mp hlane
    exact turnLane_lt side (hi old hold)

/-- A complete bounded static program remains bounded after the physical turn. -/
theorem turnProgram_bounded {w h : ℕ} (program : List (Instruction w h)) (hb : Scan.Bounded program) :
    Scan.Bounded (turnProgram program) := by
  rintro i hi
  obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hi
  exact turnInstruction_bounded old (hb old hold)

/-- Turning a literal instruction retains its positive read quota. -/
private theorem turnInstruction_quota {w h : ℕ} (i : Instruction w h) :
    (turnInstruction i).quota = i.quota := by
  cases i <;> rfl

/-- Turning the whole static program retains its total positive quota. -/
theorem turnProgram_quota {w h : ℕ} (program : List (Instruction w h)) :
    Scan.quota (turnProgram program) = Scan.quota program := by
  induction program with
  | nil => rfl
  | cons i rest ih =>
    simp only [turnProgram, List.map_cons, Scan.quota, List.map_cons, List.sum_cons] at ih ⊢
    rw [turnInstruction_quota, ih]

/-- A bounded literal read or clear commutes exactly with turning every current hole. -/
theorem instruction_eval_turn {w h : ℕ} (i : Instruction w h) (hb : i.Bounded)
    (E : Finset (Cell w h)) :
    (turnInstruction i).eval (E.map (turnEmbedding w h)) =
      (i.eval E).map (Finset.map (turnEmbedding w h)) := by
  cases i with
  | read side lane quota =>
    cases side with
    | north => exact north_read_turn lane quota hb E
    | south => exact south_read_turn lane quota hb E
    | west => exact west_read_turn lane quota E
    | east => exact east_read_turn lane quota E
  | clear side lanes =>
    change some ((E.map _).filter _) = some ((E.filter _).map _)
    apply congrArg some
    rw [Finset.filter_map]
    apply congrArg (Finset.map (turnEmbedding w h))
    apply Finset.filter_congr
    intro q _
    exact not_congr (mem_turnLanes side lanes hb q)

/-- The same bounded instruction succeeds with exactly the transformed remainder in either orientation. -/
theorem instruction_eval_turn_iff {w h : ℕ} (i : Instruction w h) (hb : i.Bounded)
    (E F : Finset (Cell w h)) :
    (turnInstruction i).eval (E.map (turnEmbedding w h)) = some (F.map (turnEmbedding w h)) ↔
      i.eval E = some F := by
  rw [instruction_eval_turn i hb]
  simpa only [Option.map_some] using
    (Option.map_injective (Finset.map_injective (turnEmbedding w h))).eq_iff
      (a := i.eval E) (b := some F)

/-- The whole bounded read/clear program commutes exactly with the physical quarter turn. -/
theorem eval_turn {w h : ℕ} (program : List (Instruction w h)) (hb : Scan.Bounded program)
    (E : Finset (Cell w h)) :
    Scan.eval (turnProgram program) (E.map (turnEmbedding w h)) =
      (Scan.eval program E).map (Finset.map (turnEmbedding w h)) := by
  induction program generalizing E with
  | nil => rfl
  | cons i rest ih =>
    simp only [turnProgram, List.map_cons, Scan.eval]
    rw [instruction_eval_turn i (hb i (List.mem_cons_self ..))]
    cases he : i.eval E with
    | none => simp only [Option.map_none, Option.bind_none]
    | some F =>
      simp only [Option.map_some, Option.bind_some]
      exact ih (fun j hj => hb j (List.mem_cons_of_mem i hj)) F

/-- Successful execution has exactly the same finite remainder after turning. -/
theorem eval_turn_iff {w h : ℕ} (program : List (Instruction w h)) (hb : Scan.Bounded program)
    (E F : Finset (Cell w h)) :
    Scan.eval (turnProgram program) (E.map (turnEmbedding w h)) = some (F.map (turnEmbedding w h)) ↔
      Scan.eval program E = some F := by
  rw [eval_turn program hb]
  simpa only [Option.map_some] using
    (Option.map_injective (Finset.map_injective (turnEmbedding w h))).eq_iff
      (a := Scan.eval program E) (b := some F)

/-- A bounded read/clear program accepts exactly the same physical inventory after turning. -/
theorem accepts_turn_iff {w h : ℕ} (program : List (Instruction w h)) (hb : Scan.Bounded program)
    (E : Finset (Cell w h)) :
    Scan.Accepts (turnProgram program) (E.map (turnEmbedding w h)) ↔ Scan.Accepts program E := by
  constructor
  · rintro ⟨F, hF⟩
    rw [eval_turn program hb] at hF
    obtain ⟨G, hG, _⟩ := Option.map_eq_some_iff.mp hF
    exact ⟨G, hG⟩
  · rintro ⟨F, hF⟩
    exact ⟨F.map (turnEmbedding w h), (eval_turn_iff program hb E F).mpr hF⟩

end PushPuzzle.Push.Cyclic
