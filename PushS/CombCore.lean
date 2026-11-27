/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombTopology
import all PushS.CombTopology
import CslibFrontier.Foundations.Data.List.Lookup

/-! Local contour partitions preserve the actual native weighted incidence lists. -/

public section

namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

/-- Sorting the geometric fan preserves every original weighted native incidence. -/
theorem fan_perm (width : ℕ) (input : Input) (vertex : ℕ) :
    (fan width input vertex).Perm (input.graph.vertices.getD vertex ⟨[], 0⟩).ports := by
  have hp := (Sort.run_perm Prod.fst (0, ⟨⟨0, false⟩, 0⟩)
    ((input.graph.vertices.getD vertex ⟨[], 0⟩).ports.map fun p =>
      (tangentKey (outgoingVector width input.drawing p.1), p))).map Prod.snd
  simpa only [fan, List.map_map, Function.comp_def, List.map_id'] using hp

private theorem vertex_isAndOr (input : Input) (hg : NCL.SourceValid input.graph) {v : ℕ}
    (hv : v < input.graph.vertices.length) :
    (input.graph.vertices.getD v ⟨[], 0⟩).IsAndOr := by
  let i : Fin input.graph.vertices.length := ⟨v, hv⟩
  have hm := congrFun (input.graph.graph_map_val hg.1) i
  have hi := (hg.isAndOr i).map Fin.val
  change ((input.graph.graph i).map Fin.val) = input.graph.vertices.get i at hm
  rw [hm] at hi
  rw [List.getD_eq_get input.graph.vertices ⟨[], 0⟩ i]
  exact hi

/-- A valid source's actual ordered fan has the native AND or OR weight multiset. -/
private theorem fan_weights (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph) {v : ℕ}
    (hv : v < input.graph.vertices.length) :
    ((fan width input v).map NCL.WeightedPort.weight).Perm [1, 1, 2] ∨
      ((fan width input v).map NCL.WeightedPort.weight).Perm [2, 2, 2] := by
  have hf := (fan_perm width input v).map NCL.WeightedPort.weight
  rcases vertex_isAndOr input hg hv with ⟨a, b, c, _, hp⟩ | ⟨a, b, c, _, hp⟩
  · left
    exact hf.trans (by simpa only [NCL.Vertex.and, List.map_cons, List.map_nil] using hp.map NCL.WeightedPort.weight)
  · right
    exact hf.trans (by simpa only [NCL.Vertex.or, List.map_cons, List.map_nil] using hp.map NCL.WeightedPort.weight)

/-- Every valid original vertex contributes precisely three weighted fan entries. -/
theorem fan_length (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph) {v : ℕ}
    (hv : v < input.graph.vertices.length) : (fan width input v).length = 3 := by
  rcases fan_weights width input hg hv with h | h <;>
    simpa only [List.length_map, List.length_cons, List.length_nil] using h.length_eq

private theorem coreTemplate_selected_ports_perm (vertex : ℕ) (ports : List (NCL.WeightedPort ℕ)) :
    ((coreTemplate vertex ports).core.ports.map Prod.snd).Perm
      [ports.getD 0 ⟨⟨0, false⟩, 0⟩, ports.getD 1 ⟨⟨0, false⟩, 0⟩, ports.getD 2 ⟨⟨0, false⟩, 0⟩] := by
  unfold coreTemplate
  extract_lets a b c kind ta tb tc inside outside
  split_ifs <;> simp only [List.map_cons, List.map_nil]
  · exact (show ([b, c] ++ [a]).Perm ([a] ++ [b, c]) from List.perm_append_comm)
  · exact (show ([c] ++ [a, b]).Perm ([a, b] ++ [c]) from List.perm_append_comm)
  · exact List.Perm.refl _

/-- The local rotation retains all three original weighted incidences. -/
theorem coreTemplate_ports_perm (vertex : ℕ) (ports : List (NCL.WeightedPort ℕ)) (hports : ports.length = 3) :
    ((coreTemplate vertex ports).core.ports.map Prod.snd).Perm ports := by
  have h := coreTemplate_selected_ports_perm vertex ports
  obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp hports
  simpa only [List.getD_cons_zero, List.getD_cons_succ] using h

/-- The emitted real core retains its original native weighted incidence list. -/
theorem coreBlock_ports_perm (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph) {v : ℕ}
    (hv : v < input.graph.vertices.length) :
    ((coreBlock width input v).core.ports.map Prod.snd).Perm (input.graph.vertices.getD v ⟨[], 0⟩).ports :=
  (coreTemplate_ports_perm v (fan width input v) (fan_length width input hg hv)).trans (fan_perm width input v)

private theorem fan_weight_cases (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph) {v : ℕ}
    (hv : v < input.graph.vertices.length) :
    (fan width input v).map NCL.WeightedPort.weight = [1, 1, 2] ∨
      (fan width input v).map NCL.WeightedPort.weight = [1, 2, 1] ∨
      (fan width input v).map NCL.WeightedPort.weight = [2, 1, 1] ∨
      (fan width input v).map NCL.WeightedPort.weight = [2, 2, 2] := by
  have hf := fan_perm width input v
  have hvalid : (⟨fan width input v, 2⟩ : NCL.Vertex ℕ).IsAndOr := by
    rcases vertex_isAndOr input hg hv with ⟨a, b, c, _, hp⟩ | ⟨a, b, c, _, hp⟩
    · exact Or.inl ⟨a, b, c, rfl, hf.trans hp⟩
    · exact Or.inr ⟨a, b, c, rfl, hf.trans hp⟩
  have hcheck := (NCL.Vertex.checkAndOr_eq_true_iff _).mpr hvalid
  simpa only [NCL.Vertex.checkAndOr, beq_self_eq_true, Bool.true_and, List.contains_iff_mem,
    List.mem_cons, List.not_mem_nil, or_false] using hcheck

/-- The literal emitted core puts every AND heavy incidence last and keeps OR weights unchanged. -/
theorem coreBlock_weights (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph) {v : ℕ}
    (hv : v < input.graph.vertices.length) :
    ((coreBlock width input v).core.kind = .andGate ∧
      (coreBlock width input v).core.ports.map (fun p => p.2.2) = [1, 1, 2]) ∨
    ((coreBlock width input v).core.kind = .orGate ∧
      (coreBlock width input v).core.ports.map (fun p => p.2.2) = [2, 2, 2]) := by
  have hlen := fan_length width input hg hv
  have hcases := fan_weight_cases width input hg hv
  obtain ⟨a, b, c, hfan⟩ := List.length_eq_three.mp hlen
  simp only [hfan, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hcases
  rcases hcases with ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ <;>
    simp [coreBlock, hfan, coreTemplate, ha, hb, hc]

/-- The actual local core metadata labels exactly one emitted lower triple. -/
theorem coreTemplate_core_group (vertex : ℕ) (ports : List (NCL.WeightedPort ℕ)) :
    ∃ left middle right, (coreTemplate vertex ports).core.ports.map Prod.fst = [left, middle, right] ∧
      .gate (coreTemplate vertex ports).core.kind left middle right ∈ (coreTemplate vertex ports).lower := by
  unfold coreTemplate
  extract_lets a b c kind ta tb tc inside outside
  split_ifs
  · exact ⟨tb, tc, inside, rfl, List.mem_cons_of_mem _ (List.mem_cons_self)⟩
  · exact ⟨inside, ta, tb, rfl, List.mem_cons_of_mem _ (List.mem_cons_self)⟩
  · exact ⟨ta, tb, tc, rfl, List.mem_cons_self⟩

/-- The original tooth crossings retain that same actual core triple and incidence metadata. -/
theorem vertexBlock_core_group (width : ℕ) (input : Input) (vertex : ℕ) :
    ∃ left middle right, (vertexBlock width input vertex).core.ports.map Prod.fst = [left, middle, right] ∧
      .gate (vertexBlock width input vertex).core.kind left middle right ∈ (vertexBlock width input vertex).lower := by
  obtain ⟨left, middle, right, hlabels, hgroup⟩ := coreTemplate_core_group vertex (fan width input vertex)
  exact ⟨left, middle, right, hlabels, List.mem_append_right _ hgroup⟩

/-- Each literal core template partitions all of its own contour tokens into lower groups. -/
private theorem coreTemplate_lower_perm (vertex : ℕ) (ports : List (NCL.WeightedPort ℕ)) :
    ((coreTemplate vertex ports).lower.flatMap TokenGroup.tokens).Perm (coreTemplate vertex ports).order := by
  unfold coreTemplate
  extract_lets a b c kind ta tb tc inside outside
  split_ifs <;>
    simp only [List.flatMap_cons, List.flatMap_nil, TokenGroup.tokens,
      List.cons_append, List.nil_append, List.append_nil]
  · exact (show ([outside] ++ [tb, tc, inside]).Perm ([tb, tc, inside] ++ [outside]) from
      List.perm_append_comm).cons ta
  · exact (show ([tc] ++ [inside, ta, tb]).Perm ([inside, ta, tb] ++ [tc]) from
      List.perm_append_comm).cons outside
  · exact List.Perm.refl _

private theorem paired_tokens_perm {α β : Type} (xs : List α) (a b : α → β) :
    (xs.flatMap fun x => [a x, b x]).Perm (xs.map a ++ xs.reverse.map b) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hmove : (b x :: xs.flatMap (fun x => [a x, b x])).Perm
        ((xs.flatMap fun x => [a x, b x]) ++ [b x]) := by
      exact (show ([b x] ++ xs.flatMap (fun x => [a x, b x])).Perm
        ((xs.flatMap fun x => [a x, b x]) ++ [b x]) from List.perm_append_comm)
    have h := (hmove.trans (ih.append_right [b x])).cons (a x)
    simpa only [List.flatMap_cons, List.cons_append, List.nil_append, List.map_cons,
      List.reverse_cons, List.map_append, List.map_nil, List.append_assoc] using h

/-- The actual whole tooth block partitions its contour into precisely its emitted lower groups. -/
theorem vertexBlock_lower_perm (width : ℕ) (input : Input) (vertex : ℕ) :
    ((vertexBlock width input vertex).lower.flatMap TokenGroup.tokens).Perm
      (vertexBlock width input vertex).order := by
  let hits := toothCrossings width input.drawing vertex
  let b := coreBlock width input vertex
  have hpair := paired_tokens_perm hits (fun c => c.token false) (fun c => c.token true)
  have hcore := coreTemplate_lower_perm vertex (fan width input vertex)
  change (b.lower.flatMap TokenGroup.tokens).Perm b.order at hcore
  have h := hpair.append hcore
  have hswap : ((hits.map (fun c => c.token false) ++ hits.reverse.map (fun c => c.token true)) ++ b.order).Perm
      (hits.map (fun c => c.token false) ++ b.order ++ hits.reverse.map (fun c => c.token true)) := by
    simpa only [List.append_assoc] using
      (List.perm_append_comm : (hits.reverse.map (fun c => c.token true) ++ b.order).Perm
        (b.order ++ hits.reverse.map (fun c => c.token true))).append_left (hits.map (fun c => c.token false))
  simpa only [vertexBlock, List.flatMap_append, List.flatMap_map, Function.comp_def,
    TokenGroup.tokens, hits, b] using h.trans hswap

/-- Every emitted lower gate occupies three consecutive positions in its actual local contour. -/
theorem coreTemplate_gate_contiguous (vertex : ℕ) (ports : List (NCL.WeightedPort ℕ))
    {kind : Shuttle.Kind} {left middle right : Token} :
    .gate kind left middle right ∈ (coreTemplate vertex ports).lower →
      ∃ before after, (coreTemplate vertex ports).order = before ++ [left, middle, right] ++ after := by
  unfold coreTemplate
  extract_lets a b c coreKind ta tb tc inside outside
  split_ifs <;> intro hg <;>
    simp only [List.mem_cons, List.not_mem_nil, or_false, false_or,
      TokenGroup.gate.injEq, reduceCtorEq] at hg
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := hg
    exact ⟨[ta], [outside], rfl⟩
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := hg
    exact ⟨[outside], [tc], rfl⟩
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := hg
    exact ⟨[], [], rfl⟩

/-- Adding the actual tooth crossings retains every core's consecutive three-port block. -/
private theorem vertexBlock_gate_contiguous (width : ℕ) (input : Input) (vertex : ℕ)
    {kind : Shuttle.Kind} {left middle right : Token}
    (hg : .gate kind left middle right ∈ (vertexBlock width input vertex).lower) :
    ∃ before after, (vertexBlock width input vertex).order = before ++ [left, middle, right] ++ after := by
  dsimp only [vertexBlock] at hg ⊢
  rcases List.mem_append.mp hg with hmark | hcore
  · obtain ⟨c, _, h⟩ := List.mem_map.mp hmark
    cases h
  · obtain ⟨before, after, horder⟩ := coreTemplate_gate_contiguous vertex (fan width input vertex) hcore
    refine ⟨(toothCrossings width input.drawing vertex).map (fun c => c.token false) ++ before,
      after ++ (toothCrossings width input.drawing vertex).reverse.map (fun c => c.token true), ?_⟩
    change _ ++ (coreTemplate vertex (fan width input vertex)).order ++ _ = _
    rw [horder]
    simp only [List.append_assoc]

/-- The complete actual lower page covers the literal contour token inventory, with multiplicity. -/
theorem cut_lower_tokens_perm (width : ℕ) (input : Input) :
    ((cut width input).lower.flatMap TokenGroup.tokens).Perm (cut width input).order := by
  simp only [cut, List.flatMap_map, List.flatMap_assoc]
  apply List.Perm.flatMap_left
  intro sv _
  exact vertexBlock_lower_perm width input sv.2

private theorem flatMap_contiguous {α β : Type*} (f : α → List β) {xs : List α} {a : α}
    {word : List β} (ha : a ∈ xs) (hlocal : ∃ before after, f a = before ++ word ++ after) :
    ∃ before after, xs.flatMap f = before ++ word ++ after := by
  obtain ⟨localBefore, localAfter, hlocal⟩ := hlocal
  obtain ⟨beforeBlocks, afterBlocks, hblocks⟩ := List.mem_iff_append.mp ha
  refine ⟨beforeBlocks.flatMap f ++ localBefore, localAfter ++ afterBlocks.flatMap f, ?_⟩
  rw [hblocks, List.flatMap_append, List.flatMap_cons, hlocal]
  simp only [List.append_assoc]

/-- Every output gate is a genuine consecutive triple in the complete computed contour. -/
theorem cut_gate_contiguous (width : ℕ) (input : Input)
    {kind : Shuttle.Kind} {left middle right : Token}
    (hg : .gate kind left middle right ∈ (cut width input).lower) :
    ∃ before after, (cut width input).order = before ++ [left, middle, right] ++ after := by
  let blocks := (vertexOrder width input.drawing).map fun sv => vertexBlock width input sv.2
  have hg' : .gate kind left middle right ∈ blocks.flatMap Block.lower := hg
  obtain ⟨b, hb, hgroup⟩ := List.mem_flatMap.mp hg'
  have hlocal : ∃ before after, b.order = before ++ [left, middle, right] ++ after := by
    obtain ⟨sv, _, rfl⟩ := List.mem_map.mp hb
    exact vertexBlock_gate_contiguous width input sv.2 hgroup
  change ∃ before after, blocks.flatMap Block.order = before ++ [left, middle, right] ++ after
  exact flatMap_contiguous Block.order hb hlocal

/-- Every actual core label in the complete cut belongs to its emitted lower triple. -/
theorem cut_core_group (width : ℕ) (input : Input) {c : Core} (hc : c ∈ (cut width input).cores) :
    ∃ left middle right, c.ports.map Prod.fst = [left, middle, right] ∧
      .gate c.kind left middle right ∈ (cut width input).lower := by
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
  obtain ⟨sv, hsv, rfl⟩ := List.mem_map.mp hb
  obtain ⟨left, middle, right, hlabels, hgroup⟩ := vertexBlock_core_group width input sv.2
  refine ⟨left, middle, right, hlabels, ?_⟩
  exact List.mem_flatMap.mpr ⟨vertexBlock width input sv.2, List.mem_map.mpr ⟨sv, hsv, rfl⟩, hgroup⟩

/-- The complete actual core table preserves every original weighted source incidence. -/
theorem cut_core_ports_perm (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length) :
    ((cut width input).cores.flatMap fun c => c.ports.map Prod.snd).Perm
      (input.graph.vertices.flatMap NCL.Vertex.ports) := by
  simp only [cut, List.flatMap_map, vertexBlock]
  have hlocal := List.Perm.flatMap_left (vertexOrder width input.drawing) (fun sv hsv =>
    coreBlock_ports_perm width input hg (v := sv.2) (by
      have hm := (vertexOrder_perm width input.drawing).mem_iff.mp hsv
      have hb := List.snd_lt_of_mem_zipIdx hm
      simp only [prepare, List.length_map, Nat.add_zero] at hb
      omega))
  apply hlocal.trans
  have hp := (vertexOrder_perm width input.drawing).flatMap_right
    (fun sv => (input.graph.vertices.getD sv.2 ⟨[], 0⟩).ports)
  apply hp.trans
  have hlen : input.graph.vertices.length = (prepare width input.drawing).1.length := by
    simpa only [prepare, List.length_map] using hcount.symm
  have hlookup := List.map_getD_zipIdx (prepare width input.drawing).1 input.graph.vertices ⟨[], 0⟩ hlen
  rw [← List.flatMap_map, hlookup]

/-- Every native output core has the preserved AND heavy-last or OR weight order. -/
theorem cut_core_weights (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    {c : Core} (hc : c ∈ (cut width input).cores) :
    (c.kind = .andGate ∧ c.ports.map (fun p => p.2.2) = [1, 1, 2]) ∨
      (c.kind = .orGate ∧ c.ports.map (fun p => p.2.2) = [2, 2, 2]) := by
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
  obtain ⟨sv, hsv, rfl⟩ := List.mem_map.mp hb
  apply coreBlock_weights width input hg
  have hm := (vertexOrder_perm width input.drawing).mem_iff.mp hsv
  have hi := List.snd_lt_of_mem_zipIdx hm
  simp only [prepare, List.length_map, Nat.add_zero] at hi
  omega

end PushPuzzle.PushS.Comb
