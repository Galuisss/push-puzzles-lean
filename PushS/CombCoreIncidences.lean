/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombCore
public import PushS.CombConfigurationCore
public import PushS.CombTopologyPolyTime
import all PushS.CombPartition

/-!
# Exact original incidences of the actual core tokens

Read each original native port from the actual core metadata. Native incidence uniqueness makes
the lookup single-valued, retaining the original weighted port and identifying its actual direct
tip or inside-rotation token.

## Main definitions

* `Comb.Core.portToken`: the actual core token for one original native port.

## Main results

* `Comb.corePortToken_eq`: exact lookup at every original metadata entry.
* `Comb.corePortToken_spec`: original weighted native incidences retain their actual core token.
-/

public section

namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

open _root_.Turing.MultiTapeTM

/-- The actual core token carrying the specified original native port. -/
def Core.portToken (core : Core) (port : NCL.Port ℕ) : Token :=
  ((core.ports.filter (fun (_, ⟨source, _⟩) => source == port)).map Prod.fst).headD (.tip 0 false)

/-- The original weighted incidence lookup is standard polynomial-time. -/
theorem computableInPolyTime_portToken :
    ComputableInPolyTime (fun p : Core × NCL.Port ℕ => p.1.portToken p.2)
      (encPair encCore (NCL.encPort encNat)) encToken := by
  unfold Core.portToken
  fun_prop

private theorem sourceKeys_nodup (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (v : Fin input.graph.vertices.length) :
    ((coreBlock width input v.val).core.ports.map (fun tp => incidenceToken tp.2.1)).Nodup := by
  have hp := (coreTemplate_ports_perm v.val (fan width input v.val)
    (fan_length width input hg v.isLt)).map (fun pw => incidenceToken pw.1)
  have hn := fan_tips_nodup width input hg v.isLt
  simpa only [coreBlock, List.map_map, Function.comp_def] using hp.nodup_iff.mpr hn

/-- Reading an original native port returns exactly its actual core metadata token. -/
theorem corePortToken_eq (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (v : Fin input.graph.vertices.length) {token : Token} {port : NCL.Port ℕ} {weight : ℕ}
    (h : (token, ⟨port, weight⟩) ∈ (coreBlock width input v.val).core.ports) :
    (coreBlock width input v.val).core.portToken port = token := by
  let core := (coreBlock width input v.val).core
  let selected := core.ports.filter (fun (_, ⟨source, _⟩) => source == port)
  have hm : (token, ⟨port, weight⟩) ∈ selected := List.mem_filter.mpr ⟨h, by simp⟩
  cases hsel : selected with
  | nil => simp only [hsel, List.not_mem_nil] at hm
  | cons head tail =>
    have hh : head ∈ selected := hsel ▸ List.mem_cons_self
    obtain ⟨hh, he⟩ := List.mem_filter.mp hh
    have he' : head.2.1 = port := beq_iff_eq.mp he
    have hkey : incidenceToken head.2.1 = incidenceToken port := congrArg incidenceToken he'
    have heq := List.inj_on_of_nodup_map (sourceKeys_nodup width input hg v) hh h hkey
    have ht : core.portToken port = head.1 := by
      change (selected.map Prod.fst).headD (.tip 0 false) = head.1
      simp only [hsel, List.map_cons, List.headD_cons]
    exact ht.trans (congrArg Prod.fst heq)

/-- Every original weighted native incidence retains its exact metadata entry at the core. -/
theorem corePortToken_spec (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (v : Fin input.graph.vertices.length) {port : NCL.Port ℕ} {weight : ℕ}
    (h : (⟨port, weight⟩ : NCL.WeightedPort ℕ) ∈ (input.graph.vertices.get v).ports) :
    ((coreBlock width input v.val).core.portToken port, ⟨port, weight⟩) ∈
      (coreBlock width input v.val).core.ports := by
  have hp := coreBlock_ports_perm width input hg v.isLt
  rw [List.getD_eq_get _ _ v] at hp
  obtain ⟨⟨token, pw⟩, ht, he⟩ := List.mem_map.mp (hp.mem_iff.mpr h)
  cases he
  rwa [corePortToken_eq width input hg v ht]

/-- Every actual core port is its original direct tip or its own inside-rotation token. -/
theorem corePort_role (width : ℕ) (input : Input) (vertex : ℕ)
    {tp : Token × (NCL.WeightedPort ℕ)} (h : tp ∈ (coreBlock width input vertex).core.ports) :
    let (token, ⟨port, _⟩) := tp
    token = incidenceToken port ∨ token = .rotation vertex true := by
  change tp.1 = incidenceToken tp.2.1 ∨ tp.1 = .rotation vertex true
  unfold coreBlock coreTemplate at h
  extract_lets a b c kind ta tb tc inside outside at h
  split_ifs at h <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  all_goals rcases h with rfl | rfl | rfl
  all_goals first | exact .inl rfl | exact .inr rfl

/-- The original native incidence is represented by its direct tip or its same actual rotation.
-/
theorem corePortToken_role (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (v : Fin input.graph.vertices.length) {port : NCL.Port ℕ} {weight : ℕ}
    (h : (⟨port, weight⟩ : NCL.WeightedPort ℕ) ∈ (input.graph.vertices.get v).ports) :
    (coreBlock width input v.val).core.portToken port = incidenceToken port ∨
      (coreBlock width input v.val).core.portToken port = .rotation v.val true :=
  corePort_role width input v.val (corePortToken_spec width input hg v h)

/-- Distinct original incidences at the same actual core retain distinct core axes. -/
theorem corePortToken_injective (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (v : Fin input.graph.vertices.length) {left right : NCL.Port ℕ} {a b : ℕ}
    (hl : (⟨left, a⟩ : NCL.WeightedPort ℕ) ∈ (input.graph.vertices.get v).ports)
    (hr : (⟨right, b⟩ : NCL.WeightedPort ℕ) ∈ (input.graph.vertices.get v).ports)
    (he : (coreBlock width input v.val).core.portToken left =
      (coreBlock width input v.val).core.portToken right) : left = right := by
  have hl' := corePortToken_spec width input hg v hl
  have hr' := corePortToken_spec width input hg v hr
  have hn := coreTokens_nodup width input hg v.isLt
  generalize hcore : (coreBlock width input v.val).core = core at he hl' hr' hn
  have hp : (core.portToken left, (⟨left, a⟩ : NCL.WeightedPort ℕ)) = (core.portToken right, ⟨right, b⟩) :=
    @List.inj_on_of_nodup_map _ _ Prod.fst core.ports hn
      (core.portToken left, ⟨left, a⟩) hl' (core.portToken right, ⟨right, b⟩) hr' he
  exact congrArg (fun tp => tp.2.1) hp

/-- A local rotation is present exactly when its inside axis carries an original weighted port.
-/
theorem coreTemplate_rotation_mem (vertex : ℕ) (ports : List (NCL.WeightedPort ℕ)) (side : Bool) :
    .rotation vertex side ∈ (coreTemplate vertex ports).order ↔
      ∃ port weight, (.rotation vertex true, ⟨port, weight⟩) ∈ (coreTemplate vertex ports).core.ports := by
  unfold coreTemplate
  extract_lets a b c kind ta tb tc inside outside
  split_ifs <;> cases side <;> simp [inside, outside, ta, tb, tc, incidenceToken]

end PushPuzzle.PushS.Comb
