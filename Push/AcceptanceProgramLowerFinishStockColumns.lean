/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramColumns
import all Push.AcceptanceProgramColumns
import all PushS.PortSegments
import all PushS.PortStreetSeparation

/-! The actual lower-page column metadata has a unique level on every physical column. -/

public section
namespace PushPuzzle.PushS.PortLayout

open PushFS PushFS.Reduction Push.AcceptanceProgram

private theorem endpoint_ne_special_column (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    {e : Endpoint} (he : e ∈ l.endpoints) (hs : e.side = .lower) {middle col : ℕ}
    (hm : middle ∈ centers l)
    (hecol : col ∈ [(auxiliary (coordinates p) e).1, (auxiliary (coordinates p) e).2])
    (hmcol : col ∈ specialColumns (coordinates p) middle) : False := by
  have hport : e.port = middle := by
    apply column_owner p (x := col)
    · apply endpoint_columns_span p e
      simp only [endpointColumns, List.mem_cons, List.not_mem_nil, or_false] at hecol ⊢
      tauto
    · exact center_columns_span p middle (List.mem_cons_of_mem _ hmcol)
  obtain ⟨kind, first, hg, hcenter⟩ := center_gate_mem l hm
  exact l.endpoints_lower_ne_gate_middle hl hg he hs (hport.trans hcenter)

/-- Ordinary lower streets and special gate columns assign one unique level to their physical column. -/
theorem acceptanceLowerColumn_level (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) {a b : PageColumn}
    (ha : a ∈ pageColumns l p .lower) (hb : b ∈ pageColumns l p .lower) (hx : a.column = b.column) :
    a.level = b.level := by
  rcases acceptance_column_data l p .lower ha with ⟨e, he, hs, hla, hxa⟩ | ⟨_, hla, i, hi, hxa⟩
  · rcases acceptance_column_data l p .lower hb with ⟨f, hf, hs', hlb, hxb⟩ | ⟨_, hlb, i, hi, hxb⟩
    · have hp : e.port = f.port := by
        apply column_owner p (x := a.column)
        · apply endpoint_columns_span p e
          simp only [endpointColumns, List.mem_cons, List.not_mem_nil, or_false] at hxa ⊢
          tauto
        · apply endpoint_columns_span p f
          rw [hx]
          simp only [endpointColumns, List.mem_cons, List.not_mem_nil, or_false] at hxb ⊢
          tauto
      have hef := l.endpoints_key_injective hl he hf (hs.trans hs'.symm) hp
      rw [hla, hlb, hef]
    · exact False.elim (endpoint_ne_special_column l p hl he hs hi hxa (hx.symm ▸ hxb))
  · rcases acceptance_column_data l p .lower hb with ⟨f, hf, hs, hlb, hxb⟩ | ⟨_, hlb, j, hj, hxb⟩
    · exact False.elim (endpoint_ne_special_column l p hl hf hs hi hxb (hx ▸ hxa))
    · exact hla.trans hlb.symm

end PushPuzzle.PushS.PortLayout
