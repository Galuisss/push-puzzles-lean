/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.Partner

/-! A literal two-port ear subdivision of an upper pair. -/

@[expose] public section
namespace PushPuzzle.Push.Partner

open PushS

/-- Write an undirected upper arc with its left port first. -/
def sortPair (a b : ℕ) : ℕ × ℕ := (min a b, max a b)

/-- The two actual incidences of an upper arc. -/
def pairPorts (ab : ℕ × ℕ) : List ℕ := [ab.1, ab.2]

private theorem sortPair_ports (a b : ℕ) : (pairPorts (sortPair a b)).Perm [a, b] := by
  by_cases h : a ≤ b
  · simp only [sortPair, min_eq_left h, max_eq_right h, pairPorts]
    exact .refl _
  · simp only [sortPair, min_eq_right (by omega : b ≤ a), max_eq_left (by omega : b ≤ a), pairPorts]
    exact List.Perm.swap _ _ []

def mapPair (cut : ℕ) (ab : ℕ × ℕ) : ℕ × ℕ := (shift cut ab.1, shift cut ab.2)

/-- Replace one selected upper arc by two arcs through a new lower WIRE. -/
def ear (l : PortLayout) (cut : ℕ) (ab : ℕ × ℕ) : PortLayout where
  portCount := l.portCount + 2
  upperPairs := sortPair (shift cut ab.1) (cut + 1) ::
    sortPair (shift cut ab.2) cut :: (l.upperPairs.erase ab).map (mapPair cut)
  lowerGroups := l.lowerGroups.map (mapGroup cut) ++ [.wire cut (cut + 1)]

/-- A left ear buffers the first two ports of an actual consecutive triple. -/
def leftEar (l : PortLayout) (first : ℕ) : PortLayout := ear l first (first, first + 1)

/-- A right ear buffers the last two ports of an actual consecutive triple. -/
def rightEar (l : PortLayout) (first : ℕ) : PortLayout := ear l (first + 3) (first + 1, first + 2)

/-- No old lower group is removed by the actual ear construction. -/
theorem mapGroup_mem_ear {l : PortLayout} {cut : ℕ} {ab : ℕ × ℕ} {g : LowerGroup}
    (hg : g ∈ l.lowerGroups) : mapGroup cut g ∈ (ear l cut ab).lowerGroups :=
  List.mem_append_left _ (List.mem_map.mpr ⟨g, hg, rfl⟩)

theorem ear_wire_mem (l : PortLayout) (cut : ℕ) (ab : ℕ × ℕ) :
    LowerGroup.wire cut (cut + 1) ∈ (ear l cut ab).lowerGroups :=
  List.mem_append_right _ (List.mem_singleton.mpr rfl)

/-- The actual lower port word is exactly the old word followed by the new WIRE. -/
theorem ear_lower_ports (l : PortLayout) (cut : ℕ) (ab : ℕ × ℕ) (hs : SafeCut l cut) :
    (ear l cut ab).lowerGroups.flatMap groupPorts =
      (l.lowerGroups.flatMap groupPorts).map (shift cut) ++ [cut, cut + 1] := by
  simp only [ear, List.flatMap_append, List.flatMap_map, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, groupPorts, List.map_flatMap]
  congr 1
  apply List.flatMap_congr
  intro g hg
  exact mapGroup_ports hs g hg

/-- Every old upper endpoint occurs once more at its shifted port, with just two new endpoints. -/
theorem ear_upper_ports (l : PortLayout) (cut : ℕ) (ab : ℕ × ℕ) (hp : ab ∈ l.upperPairs) :
    ((ear l cut ab).upperPairs.flatMap pairPorts).Perm
      ((l.upperPairs.flatMap pairPorts).map (shift cut) ++ [cut, cut + 1]) := by
  have hp' := (List.perm_cons_erase hp).flatMap_right pairPorts
  have hm := hp'.map (shift cut)
  have hs₁ := sortPair_ports (shift cut ab.1) (cut + 1)
  have hs₂ := sortPair_ports (shift cut ab.2) cut
  have hs := (hs₁.append hs₂).append_right
    (((l.upperPairs.erase ab).map (mapPair cut)).flatMap pairPorts)
  apply Multiset.coe_eq_coe.mp
  have hm' := Multiset.coe_eq_coe.mpr hm
  have hs' := Multiset.coe_eq_coe.mpr hs
  simp only [List.append_assoc] at hs'
  simp only [ear, List.flatMap_cons] at hs' ⊢
  rw [hs']
  simp only [List.flatMap_cons, pairPorts, List.map_append, List.map_cons, List.map_nil,
    ] at hm'
  have hrest : (((l.upperPairs.erase ab).map (mapPair cut)).flatMap pairPorts) =
      ((l.upperPairs.erase ab).flatMap pairPorts).map (shift cut) := by
    simp only [List.flatMap_map, List.map_flatMap]
    rfl
  rw [hrest]
  simp only [← Multiset.coe_add]
  rw [hm']
  simp only [← Multiset.coe_add]
  change (({shift cut ab.1} : Multiset ℕ) + {cut + 1}) + (({shift cut ab.2} + {cut}) + _) =
    (({shift cut ab.1} + {shift cut ab.2}) + _) + ({cut} + {cut + 1})
  ac_rfl

end PushPuzzle.Push.Partner
