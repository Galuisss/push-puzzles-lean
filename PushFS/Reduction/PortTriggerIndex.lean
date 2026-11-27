/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PortIncidence
public import PushFS.Reduction.TriggerReadout

/-! Attach distinct physical triggers to the actual unique source-port incidences. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.TriggerReadout


open Cslib.Complexity.NCL PushPuzzle.NCL

variable {V E Label : Type} [Fintype V] [Fintype E] [Fintype Label]
  {w h : ℕ} {G : ConstraintGraph V E}

/-- Source incidence uniqueness supplies the physical port indexing used only in the reverse proof. -/
noncomputable def ofIncidences (hG : G.WellFormed) (boxes : PortIncidence G ↪ Label)
    (threshold : PortIncidence G → Cell w h → Bool) : TriggerReadout E Label w h where
  label := (portIncidenceEquiv hG).symm.toEmbedding.trans boxes
  threshold p := threshold ((portIncidenceEquiv hG).symm p)

/-- Reading a real source incidence uses exactly its own physical box and threshold. -/
theorem ofIncidences_read (hG : G.WellFormed) (boxes : PortIncidence G ↪ Label)
    (threshold : PortIncidence G → Cell w h → Bool) (S : LabelledState Label w h)
    (i : PortIncidence G) :
    (ofIncidences hG boxes threshold).read S (incidentPort G i) =
      threshold i (S.position (boxes i)) := by
  change (ofIncidences hG boxes threshold).read S ((portIncidenceEquiv hG) i) = _
  simp only [read, ofIncidences, Equiv.symm_apply_apply, Function.Embedding.trans_apply,
    Equiv.toEmbedding_apply]

/-- Literal canonical trigger coordinates establish the complete original source orientation. -/
theorem ofIncidences_full (hG : G.WellFormed) (boxes : PortIncidence G ↪ Label)
    (threshold : PortIncidence G → Cell w h → Bool) (S : LabelledState Label w h)
    (s : E → Bool)
    (hs : ∀ i, threshold i (S.position (boxes i)) = PortClaims.full s (incidentPort G i)) :
    (ofIncidences hG boxes threshold).read S = PortClaims.full s := by
  funext p
  obtain ⟨i, rfl⟩ := incidentPort_surjective hG p
  exact (ofIncidences_read hG boxes threshold S i).trans (hs i)

end PushPuzzle.PushFS.Reduction.TriggerReadout
