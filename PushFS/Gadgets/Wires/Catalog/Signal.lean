/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.RawRelay
public import PushFS.Gadgets.Wires.Catalog.Endpoints

/-! Full seven-cell endpoint soundness on arbitrary successful ambient trajectories. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog

open Soundness Polyline
set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

/-- The actual first physical endpoint has crossed its source-route threshold. -/
def sourceHigh {W H : ℕ} (k : Kind) (dx dy : ℕ) (p : PushFS.Cell W H) : Prop :=
  match k with
  | .east | .eastSouth=>dx+3≤p.1.val
  | .west | .westSouth=>p.1.val≤dx+200001
  | .south | .southEast | .southWest=>dy+3≤p.2.val

/-- The true last physical endpoint has crossed its outgoing source-route threshold. -/
def targetHigh {W H : ℕ} (k : Kind) (dx dy : ℕ) (p : PushFS.Cell W H) : Prop :=
  match k with
  | .east | .southEast=>dx+200001≤p.1.val
  | .west | .southWest=>p.1.val≤dx+3
  | .south | .westSouth | .eastSouth=>dy+198062≤p.2.val

variable {I : Instance} {L : Type} [Fintype L] {M : SlotMatching I L}
    {S T : LabelledState L I.width I.height}

/-- The entire real padded cell transmits its signal; the hypotheses mention only walls, physical slots and the surrounding successful path. -/
theorem signal {k : Kind} {a b : Bool} (g : StorageImage M (slotMatching k a b))
    (h : Successful M S T) (cert : Certificate I) (ho : M.Ordered)
    (hin : sourceHigh k g.dx g.dy (S.position (g.labels (firstLabel k)))) :
    targetHigh k g.dx g.dy (S.position (g.labels (lastLabel k))) := by
  have hfit : g.dx+200005≤I.width := g.fit_x
  have vfit : g.dy+198066≤I.height := g.fit_y
  cases k
  · have hh:=(g.comp (baseImage .east a b)).east_chain h cert ho (by
      change g.dx+0+3≤(S.position (g.labels (firstLabel .east))).1.val
      exact hin)
    change g.dx+0+200000+1≤(S.position (g.labels (lastLabel .east))).1.val at hh
    exact hh
  · have hh:=(g.comp (baseImage .west a b)).west_chain h cert ho (by
      change (S.position (g.labels (firstLabel .west))).1.val≤g.dx+0+200000+1
      exact hin)
    exact hh
  · have hh:=(g.comp (baseImage .south a b)).south_chain h cert ho (by
      change g.dy+0+3≤(S.position (g.labels (firstLabel .south))).2.val
      exact hin)
    exact hh
  · have hh:=NormalRelay.signal (g.comp (baseImage .westSouth a b)) h cert ho (by
      change (S.position (g.labels (firstLabel .westSouth))).1.val≤g.dx+99992+99970+39
      change (S.position (g.labels (firstLabel .westSouth))).1.val≤g.dx+200001 at hin
      omega)
    change g.dy+99023+98999+40≤(S.position (g.labels (lastLabel .westSouth))).2.val at hh
    change g.dy+198062≤(S.position (g.labels (lastLabel .westSouth))).2.val
    omega
  · let z:=g.comp (baseImage .eastSouth a b)
    let e:=GridIsometry.reflectX I.width I.height
    have h1:=orient_successful M h e
    have c1:=reflectXCertificate M cert
    have o1:=ordered_reflectX M ho
    have hi : (S.position (g.labels (firstLabel .eastSouth))).1.val≥g.dx+3 := hin
    have hh:=OutRelay.signal z.unreflectX h1 c1 o1 (by
      change I.width-((S.position (g.labels (firstLabel .eastSouth))).1.val+1)≤
        I.width-(g.dx+0)-100013+99970+39
      omega)
    change g.dy+99023+98979+60≤(S.position (g.labels (lastLabel .eastSouth))).2.val at hh
    change g.dy+198062≤(S.position (g.labels (lastLabel .eastSouth))).2.val
    omega
  · let z:=g.comp (baseImage .southEast a b)
    let e:=GridIsometry.transpose I.width I.height
    let M1:=M.reorient e
    have h1:=orient_successful M h e
    have c1:=transposeCertificate M cert
    have o1:=ordered_transpose M ho
    let f:=GridIsometry.reflectX I.height I.width
    have h2:=orient_successful M1 h1 f
    have c2:=reflectXCertificate M1 c1
    have o2:=ordered_reflectX M1 o1
    have hi : g.dy+3≤(S.position (g.labels (firstLabel .southEast))).2.val := hin
    have hh:=InRelay.signal z.untranspose.unreflectX h2 c2 o2 (by
      change I.height-((S.position (g.labels (firstLabel .southEast))).2.val+1)≤
        I.height-(g.dy+0)-99044+98981+59
      omega)
    change g.dx+99992+99969+40≤(S.position (g.labels (lastLabel .southEast))).1.val at hh
    change g.dx+200001≤(S.position (g.labels (lastLabel .southEast))).1.val
    omega
  · let z:=g.comp (baseImage .southWest a b)
    let e:=GridIsometry.reflectX I.width I.height
    let M1:=M.reorient e
    have h1:=orient_successful M h e
    have c1:=reflectXCertificate M cert
    have o1:=ordered_reflectX M ho
    let f:=GridIsometry.transpose I.width I.height
    let M2:=M1.reorient f
    have h2:=orient_successful M1 h1 f
    have c2:=transposeCertificate M1 c1
    have o2:=ordered_transpose M1 o1
    let v:=GridIsometry.reflectX I.height I.width
    have h3:=orient_successful M2 h2 v
    have c3:=reflectXCertificate M2 c2
    have o3:=ordered_reflectX M2 o2
    have hi : g.dy+3≤(S.position (g.labels (firstLabel .southWest))).2.val := hin
    have hh:=NormalRelay.signal z.unreflectX.untranspose.unreflectX h3 c3 o3 (by
      change I.height-((S.position (g.labels (firstLabel .southWest))).2.val+1)≤
        I.height-(g.dy+0)-99044+99001+39
      omega)
    change I.width-(g.dx+0)-100013+99969+40≤
      I.width-((S.position (g.labels (lastLabel .southWest))).1.val+1) at hh
    change (S.position (g.labels (lastLabel .southWest))).1.val≤g.dx+3
    have hb:=(S.position (g.labels (lastLabel .southWest))).1.isLt
    omega

end PushPuzzle.PushFS.Gadgets.Wires.Catalog
