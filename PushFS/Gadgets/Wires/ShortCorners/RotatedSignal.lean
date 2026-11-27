/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.ShortCorners.Signal

/-! The complete actual protected short-corner signal survives every rectangular D4 image. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.ShortCorners

open Catalog Soundness Polyline

def sourceHigh {W H : ℕ} (k : Kind) (o : RectOrientation) (dx dy : ℕ) (p : Cell W H) : Prop :=
  ((o.undo W H).cells p).1.val+1≤(o.undoOffset W H (width k) (height k) dx dy).1+sourceX k

def targetHigh {W H : ℕ} (k : Kind) (o : RectOrientation) (dx dy : ℕ) (p : Cell W H) : Prop :=
  (o.undoOffset W H (width k) (height k) dx dy).2+lastY k+1≤((o.undo W H).cells p).2.val

variable {I : Instance} {L : Type} [Fintype L] {M : SlotMatching I L}

/-- All real boxes, walls, player steps and terminal identities are retained by the ambient inverse rotation. -/
theorem rotated_signal (k : Kind) (o : RectOrientation) (a b : Bool)
    (g : StorageImage M ((slotMatching k a b).reorient ((o.axis (width k) (height k)).geometry)))
    {S T : LabelledState L I.width I.height} (hs : Successful M S T) (cert : Certificate I) (ordered : M.Ordered)
    (hin : sourceHigh k o g.dx g.dy (S.position (g.labels (first k)))) :
    targetHigh k o g.dx g.dy (S.position (g.labels (last k))) :=
  signal k (StorageImage.straighten (N:=slotMatching k a b) o g)
    (orient_successful M hs (o.undo I.width I.height))
    (rectCertificate M cert o.inverse) (rectOrdered M ordered o.inverse) hin

end PushPuzzle.PushFS.Gadgets.Wires.ShortCorners
