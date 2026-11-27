/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupportSouthPayment
public import Push.AcceptanceProgramLowerFinishStock
import all Push.AcceptanceSoundnessSupportCutPayment
import all Push.AcceptanceSoundnessSupportLanes
import all Push.AcceptanceSoundnessSupportClean

/-! The actual payment of an original central marker certifies that its lower-page column was already empty. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS AcceptanceProgram

/-- Every original central marker is paid by its actual lower finishing round, with no lower-page hole remaining beforehand. -/
theorem canonical_cut_lower_exhausted (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.centralMarkers p) (hy : q.2.val = p.D) :
    ∃ pay : RoundPayment (pageCheckStages l p) (pageCheckTarget l p target)
        (roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
          (targetHoles l p target) (PushS.holes t) 25) q,
      pay.side = .south ∧
        (∀ r ∈ pay.input, r.1 = q.1 → r.2.val ≤ p.D) ∧
          (∀ r ∈ pay.output, r.1 = q.1 → r.2.val < p.D) := by
  obtain ⟨pay, hsouth, cols, hrequests, _⟩ := canonical_cut_payment_lower l p hl hM haxes initial target hr ha hq hy
  have hstage : Template.read pay.side pay.requests = .read .south (prefixRequests cols fun _ => p.D + 1) :=
    congrArg₂ Template.read hsouth hrequests
  have hsplit : pageChecks l p .lower ++ pageChecks l p .upper =
      pay.before ++ .read .south (prefixRequests cols fun _ => p.D + 1) :: pay.after :=
    pay.split.trans (congrArg (fun stage => pay.before ++ stage :: pay.after) hstage)
  have hread : Scan.eval (instructions (emit [.read .south (prefixRequests cols fun _ => p.D + 1)]
      (emit pay.before (pageCheckTarget l p target)).remaining).rounds) pay.input = some pay.output := by
    simpa only [hsouth, hrequests] using pay.read_eval
  have hline : ReadTouches (.read .south (prefixRequests cols fun _ => p.D + 1)) q := by
    simpa only [ReadTouches, hsouth, hrequests] using pay.on_line
  have hx := prefix_touches p .south cols _ hline
  have hbound := lowerFinish_target_front_card_le_one l p hl hM haxes target pay.before pay.after cols hsplit q.1.val hx
  have hcert := south_round_front_at_most_one_exhausted cols (fun _ => p.D + 1)
    (emit pay.before (pageCheckTarget l p target)).remaining pay.input pay.output hx hread pay.present pay.removed hbound
  refine ⟨pay, hsouth, ?_⟩
  simpa only [hy] using hcert

end PushPuzzle.Push.AcceptanceSoundness
