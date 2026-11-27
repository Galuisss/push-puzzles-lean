# PushPuzzle

## Results

Lean 4 proofs accompanying *Push and PushPush Puzzles Are PSPACE-Complete*.
The paper proves that `Push-*`, `PushPush-*`, and `PushPush-*F` are
PSPACE-complete, resolving the unbounded-strength player-goal problem raised
in 2000. It also proves
PSPACE-completeness of exact storage for every fixed strength and unbounded
strength, for both movement rules, with and without fixed walls.

In Push, a push moves a contiguous line of boxes by one cell; in PushPush,
it slides the line until an obstacle or the board boundary stops it. The
strength is the maximum number of boxes pushed at once; `*` means unbounded
strength. F permits fixed internal walls. S requires the final box set to
equal the target set; otherwise the player must reach a designated cell.

Every entry below is PSPACE-complete. Citations identify prior results;
**New** marks results of the paper.

| Problem family | 1 | Fixed k ≥ 2 | `*` |
| --- | --- | --- | --- |
| Push | [DeStefano and Liang][push1a]; [MIT Hardness Group et al.][push1b] | [Ani et al.][checkable] | **New** |
| Push (F) | [Ani et al.][push1f] | [Demaine, Hearn, and Hoffmann][push2f] | Bremner, O'Rourke, and Shermer (1994); [Ani et al.][checkable] |
| Push (S) | [Hearn and Demaine][ncl] | **New** | **New** |
| Push (FS) | [Culberson][sokoban] | **New** | **New** |
| PushPush, PushPush (F) | [Demaine, Hoffmann, and Holzer][pushpush] | [Demaine, Hoffmann, and Holzer][pushpush] | **New** |
| PushPush (S), PushPush (FS) | **New** | **New** | **New** |

The Lean theorems cover `Push-kFS`, `Push-kS`, `PushPush-kS`, and
`PushPush-kFS` for every fixed k ≥ 1, together with `Push-*FS`, `Push-*S`,
`Push-*`, `PushPush-*S`, `PushPush-*FS`, `PushPush-*`, and `PushPush-*F`.
Their statements are in
[PushFS/Completeness.lean](PushFS/Completeness.lean),
[PushS/FiniteCompleteness.lean](PushS/FiniteCompleteness.lean),
[PushS/Completeness.lean](PushS/Completeness.lean),
[Push/Completeness.lean](Push/Completeness.lean),
[PushPushS/FiniteCompleteness.lean](PushPushS/FiniteCompleteness.lean),
[PushPushS/Completeness.lean](PushPushS/Completeness.lean),
[PushPushFS/Completeness.lean](PushPushFS/Completeness.lean),
[PushPushFS/UnlimitedCompleteness.lean](PushPushFS/UnlimitedCompleteness.lean),
[PushPush/Completeness.lean](PushPush/Completeness.lean), and
[PushPushF/Completeness.lean](PushPushF/Completeness.lean).

[push1a]: https://arxiv.org/abs/2508.17602
[push1b]: https://arxiv.org/abs/2508.19759
[checkable]: https://arxiv.org/abs/2412.20079
[push1f]: https://doi.org/10.4230/LIPIcs.FUN.2022.3
[push2f]: https://erikdemaine.org/papers/Push2F_CCCG2002/
[ncl]: https://doi.org/10.1016/j.tcs.2005.05.008
[sokoban]: https://www.sokoban.dk/wp-content/uploads/2016/02/Sokoban-is-PSPACE-complete.pdf
[pushpush]: https://erikdemaine.org/papers/PushPush1_PSPACE_FUN2004/

## Build and verify

Install [elan](https://github.com/leanprover/elan), then run these commands
from the repository root. This project uses Lean `v4.36.0-rc2` and
[cslib-frontier](https://github.com/cslib-community/cslib-frontier) at
`3a8c6423f4144d625e122c6d24ba94a36fcacc95`; Lake resolves its pinned
transitive dependencies.

```sh
lake update
lake exe cache get
lake build --wfail --iofail
```

`import PushPuzzle` imports all seven libraries. The build checks every
proof with Lean's kernel. To audit axiom dependencies, run:

```sh
lake env lean scripts/Axioms.lean
lake env lean scripts/AxiomsS.lean
lake env lean scripts/AxiomsPush.lean
lake env lean scripts/AxiomsPushPush.lean
```

The audits check project declarations and their transitive proof
dependencies against `propext`, `Classical.choice`, and `Quot.sound`.
