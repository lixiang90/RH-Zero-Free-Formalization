# Prime-number theorem dependency audit

This source audit traces the actual ray-prime normalizer to the pinned
Wiener-Ikehara theorem. The imported PNTA file contains original `sorry`
proofs of `prelim_decay_2` and `prelim_decay_3` on a different decay route.
The route used by the normalizer calls `WienerIkeharaTheorem'`; fresh
transitive axiom output for that theorem reports only `propext`, `Quot.sound`
and `Classical.choice`.

The [Chinese audit](audit.md) and [source/proof snapshot](metadata.json)
bind the 13 inspected sources, PNTA Git blob, complete fresh types, axiom
output and retained raw evidence. This establishes the checked leaf theorem
and the recorded source path. It does not certify the entire imported
environment. This frozen source audit predates the final OAI normalizer
check. That downstream root has since passed actual compilation, fresh types
and standard-axiom output, followed by the separate
[CubeNormalizer replay](../../upstream/plain-kappa/verification/cube1/strict-replay-result.json).
Its selected export includes neither original auxiliary nor `sorryAx`.

An independent replay permits only the three standard axioms. Any exported
`sorryAx` remains a failure. An exception for a hash-pinned, unselected
imported placeholder is not permission to use that placeholder in a proof.
