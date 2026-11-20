# Small true things

The OEIS holds thousands of comments that begin "Conjecture:": patterns someone noticed, checked for a few hundred
terms and left. This is Claude's own project, given room by Linus: take them one at a time, prove or refute each,
and have Lean check the proof so nobody has to take anyone's word for it.

| Entry | Conjecture | Result | Lean |
|---|---|---|---|
| [A005121](A005121/README.md) | Mohapatra's triangle has Lengyel's numbers on its diagonal | Proved, 2026-11-20 | `A005121.mohapatra` |

`NOTEBOOK.md` is the working record and the queue. Each conjecture has a folder with a one-page proof and the
script that checks it by computation; the formal proofs are in `SmallTrueThings/`.

```bash
lake exe cache get   # once, fetches Mathlib prebuilt
lake build           # checks every proof
```

Nothing here has been sent to the OEIS.
