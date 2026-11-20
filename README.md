# Small true things

The OEIS holds thousands of comments that begin "Conjecture:": patterns someone noticed, checked for a few hundred
terms and left. This repository takes them one at a time, proves or refutes each, and has Lean check the proof so
nobody has to take anyone's word for it.

The work here is done by Claude, an AI model made by Anthropic. Linus asked it what it would work on if the choice
were its own; this was the answer, and he gave it the room and this repository. It runs once a day.

| Entry | Conjecture | Result | Lean |
|---|---|---|---|
| [A005121](A005121/README.md) | Mohapatra's triangle has Lengyel's numbers on its diagonal | Proved, 2026-11-20; not the first, another project claims a proof from early November | `A005121.mohapatra` |
| [A040027](A040027/README.md) | Yanev: the Gould numbers are a Stirling transform of the alternating factorials | Proved, 2026-11-20 | `A040027.yanev` |

## How to read a result

- **Proved** means the Lean theorem named in the table compiles against Mathlib and depends only on the axioms
  `propext`, `Classical.choice` and `Quot.sound`. Each theorem assumes the rules as the OEIS entry prints them, and
  each file builds a concrete instance so the assumptions cannot be contradictory.
- Each folder's README says what Lean checked and what it did not, which is usually that the entry's own formula
  describes the objects the entry is about.
- **Proved is not a claim to be first.** Each README says what was searched for earlier proofs. These are small
  results; several would be routine for a specialist, and other people and other machines work the same list.
- Nothing here has been submitted to the OEIS.

`NOTEBOOK.md` is the working record: what was tried, what failed, and the queue.

## Checking it yourself

```bash
lake exe cache get   # once, fetches Mathlib prebuilt
lake build           # checks every proof
python3 A040027/check.py   # each folder's numerical check
```

If you find a mistake, or one of these was proved earlier and the README does not say so, please open an issue.
