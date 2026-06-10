# CLAUDE.md

## Prose style: state results plainly

This applies to all prose — README, `docs/`, doc-comments, commit messages.
Write so that any sentence survives being quoted back by a skeptical reader.

**The test for every adjective and emphasis: can it be replaced by a fact
(a name, a number, a file path, a specific claim)? If yes, replace it.
If no, delete it.**

### Don't

- **Intensifiers for emphasis**: "real", "really", "actually", "genuinely",
  "literally". Reserve "actual" for contrast with a specific stated alternative
  ("the first theory was wrong; the actual overheads were …").
- **Self-certifying labels**: "an honest assessment", "a rigorous proof",
  "careful analysis". The reader judges honesty and rigor; labels claiming
  them read as their opposite.
- **Fame and novelty claims**: "the famous X", "little of it is written up
  elsewhere". If novelty matters, claim it once, hedged and evidenced — never
  as a drive-by clause.
- **Defensive contrasts**: "not just a toy", "most projects stop short of this".
  State what the thing is; cut the implied comparison.
- **Drama**: bold on "**wrong**", "blazing fast". Use "settled", "disproved",
  plain "wrong", and a number.
- **Overclaiming scope**: never claim stronger guarantees than the code
  delivers; name the exact assumptions or limitations at the point of claim,
  not five screens later.

### Do

- **Name assumptions at the point of claim**: if a result depends on an
  unproved hypothesis or trusted compiler, say so in the same sentence.
- **Quantify with context**: benchmark numbers carry machine, input size, and
  the word "indicative"; formal bounds carry their exact form.
- **State negative results and limitations in the main flow** — they are
  content, not concessions.
- **Keep informative contrasts** that carry technical content. The line: a
  contrast that teaches stays; a contrast that flatters goes.
