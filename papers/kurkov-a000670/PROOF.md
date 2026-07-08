# Theorem (Kurkov's 2018 conjecture in OEIS A000670)

**Statement (frozen verbatim from https://oeis.org/A000670, formula section, fetched 2026-07-06):**
"Conjecture: a(n) = Sum_{k=0..2^(n-1)-1} A284005(k) for n > 0 with a(0) = 1. - Mikhail Kurkov, Jul 08 2018"

Here a(n) = A000670(n) (Fubini numbers, ordered set partitions of [n]) and A284005 is
defined (frozen verbatim from https://oeis.org/A284005) by A284005(0)=1 and
A284005(m) = (1 + wt(m)) * A284005(floor(m/2)) where wt = binary weight.

## Setup

Unwinding the recursion (equivalently Ryde's product formula on the A284005 page):
for m with binary digits b_1 b_2 ... b_L (MSB first),

    A284005(m) = prod_{i=1}^{L} (1 + w_i),   w_i := b_1 + ... + b_i.

Prefixes of weight 0 contribute a factor 1, so **left-padding with zeros does not
change the value**. Hence for fixed n we may regard each k in {0,...,2^{n-1}-1}
as a string b_1...b_{n-1} of exactly n-1 bits (MSB first, zero-padded), and

    A284005(k) = prod_{i=1}^{n-1} (1 + w_i),   w_i = b_1 + ... + b_i.   (*)

## Refined Theorem

For a binary string b = b_1...b_{n-1}, let M(b) = {1} ∪ {i+1 : b_i = 1} ⊆ [n].
Then the number of ordered set partitions of [n] whose set of block minima equals
M(b) is exactly prod_{i=1}^{n-1} (1 + w_i) = A284005(k).

Since every ordered set partition of [n] has a unique set of block minima, which
always contains 1, and M is a bijection from {0,1}^{n-1} onto {S ⊆ [n] : 1 ∈ S},
summing over all k proves the conjecture.

## Proof of the Refined Theorem

Build ordered set partitions by inserting the elements 1, 2, ..., n in increasing
order. Because elements are inserted in increasing order, an element is the
minimum of its block **iff it opened that block** (every element joining an
existing block is larger than that block's opener).

Insertion step for element i+1 (i = 1, ..., n-1), given the current ordered set
partition of [i] with m_i blocks:

- if b_i = 1 (element i+1 must be a block minimum): open a new singleton block,
  in any of the m_i + 1 positions of the ordered list of blocks;
- if b_i = 0 (element i+1 must not be a block minimum): join any of the m_i
  existing blocks.

The number of blocks after step i is m_{i+1} = 1 + w_i (start: m_1 = 1, one block
containing element 1; each b_i = 1 adds a block). Therefore the number of choices
at step i is:

- b_i = 1:  m_i + 1 = (1 + w_{i-1}) + 1 = 1 + w_i  (since w_i = w_{i-1} + 1),
- b_i = 0:  m_i     =  1 + w_{i-1}      = 1 + w_i  (since w_i = w_{i-1}).

In both cases exactly 1 + w_i choices — so the number of insertion histories with
signature b is prod_{i=1}^{n-1}(1 + w_i), which is (*).

Distinct choices at any step yield distinct ordered set partitions, and every
ordered set partition of [n] arises from exactly one insertion history: delete n
(and its block if singleton) to recover the ordered set partition of [n-1] and
the last choice, and induct. So insertion histories with signature b are in
bijection with ordered set partitions whose block-minima set is M(b).  ∎

## Verification performed

- Ground truth: conjecture verified numerically for n = 1..20 (groundtruth.py).
- Refined theorem verified exhaustively for ALL minima-sets at n = 1..8
  (all 598,444 ordered set partitions enumerated; 255 minima-set classes;
  0 mismatches) — lemma_check.py.
- checker.py + mutation tests: see below.

## What this does not show

- Priority is NOT established: the formula line still reads "Conjecture" in the
  entry as of 2026-07-06, but a published proof elsewhere (e.g., in work on
  A329369/A284005 by Kurkov or others) has not been excluded by a proper
  dated search sweep. House-standard kill-check queries still required.
- The refined statement (block-minima refinement) may also be known folklore;
  same caveat.
