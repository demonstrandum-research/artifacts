# The eventual value of h₄, and improved bounds for the Choi–Erdős–Szemerédi pairwise-sums problem (Erdős #866)

**Draft v5 — release freeze, 2026-07-08 (C5P2/C6P2 gate execution).**
Supersedes Draft v4 (same path): no mathematical change — quotes the
completed canonical verification counts (G1: 298/298 cells, 0 failures;
§9.1 and Appendix B), records the multi-run assembly provenance of that
pass honestly, and adds the fresh 2026-07-08 openness kill-check (§13).
Release gate G1–G3 GREEN on disk (`check_gate.py`). Cells landed after
the 298-cell freeze (h4 65–68, g5 24–25) remain **outside** the claimed
ranges. Draft v4 (C6-P2, 2026-06-13) added §10 — the C5-P1 g-side
per-anchor collapse ((†), Theorem Z, the conditional capacity ceiling,
and the in-flight n-free enumeration), graded honestly per part, **no
new claim**. Draft v3 superseded
v2 (C4-P4, 2026-06-12); v2 superseded v1
(`C3P4-hygiene-paper/paper/draft-866.md`); v1 upgraded
`P5-hygiene/paper/skeleton-866.md`. C4-campaign upgrades folded in: the
exact-value theorem for $h_4$ is now **kernel-verified at
$N_0 = 331{,}777 = 24^4+1$** (`Erdos866.h4_eq_4`, the per-o-pair
balanced-window collapse, §6 — both halves of Thm 1.3 now [K]), and the
general-$k$ constants of §8 are at paper grade (C4-P3 write-out + audit).
Evidence grades: **[K]** kernel-grade (Lean 4, sorry-free, axioms exactly
`[propext, Classical.choice, Quot.sound]`, fresh audits
`lean/scripts/auditC4P1.log` + `c4p1_fullbuild.log` (the h4_eq_4 port,
8039 jobs green) and `lean/scripts/auditC4Synth.log` + `c4synth_build.log`
(C4 synthesis: from-scratch rebuild, `.lake/build` deleted first; 28/28
declarations on the three base axioms or fewer, zero `sorryAx`));
**[P]** paper-grade (written proof + exact-arithmetic machine-verified
numerics + independent re-verification); **[E]** exact-computational (SAT
certificates, dual-engine UNSAT + DRAT/LRAT archive checked by a formally
verified checker); **[D]** derivation-grade (derivation in hand, full
write-out + audit pending — not headlined). Every claim states **g vs h**
explicitly (PROBLEM.md A2).

---

## Abstract

For $A \subseteq \{1,\dots,2n\}$, let $g_k(n)$ be the least $m$ such that
$|A| \ge n+m$ forces $k$ distinct integers $b_1,\dots,b_k$ (not necessarily
in $A$, at most one non-positive automatically) with all $\binom{k}{2}$
pairwise sums $b_i+b_j \in A$, and let $h_k(n)$ be the variant requiring the
$b_i$ to be distinct **positive** integers. Choi, Erdős and Szemerédi (1975)
proved $h_4(n) = O(1)$ — "we were too lazy to determine $t$" (Erdős, 1972) —
and the best published bounds were $3 \le h_4(n) \le 2270$, the upper bound
formally verified in Lean (van Doorn–Aristotle, 2026). We determine the
eventual value of this constant under the modern (positive-variant)
convention:

> **$h_4(n) = 4$ for all $n \ge 331{,}777$,**

and this exact-value theorem is itself **verified by the Lean 4 kernel**
(`Erdos866.h4_eq_4`, sorry-free, against van Doorn's public
formalization), with $h_4(n) = 4$ also at every computed value
$n \in \{3,4\} \cup [6,64]$
and $h_4(5)=5$. En route we prove $4 \le h_4(n) \le 1000$ for all $n \ge 3$,
both halves **verified by the Lean 4 kernel** against van Doorn's public
formalization; the lower bound also yields the first strict separation
$g_4(n) < h_4(n)$ beyond $k=3$, likewise kernel-verified. For five summands
we improve the $g_5$ upper constant by a factor $32$, from van Doorn's
$113{,}591{,}719$ to $3{,}519{,}219$ (g-side), by removing the
disjoint-representations loss from the CES recursion — this bound too is
now **verified by the Lean 4 kernel** (`gFun 5 n < 3519220`, sorry-free,
$34\times$ below the prior Lean constant $1.2\cdot10^8$) — and we improve
the $h_5$ lower bound from $\log_2 n$ to $\#\{\text{Fibonacci} \le n\} + 1$
(asymptotic factor $1/\log_2\varphi \approx 1.4404$), the family-side
inequality kernel-verified. We further compute exact values of $g_k, h_k$
($k \le 6$) on initial segments — in particular $g_5(n) = 4$ for
$15 \le n \le 23$, bearing directly on van Doorn's question of whether
$g_5(n) \le 4$ for all large $n$ — each nontrivial cell certified by dual
SAT engines and an archived DRAT/LRAT proof checked by the formally
verified checker cake_lpr. Toward that question we develop (without
claiming the theorem) a g-side structural reduction: a one-window
per-anchor dichotomy, an all-low/all-top zone theorem, and a
conditional capacity ceiling that shrinks the open middle band to
$d \in [5,19]$ (§10). All results are produced and verified under an
exact-arithmetic / proof-certificate doctrine described in §12.

---

## 1. Introduction

### 1.1 The problem

Erdős problem #866 (erdosproblems.com/866, citing [CES75], [Er72],
[Er92c]) asks:

> Let $k\geq 3$ and $g_k(N)$ be minimal such that if
> $A\subseteq \{1,\ldots,2N\}$ has $\lvert A\rvert \geq N+g_k(N)$ then there
> exist integers $b_1,\ldots,b_k$ such that all $\binom{k}{2}$ pairwise sums
> are in $A$ (but the $b_i$ themselves need not be in $A$). Estimate
> $g_k(N)$.

Throughout we use van Doorn's modern formulation [vD26], identical to the
public Lean development [L866]: the $b_i$ are pairwise **distinct** integers
(without distinctness the problem trivializes), and at most one $b_i$ can be
non-positive (two non-positives sum to $\le 0 \notin A$) — this is a derived
fact, not a clause. The **positive variant** $h_k(n)$ requires all $b_i \ge 1$.
The two functions genuinely differ: $g_3 = 1 < 2 = h_3$, and
$h_5 \asymp \log n$ while $g_5 = O(1)$ [vD26]. Basic structure:
$g_k \le h_k \le g_{k+1}$ for $k \ge 3$ [vD26 eq. (2); Lean
`gFun_le_hFun_le_gFun_succ`].

History. CES75 proved $g_3$-type and $h_3$-type results ($h_3 = 2$ for
$n \ge 4$), boundedness of the four-summand constant ($h_4 = O(1)$; "we
were too lazy to determine $t$", [Er72] p. 83), $h_5 \asymp \log n$,
$g_6 \asymp h_6 \asymp \sqrt n$, and the general bounds
$t_{k+1} \le 2^k n^{1-2^{-k}}$ and $h_k(n) > n^{1-\epsilon}$ for large $k$.
Van Doorn [vD26] introduced the $g/h$ split, proved $g_3(n) = 1$ ($n\ge3$),
$g_4(n) = 3$ ($n\ge2$), $g_5(n) < 1.2\cdot10^8$, $h_4(n) \le 2270$, and
$g_k \le h_k < 4n^{1-2^{2-k}}$; the entire development [vD26] is formalized
sorry-free in Lean 4 [L866] (formal author: Aristotle, Harmonic; 3494
lines, Mathlib only). Caveats inherited from the sources: CES75's
lower-bound examples for $k \in \{3,5\}$ silently assume positive $b_i$ and
are wrong for $g_k$ (PROBLEM.md A2; e.g. $b = (-1,2,3,5,6)$ has all ten
pairwise sums in odds ∪ powers-of-2); [Er72] demanded the *sums* be
distinct, a strictly stronger convention than the modern one (A6). Our
exact-value theorem for $h_4$ is stated under the modern convention
([vD26]/Lean `hFun`), and we say so explicitly wherever it is claimed.

### 1.2 Results

| # | Statement (g/h explicit) | Was | Grade | Where |
|---|---|---|---|---|
| Thm 1.1 | $h_4(n) \le 1000$ for all $n \ge 1$ | 2270 [L866] | **[K]** `h4_le_1000` | §5 |
| Thm 1.1′ | $h_4(n) \le 1529$, from Ruzsa's published weak-Sidon bound only | 2270 | [P] (companion; not separately ported) | §5 (Thm 5.5) |
| Thm 1.2 | $h_4(n) \ge 4$ for all $n \ge 3$; hence $g_4(n) < h_4(n)$ for $n \ge 3$ — first strict $g/h$ separation beyond $k=3$ | 3 (via $g_4$) | **[K]** `four_le_hFun_four`, `gFun_four_lt_hFun_four` | §3 |
| **Thm 1.3** | **$h_4(n) = 4$ for all $n \ge 331{,}777$** (positive variant, modern convention) — the eventual value of the constant CES75 left undetermined | $[3,2270]$ | **[K]** `h4_eq_4` (both halves; corollaries `h4_eq_4_charter`/`h4_eq_4_c2` pin the superseded paper-grade constants $4{,}593{,}324$ and $8\cdot10^7$) | §6 |
| Thm 1.4 | $g_5(n) \le 3{,}519{,}219$ for all $n \ge 1$ (g-side) | $113{,}591{,}719$ [vD26]; Lean constant $1.2\cdot10^8$ | **[K]** `g5upper_star_charter` (`gFun 5 n < 3519220`, all $n$); Lemma 7.1 induction fully proved in Lean at general $k$ | §7 |
| Thm 1.5 | $h_5(n) \ge z(n) + 1$ for all $n \ge 1$, $z(n) := \#\{\text{Fibonacci} \le n\}$; $z(n) \ge \lfloor\log_2 n\rfloor + 1$, asymptotic factor $1/\log_2\varphi \approx 1.4404$ over the standing bound | $> \log_2 n$ [L866] | **[K]** `fibCnt_lt_hFun_five` (family inequality, all $n$); the $z$-vs-$\log_2$ comparison is elementary + exhaustively checked to $10^6$, not yet formal | §3 |
| Thm 1.6 | Exact values ($k \le 6$ tables): $g_5(n)=4$ for $15\le n\le 23$; $h_4(n)=4$ on $\{3,4\}\cup[6,64]$, $h_4(5)=5$; $g_4(60)=3$ with unique extremum = vD's family; $h_5(n)=z(n)+1$ for $13\le n\le 26$; uniqueness of the Thm-1.2 extremum for $11 \le n \le 64$ | vD26 search: no counterexample to $g_5\le5$, $n\le15$ | [E] | §9 |
| Thm 1.7 | general $k\ge4$, explicit $N(k) = k^4\cdot2^{4k+27}$: $g_k(n) < 2n^{1-2^{2-k}}$, $h_k(n) < 2.25\,n^{1-2^{2-k}}$ for $n \ge N(k)$ | $4n^{1-2^{2-k}}$ [vD26] | [P] — full write-out + audit `lenses/C4P3-allk-writeup/T2-ALLK.md`, machine numerics `verify_allk.py` 272 checks PASS (re-run at C4 synthesis); the recursion core (Lemma 7.1 and its extraction lemma) is proved in Lean at general $k \ge 3$; no Lean object for the all-$k$ statement itself | §8 |

Two results are, to our knowledge, the first of their kind for this
problem: Thm 1.3 is the first exact-value theorem for any unbounded-$n$
regime of $h_4$ (CES75 Theorem 2 proved existence of the constant; no
source computed it) — and it is itself kernel-verified — and
Thm 1.2 + Thm 1.1 give the first
kernel-verified two-sided interval $h_4(n) \in [4, 1000]$ ($n \ge 3$;
upper half for all $n \ge 1$). Every constant this paper headlines as
beating a published bound, and the exact-value theorem itself, is
Lean-verified: Thms 1.1, 1.2, 1.3, 1.4 and the family inequality of
Thm 1.5 are all [K]. Beyond the numbered results, §10 reports a
structural program toward $g_5 = 4$ (per-anchor dichotomy (†),
Theorem Z, conditional capacity) at explicitly sub-[K] grades and
with no exact-value claim — it is included for its mathematical
content and as the audited state of the open problem, not as a
headline result.

### 1.3 Formalization status (binding, audited 2026-06-12/13 (C4–C5 sessions))

Our Lean 4 extension project builds against the byte-pinned upstream
development [L866] (sha256 `043731e3…9845e`, re-hashed at the C4-P1 and
C4-synthesis audits; upstream files never modified). From-scratch
rebuild (`.lake/build` deleted first): 8039 jobs green
(`lean/scripts/c4synth_build.log`). Kernel-verified, axioms exactly
`[propext, Classical.choice, Quot.sound]` (one `decide`-backed
certificate drops `Classical.choice`), zero `sorryAx` in any
root-imported module (audits `lean/scripts/AuditC4P1.lean` →
`auditC4P1.log` and `AuditC4Synth.lean` → `auditC4Synth.log`, 28/28
declarations, with compile-time statement pins incl.
$331777 = 24^4+1$ and `hFun` = upstream `sInf` definition by `rfl`;
independently: the C3-synthesis audit `AuditC3Synth.lean`):

- `Erdos866.h4_eq_4 : ∀ n, 331777 ≤ n → hFun 4 n = 4` (Thm 1.3, both
  halves; module `Erdos866/H4Dichotomy.lean`, imported by the root);
- `Erdos866.g5upper_star_charter : ∀ n, gFun 5 n < 3519220` (Thm 1.4 at
  the charter constant) with the pinned target
  `Erdos866.T1TargetG5_closed_charter`, plus the fallback
  `g5upper_star : ∀ n, gFun 5 n < 3520600`; the engine is the fully
  proved Lemma 7.1 (`Erdos866.lemmaA`, general $k \ge 3$) and its
  general-$k$ extraction lemma `Erdos866.ceslemgeneral_star`;
- `h4_le_1000 : ∀ n, 0 < n → hFun 4 n ≤ 1000` (Thm 1.1) and the pinned
  target `Erdos866.T1TargetH4_closed_1000`;
- `Erdos866.four_le_hFun_four : ∀ n, 3 ≤ n → 4 ≤ hFun 4 n` (Thm 1.2);
- `Erdos866.gFun_four_lt_hFun_four : ∀ n, 3 ≤ n → gFun 4 n < hFun 4 n`;
- `Erdos866.fibCnt_lt_hFun_five : ∀ n, fibCnt n < hFun 5 n` (Thm 1.5
  family inequality);
- `Erdos866.key_ineq_star / key_ineq_star_tuned / key_ineq_star_charter /
  fStar5_le_poly` (the (xineq*) numeric layer of Thm 1.4).

Honestly flagged as **not formal**: Thm 1.1′ (companion only); the
$z$-vs-$\log_2$ comparison in Thm 1.5; the all-$k$ statement of §8
(paper-grade; its recursion core *is* formal); and §9 (which is
certificate-checked computation, §9.1, not Lean). The former principal
trust locus — the hand-proved structural reduction of Thm 1.3 — was
discharged by the Lean port: `structural_case` is closed sorry-free on
the per-o-pair chain (§6), and the module is imported by the sorry-free
root.

## 2. Notation

$n \ge 1$; window $W := \{1,\dots,2n\}$; $A \subseteq W$ with
$|A| = n + s$ ($s$ = **surplus**). $g_k(n), h_k(n)$ per §1.1 (= Lean
`gFun`/`hFun`). A *(g,k)-config* is $k$ distinct integers $b_i$ with all
pairwise sums in $A$; an *(h,k)-config* additionally has all $b_i \ge 1$.
$A_0$ := even elements of $A$. For the central-window proof (§5):
$C_4 := 1000$ (resp. 1529), $\tau := |A_0| - C_4 \ge 0$, $O_{miss}$ := odd
numbers of $W$ missing from $A$ ($|O_{miss}| \le \tau$). For the recursion
(§7): $\varphi$ = forbidden-set size, $x$ = diameter,
$C_5 := 3{,}519{,}219$. Fibonacci normalization (Thm 1.5): $F_1 = 1$,
$F_2 = 2$, $F_j = F_{j-1}+F_{j-2}$ (distinct values $1,2,3,5,8,\dots$);
$z(n) = \#\{j : F_j \le n\}$. The Thm-1.2 family is $A^*_n$; lab notation
$m_k^v(n)$ = maximum config-free size, $v \in \{g,h\}$, so
$v_k(n) = m_k^v(n) + 1 - n$. (This applies the skeleton's collision
ledger; lens-internal $t$, $C$, $M$ are renamed $\tau$, $C_4/C_5$,
$|O_{miss}|$ throughout.)

## 3. Lower bounds by parity (h-side; Thms 1.2, 1.5)

**Theorem 3.1 (= 1.2, [K]).** For $n \ge 3$ the set
$A^*_n := \{1,3,\dots,2n-1\} \cup \{2,\, 2n-2,\, 2n\}$, of size $n+3$,
contains no (h,4)-config. Hence $h_4(n) \ge 4$.

*Proof.* The even elements are exactly $E = \{2, 2n-2, 2n\}$. Suppose
$b_1<b_2<b_3<b_4$ positive with all six sums in $A^*_n$; split by parity
$(p,q)$, $p$ odd count. $(4,0)/(0,4)$: the five distinct values
$b_1{+}b_2 < b_1{+}b_3 < b_2{+}b_3 < b_2{+}b_4 < b_3{+}b_4$ are even, but
$|E| = 3$. $(3,1)/(1,3)$: the three same-parity $b$'s give three distinct
even sums $= E$ exactly, forcing smallest sum $= 2$; but two distinct
positive odds sum to $\ge 4$ (evens to $\ge 6$). $(2,2)$: odds
$o_1<o_2$, evens $e_1<e_2$; the even sums $o_1{+}o_2,\,e_1{+}e_2 \ge 4 > 2$
lie in $\{2n-2, 2n\}$, so $(o_1{+}o_2)+(e_1{+}e_2) \ge 4n-4$; the cross
sum $o_2+e_2$ is odd, $\le 2n-1$, so
$o_1{+}e_1 \ge (4n-4)-(2n-1) = 2n-3$ and
$(o_2{-}o_1)+(e_2{-}e_1) = (o_2{+}e_2)-(o_1{+}e_1) \le 2$ — but distinct
odds and distinct evens each differ by $\ge 2$. ∎

Lean: `four_le_hFun_four` (witness card + config-freeness via a single
`omega` over the 6 sum-memberships, 6 distinctness, 4 positivity facts).
Machine checks: config-freeness of $A^*_n$ for $3 \le n \le 400$ (Python
DFS) and $n \le 1000 \cup \{1200,1500,2000\}$ (independent Rust checker).

**Corollary 3.2 ([K]).** $g_4(n) = 3 < 4 \le h_4(n)$ for $n \ge 3$: the
$b_1 \le 0$ escape is *necessary* at surplus 3. This is the first strict
$g_k < h_k$ separation beyond $k = 3$ ($g_3 = 1 < 2 = h_3$ was known
[vD26]); contrast $k=5$, where the separation is asymptotic
($g_5 = O(1)$, $h_5 \asymp \log n$). Lean: `gFun_four_lt_hFun_four`
(uses upstream `g4`).

**Theorem 3.3 (= 1.5, family half [K]).** For all $n \ge 1$ (Lean: all
$n$), $B_n := \{1,3,\dots,2n-1\} \cup \{2F_j : F_j \le n\}$, of size
$n + z(n)$, contains no (h,5)-config. Hence $h_5(n) \ge z(n)+1$.

*Proof.* Domination: for Fibonacci values $f_a < f_b < f_c$ we have
$f_a + f_b \le f_c$ (if $f_b = F_j$ then $f_a \le F_{j-1}$,
$f_c \ge F_{j+1} = F_j + F_{j-1}$). Among 5 positive $b_i$ three share
parity, say $x_1<x_2<x_3$; their pairwise sums are even elements of
$B_n$, i.e. $2f_a = x_1{+}x_2 < 2f_b = x_1{+}x_3 < 2f_c = x_2{+}x_3$ with
$f_a<f_b<f_c$ Fibonacci. But $2f_a + 2f_b - 2f_c = 2x_1 \ge 2$, i.e.
$f_a + f_b > f_c$ — contradiction. ∎

Lean: `fibCnt_lt_hFun_five`, with `fibCnt n` = number of Fibonacci
*values* in $[1,n]$ and engine `fib_triple_bound`; first formal
improvement of the $h_5$ lower constant over upstream `h5lower`
($\log_2 n < h_5(n)$).

**Corollary 3.4 ([P]).** $F_j \le 2^{j-1}$ gives $z(n) \ge
\lfloor\log_2 n\rfloor + 1$, so $h_5(n) \ge \lfloor\log_2 n\rfloor + 2$,
beating the standing bound pointwise by $\ge 1$ for every $n \ge 2$
(exhaustively checked $n \le 10^6$; min margin exactly 1) and
asymptotically by $1/\log_2\varphi = 1.4404\dots$ (since
$z(n) = \log_\varphi n + O(1)$). *(The comparison lemma
$\lfloor\log_2 n\rfloor + 1 \le z(n)$ is not yet formalized — C4-P5(a).)*

**Proposition 3.5 (extremal class, [P]).** Call an even set
$E = \{e_1<\dots<e_m\} \subseteq [2,2n]$ *dominated* if
$e_{i-2}+e_{i-1} \le e_i$ ($i \ge 3$). Every $A$ = (all odds) ∪
(dominated $E$) is (h,5)-config-free, and conversely $m \le z(n)$ for
dominated $E$ (induction: $e_i/2 \ge F_i$). So $n + z(n)$ is the exact
maximum size of an "all-odds + dominated-evens" certificate; the
maximizers match every all-odds extremal set found by exact enumeration
for $13 \le n \le 16$.

## 4. The weak-Sidon toolbox

$S \subseteq \mathbb{Z}$ finite is **weak Sidon** if no four
pairwise-distinct $a,b,c,d \in S$ have $a+b = c+d$.

**Lemma 4.1 (energy; cited verified ingredient [K]).** $S \subseteq
\{1,\dots,N\}$ weak Sidon, $|S| = s$ ⇒ for every integer $\nu \ge 1$:
$s^2\nu \le (N+\nu-1)(3s+\nu-1)$. *Provenance:* verbatim Lean
`weak_sidon_key_ineq` (Upstream.lean:889); mathematical content in the
proof of Ruzsa [Ru93, Thm 4.6] (double-count fibers of $S + [1,\nu]$;
Cauchy–Schwarz; weak Sidon forces difference multiplicities $\le 2$ with
$\le s$ doubled differences).

**Lemma 4.1R (published fallback).** Weak Sidon $S \subseteq [1,N]$ has
$|S| \le \sqrt N + 4N^{1/4} + 11$ [Ru93, Thm 4.6; Lean
`weak_sidon_bound`].

**Lemma 4.2.** If $S$ is not weak Sidon there are $a_1<a_2<a_3<a_4$ in
$S$ with $a_1+a_4 = a_2+a_3$ (the equal-sum pairing must match extremes).

**Lemma 4.3 ((Φ,ν)-violation).** If $\Phi^2\nu > (N_0+\nu-1)(3\Phi+\nu-1)$
and $|S| \ge \Phi$ with $S$ in a window of length $N_0$, then $S$ is not
weak Sidon, yielding the quadruple of 4.2. Anti-monotone in $N_0$.

**Lemma 4.4 (k=4 chain).** Let $E \subseteq 2\mathbb{Z}_{\ge 2}$ with
diameter $\le x$, and suppose $(\Phi,\nu)$ violates the window $x/2+1$
and $r(r-1) > 2x(\Phi-1)$ where $r = |E|$. Then $E$ contains an
(h,4)-config. *Proof sketch:* a popular difference $d$ gives
$|E \cap (E-d)| \ge \Phi$ after an alternating-path disjointification;
apply 4.3 to the halved set; lift the additive quadruple to
$(b_1,\dots,b_4) = (A_1/2,\ A_1/2{+}A_2{-}A_1,\ A_1/2{+}A_3{-}A_1,\
A_1/2{+}d)$. Lean analogue: `ceslem_k4_chain`; in the port the new lemma
`not_weak_sidon_of_phinu` feeds `weak_sidon_key_ineq` directly with the
certificate's explicit $\nu$ on a halved-and-translated $\Phi$-subset.

## 5. Theorem 1.1: h₄(n) ≤ 1000 — asymmetric central window **[K]**

Statement (positive variant): every $A \subseteq \{1,\dots,2n\}$ with
$|A| \ge n + 1000$ admits four distinct positive integers with all six
pairwise sums in $A$. Kernel-verified as `h4_le_1000`. The proof is
van Doorn's §7 skeleton with two changes: an **asymmetric central
window** (change 1) and the **energy-form weak-Sidon base** 4.1 in place
of 4.1R (change 2). Set $C_4 = 1000$, $\tau = |A_0| - C_4 \ge 0$,
$|O_{miss}| \le \tau$.

**Lemma 5.1 (central element).** If $2m \in A$ with
$4\tau+3 \le m \le n-2\tau-2$, then $A$ has an (h,4)-config.
*Proof.* Candidates $b_3 \in K := \{m-2-2i : 0 \le i \le 2\tau\}$
($|K| = 2\tau+1$, all $\equiv m \bmod 2$); set $b_4 := 2m-b_3$ and take
$(b_3,\ m-1,\ m+1,\ b_4)$. The two even sums are $2m \in A$; the four
cross sums are odd and (using $8\tau+6 \le 2m \le 2n-4\tau-4$) land in
$[1, 2n-1]$. Each missing odd kills $\le 2$ candidates ($y < 2m$ only via
$s_1,s_2$; $y > 2m$ only via $s_3,s_4$), so $\le 2\tau < |K|$ are bad. ∎
*(The window's lower edge is forced by positivity of $b_3$; the upper
edge only needs $2m + 4\tau + 3 \le 2n - 1$ — hence the asymmetry, which
is what shrinks the high interval in Case 2 below.)*

**Theorem 5.2 (assembly).** If no even element of $A$ is central
(Lemma 5.1 empty), then $A_0$ splits into
low $\subseteq [2,\ 8\tau+4]$ (diameter $\le 8\tau+2$) and
high $\subseteq [2n-4\tau-2,\ 2n]$ (diameter $\le 4\tau+2$). A numeric
certificate supplies, for each $\tau$, tuples
$(\Phi_L,\nu_L,\psi_L,\Phi_H,\nu_H,\psi_H)$ satisfying the verification
conditions V2–V5 (each $(\Phi,\nu)$ violates its window per 4.3, and
$\psi$-cardinality forces the chain 4.4); pigeonhole gives
$|$low$| \ge \psi_L$ or $|$high$| \ge \psi_H$ whenever
$|A_0| \ge \psi_L + \psi_H - 1$, and the certificate guarantees
$\max_\tau(\psi_L+\psi_H-1-\tau) = 1000$. For $\tau \le 4\cdot10^5$ this
is a 157-block tile (`cert_energy.csv`); for $\tau > 4\cdot10^5$ the
closed-form tail (Lemma 5.3). ∎

**Lemma 5.3 (tail).** With $u = \lceil\sqrt{N_0}\rceil$, the tuple
$\Phi = 2u$, $\nu = 4u$, $\psi = \mathrm{isqrt}(4xu)+2$ satisfies V2–V5
for every $\tau > 4\cdot10^5$ (three exact rational inequalities,
polynomial positivity checked for $u \in [7,5000]$ and asymptotically).

**Proposition 5.4 (route-optimality, [P]).** $C_4 = 1000$ is exactly
optimal for this window/lemma decomposition: 999 fails at $\tau = 2648$
(the maximum $\psi_L+\psi_H-1-\tau = 1000$ is attained at
$\tau \in \{2647, 2648\}$ — a tie, recorded in machine artifacts).
Likewise 1529 is exact for the Ruzsa-only variant ($\tau = 3559$).

**Theorem 5.5 (= 1.1′, [P]).** The same skeleton from Lemma 4.1R alone
gives $h_4(n) \le 1529$ (177-block certificate `cert_ruzsa.csv`). This
was the port fallback; the energy form landed, so it remains a
paper-grade companion for readers who want only published ingredients.

**Verification.** (i) Lean kernel: `h4_le_1000` sorry-free, axioms clean
— the binding check; certificate rows enter as kernel-`decide` facts.
(ii) `check_cert.py`: ACCEPT for both certificates (exact integers,
tiling of $[0, 4\cdot10^5]$). (iii) Independent synthesis re-sweep
(`verify_central.py`, fresh implementation): max
$\psi_L+\psi_H-1-\tau = 1000$ (argmax tie 2647/2648) and 1529
(argmax 3559), witness tuples reproduced digit-exact; tail facts
re-verified at $\tau \in \{4\cdot10^5{+}1, 10^6, 10^7, 10^9\}$.
(iv) Mutation tests: corrupted certificates rejected. Fresh re-runs of
(ii)–(iii): `numerics_c3p4_fresh.log` (C3-P4 lens).

## 6. Theorem 1.3: the eventual value h₄(n) = 4 for n ≥ 331,777 **[K]**

Positive variant, modern convention ([vD26]/Lean `hFun`); the historical
[Er72] phrasing demanded distinct *sums* (A6), so we claim the value of
$h_4$, not the verbatim 1972 constant. Lower half = Thm 3.1 **[K]**.
Upper half **[K]**: for $n \ge N_0 := 331{,}777 = 24^4+1$, every
$A \subseteq [1,2n]$ with $|A| = n+4$ has an (h,4)-config. The whole
theorem is verified by the Lean 4 kernel:

> `Erdos866.h4_eq_4 : ∀ n, 331777 ≤ n → hFun 4 n = 4`
> (module `Erdos866/H4Dichotomy.lean`, imported by the sorry-free root;
> axioms exactly `[propext, Classical.choice, Quot.sound]`; audits
> `auditC4P1.log`, `auditC4Synth.log`; in-file corollaries
> `h4_eq_4_charter` and `h4_eq_4_c2` pin the superseded paper-grade
> constants $4{,}593{,}324$ and $8\cdot10^7$.)

The hand proof evolved in three rungs — $8\cdot10^7$
(`lenses/P4-frontier/DICHOTOMY.md`), $4{,}593{,}324$ (the KC1 $= 2$
kill-count correction, `lenses/C3P3-frontier-transfer/GTRANSFER.md` §5),
and the kernel chain below (the per-o-pair balanced-window collapse,
C4-P1), which is what is formalized; structure:

**Setup.** $D$ = missing odds, $d = |D|$, so $|E| = d+4$ for the even
part $E$. Two constructive machines: the **(2+2) machine** (two even
anchors $s,t \in E$, an odd pair summing to $s$, an even pair summing to
$t$; the four odd cross sums must all be hit by $D$) and the **triangle
machine** (a *positive triangle* $2g_1<2g_2<2g_3 \in E$ with
$g_1+g_2 \ge g_3+1$ yields $x<y<z$ same-parity with
$x{+}y, x{+}z, y{+}z \in A$; sweeping the opposite-parity fourth point
$w$ forces **(T★)**: every positive triangle has $z \ge 2n-2-6d$).

**The kill-count (K), per-o-pair.** Per fixed $(s,t,\text{o-pair})$,
each missing odd $m \in D$ kills at most **2** e-pair combos: $m$ blocks
an e-pair only via a cross sum $m = o_i + e$, so with the o-pair
$(o_1,o_2)$ fixed there are at most two candidate even values
$e \in \{m-o_1,\ m-o_2\}$, and each determines its partner $t-e$, hence
the whole e-pair (`K_epairs_le2`; the bound 2 is tight — verified
exhaustively on parameter grids, `killcount_check.py` KC1 and the
independent grid in `verify_constants.py`). The original write-up used
the (true but not tight) aggregate bound 4.

**The balanced-window collapse (`balanced_kill`).** The per-o-pair form
is strictly stronger than the aggregate use: with one *balanced* o-pair
of $s$ fixed, the window of balanced e-pairs of $t$ ($e_2$ even in
$(t/2,\ t/2+4d+2]$) hosts $2d+1$ candidate e-pairs, while the fixed
o-pair leaves at most $2|D| = 2d$ of them killable. One surviving e-pair
gives the (2+2) machine its four cross sums — contradiction. This single
lemma replaces *both* zone lemmas of the earlier chains (the middle
exclusion X1/X1′ and the triangular-grid X2/X2′), at validity
$n \ge 8d+8$ (slope $1/8$, halving the earlier $16d$):

- **MID** ($s = t$): $E \cap [8d+8,\ 2n-4d-5]$ is empty;
- **LOW×TOP** ($s \in [4, 8d+6]$, $t \in$ TOP): impossible, so
  LOW $\subseteq \{2\}$;
- **TT**: three TOP elements give a positive triangle with
  $z \le n+2d+1$, killed by (T★) ($3d+1$ anchors
  $w = 2j-(1-x\bmod 2)$, kill map $(m, \text{pos} \in \{0,1,2\})$), so
  $|$TOP$| \le 2$.

If TOP $\ne \emptyset$: $|E| \le 1 + 2 = 3 < d+4$ — contradiction. If
TOP $= \emptyset$: (T★) makes $\Lambda := E/2 \subseteq [1, 4d+3]$
*triangle-free* ($\lambda_{i-2}+\lambda_{i-1} \le \lambda_i$), so
$\max\Lambda \ge F_{|\Lambda|+1} \ge F_{d+5} > 4d+3$ — **false for every
$d \ge 0$** (`triangle_free_fib` + `cap_fib`; checked to $d = 1000$ in
exact arithmetic as belt). The Fibonacci capacity bound (CAP) thus
closes the structural regime outright for all $d \ge 0$: no finite
endgame enumeration occurs anywhere on the proof path. ∎

**Dense regime ($d > (n-7)/8$).** Then $|E| = d+4 > (n-7)/8 + 4 \ge
F_4(2n-2)$ for $n \ge 331{,}777$, and upstream **Lean-verified**
`ceslemgeneral_pos` ($k=4$) applied to $E$ produces four distinct
positive integers with all pairwise sums in $E$. This is the only
non-elementary ingredient. The crossover is certified in exact
arithmetic and in the kernel: with $n = u^4$-scaling, the threshold is
the integer root bracket $q(23) < 0 < q(24)$, i.e. $u \ge 24$, giving
$N_0 = 24^4 + 1 = 331{,}777$; in $s = u - 24$ the majorization
polynomial is $3s^4+220s^3+5404s^2+44952s+12162$, all coefficients
positive (identity + threshold re-checked by `verify_constants.py`,
ALL PASS, re-run at C4 synthesis). $N_0$ is *not* optimized (the $u \ge
24$ threshold is for this majorization; $\sim 2.4\cdot10^5$ is
plausible) — exact-value work supersedes constant-shaving. ∎

**The earlier chains as belt.** The first proof of Thm 1.3 (C2, with
aggregate (K) $\le 4$) ran the dichotomy at $n \ge 32d+10$: there CAP
only forces $d \in \{1,2,3,4\}$, leaving exactly 92 triangle-free
structures, each killed by exhaustive search — machine-checked twice
with independent codebases (`endgame.py` branch-and-bound;
`endgame_brute.py` full enumeration with an independent combo
generator): RESIDUAL EMPTY; its exact-rational crossover is pinned at
$70{,}192{,}954$. The KC1 $=2$ aggregate chain (GTRANSFER §5) then gave
$N_0 = 4{,}593{,}324$ at validity $16d+8$, with its own self-asserting
exact-rational certificate (`n0_v2.py`: success at $4{,}593{,}324$,
failure at $4{,}593{,}323$). Everything in both earlier chains remains
verified — the 92-structure packing certificates stay kernel-closed in
the module (`decide`-checked) even though they are now off the proof
path — and they are retained as redundant belt.

**Sharpness.** $A^*_n$ sits exactly on every machine boundary: LOW
$=\{2\}$ (no o-pair), $|$TOP$| = 2$, and its only mixed triple
$(1, n-1, n)$ has $g_1+g_2 = g_3$ — the $x = 0$ escape. Surplus 4
leaves no room.

**Honest accounting.** The entire theorem — structural reduction, zone
collapse, CAP, dense regime, crossover, and assembly — is now verified
by the Lean 4 kernel (`h4_eq_4`); the former trust locus (the
hand-proved structural reduction) is discharged. Machine checks beyond
the kernel: the kill-count constants (exhaustive grids,
`killcount_check.py` and the independent grid in `verify_constants.py`
— worst case exactly 2, tight), the crossover identity and threshold
(exact-rational, `verify_constants.py` ALL PASS), 20k+20k
random-instance checks of both balanced-window constructions, the
validity-collection sweep to $d \le 9999$, the belt-chain finite endgame
(twice, independent codebases), and empirical validation of the machines
(`validate.py` ALL PASS: no false fire on 120 lab extremal sets; fires
on $A^*_n + x$ for every $x$, $6 \le n \le 120$; 400 adversarial random
instances; greedy-blocked near-residual structures).
Hostile Codex reviews: the original chain (thread
019ebb83…) ACCEPT-WITH-EDITS, all edits applied; the kill-count
correction and $N_0 = 4{,}593{,}324$ (thread 019ebd11…)
ACCEPT-WITH-EDITS; the kernel port and per-o-pair collapse (thread
019ebd9f…) ACCEPT-WITH-EDITS — "I did not find a hidden weakening" —
with the foil independently re-running audit + constants + full build.
The gap between the last fully-chained exact cell (§9.2) and $N_0$
stays at $h_4 \in [4,1000]$ (Thm 1.1) and is closable
only by a linear-density dense lemma (open, §11); SAT cannot reach it.

## 7. Theorem 1.4: the forbidden-set recursion and g₅(n) ≤ 3,519,219

g-side. Define $f^*_3(x,\varphi) := \varphi + \tfrac12 +
\sqrt{x+1+(\varphi-\tfrac12)^2}$ and
$f^*_k(x,\varphi) := \varphi + \tfrac12 +
\sqrt{x\,f^*_{k-1}(x,\varphi{+}1) + (\varphi-\tfrac12)^2}$.

**Lemma 7.1 (the new lemma; replaces [vD26] Lemma 7).** Let $k \ge 3$,
$F$ a finite set of positive integers, $|F| = \varphi$, and
$A_0 = \{a_1 < \dots < a_r\}$ a set of even integers $\ge 2$ with
diameter $x := a_r - a_1 \ge 2$ (i.e. $r \ge 2$; the Lean statement
carries the range guard explicitly — see §7.3). If
$r \ge f^*_k(x,\varphi)$ there exist integers $c_1,\dots,c_k$ with
(1) $c_1 \in A_0$; (2) $c_2,\dots,c_k$ nonzero, pairwise distinct,
none in $F$; (3) every subset sum containing $c_1$ lies in $A_0$.

*Proof idea.* Induction via $U_m := A_0 \cap (A_0 - m)$ with forbidden
set $F \cup \{m\}$. Van Doorn's Lemma 7 demands $s$ *disjoint*
representations of $m$ — costing a factor 2 per recursion level — only
to force $m \ne c_i$; the forbidden set does that bookkeeping at
additive cost $\varphi(r-1)$ in the count instead. Base $k=3$: if every
allowed $m$ had $|U_m| \le 1$ then $r(r-1)/2 \le \varphi(r-1) + x/2$,
contradicting $(r-1)(r-2\varphi) \ge x+1$; an allowed $m$ with
$u < u' \in U_m$ gives $(c_1,c_2,c_3) = (u',\, u-u',\, m)$. Step: some
allowed $m$ has $|U_m| \ge (r-1)(r-2\varphi)/x \ge
f^*_{k-1}(x,\varphi+1)$; recurse on $U_m$, append $c_k := m$. ∎

**Corollary 7.2 ($\varphi = 0$).** $r \ge f^*_k(x,0)$ ⇒ $A_0$ contains a
(g,k)-config ($b_1 = c_1/2$, $b_i = c_1/2 + c_i$).

**Theorem 7.3 (= 1.4, [K]).** $g_5(n) \le C_5 = 3{,}519{,}219$ for all
$n \ge 1$: van Doorn's Theorem 8 proof verbatim with Lemma 7 → Cor 7.2
($\varphi$-chain $f^*_5(x,0) \to f^*_4(x,1) \to f^*_3(x,2)$), where
$C_5$ is the least integer with
$x/12 + C_5/2 - 2 > f^*_5(x,0)$ for all $x \ge 1$ (**xineq***). The
case split (slope 1/12, central window, kill-rate 3) is unchanged.
Improvement factor over the paper-internal constant: $32.3\times$
($113{,}591{,}719 / 3{,}519{,}219$); over the Lean-stated
$1.2\cdot10^8$: $34.1\times$.

**Why only factor 32 and not more (negative results, [P]).** The audit
of every lossy step shows S2 (disjointness) was the *only* first-order
slack: slope 1/12 is rigid in this skeleton (both end-margins forced
$\ge 6\tau+2$; kill-rate 3 tight), asymmetric windows buy nothing for
$g_5$, and the new recursion is *worse* for the single-level $h_4$
chain. Dead-end map preserved deliberately (referee value;
`new-recursion.md` §4). An "O'Bryant-with-exclusions" base would push
$C_5$ to $\approx 1.81\cdot10^6$ — open (§11).

**Verification.** (i) Lean kernel — the binding check:
`g5upper_star_charter : ∀ n, gFun 5 n < 3519220` sorry-free, axioms
clean (§7.3). (ii) (xineq*) and minimality of $C_5$: pure-integer
interval certificate (`certify.py`, isqrt outward rounding, scale
$2^{48}$): 196,759 monotonicity intervals tile $[1,10^{16}]$ (min slack
$0.0745$ at $x \approx 1.4777\cdot10^8$), decreasing-ratio tail for
$x \ge 10^{16}$, $C_5 - 1$ violated at $x = 147{,}760{,}000$; mutation
tests rejected. (iii) Independent synthesis re-implementation
(Decimal-60) matches the local minimum to 10 significant digits.
(iv) Independent exact-arithmetic re-verification of the Lean numeric
layer (`verify_numerics.py`: tangency identities exact in value and
slope, slope gap $6.6\cdot10^{-7} > 0$, constant margin $14.25$).
Gate-2 anchors: the same code path reproduces van Doorn's
$113{,}591{,}719$ and the $h_4$-sketch constant 3166 exactly. Fresh
re-runs: `numerics_c3p4_fresh.log`.

### 7.3 Lean port (complete) and the statement repair

The port is **complete and kernel-verified at the charter constant**:
`Erdos866.g5upper_star_charter (n) : gFun 5 n < 3519220` and the pinned
target `T1TargetG5_closed_charter`, sorry-free on the three base axioms,
root-imported, fresh build green ($34.1\times$ below the upstream Lean
constant `g5upper`'s $1.2\cdot10^8$; audits §1.3). Ingredients: the
Lemma 7.1 induction is fully proved (`lemmaA`, by `Nat.le_induction`
over $k$, at **general** $k \ge 3$ — the disjoint-representations
bookkeeping genuinely disappears: distinctness of the appended element
comes from $b_i \notin F \cup \{m\}$), together with the general-$k$
extraction lemma `ceslemgeneral_star`; van Doorn's Theorem-8 case tree
is formalized once, parameterized over the constant $c$ with a single
key-inequality hypothesis, and instantiated at $c = 3{,}519{,}219$. The
numeric layer avoids any 196k-row certificate replay: the $u := x^{1/8}$
substitution turns the chain into square-root-free polynomial
inequalities (`key_ineq_star`, `key_ineq_star_tuned`, and the charter
`key_ineq_star_charter` via a two-regime split at $u_c = 52/5$ whose
sharp-regime margins — slope gap $3.5\cdot10^{-12}$, constant margin
$0.016$ — are razor-thin but exact-rational, checked by the kernel).
Two hostile Codex passes on the port (one per rung) returned ACCEPT,
the second with zero findings.

Formalization already paid off mathematically: as prose, Lemma 7.1 was
**false for singletons** ($x = 0$: $f^*_4(0,0) = 1 = |A_0|$ with no
structure) — the Lean statement carries the range guard
`2 ≤ max − min`, and the prose above is the repaired form. A second
trap surfaced by the port: the parameterized Theorem-8 wrapper needs
$c \ge 7$ (not $c \ge 4$) for its concentrated-edge pigeonhole —
harmless at $c = 3{,}519{,}219$ but a real failure mode for anyone
re-instantiating the wrapper at tiny constants. $C_5 = 3{,}519{,}219$
is the certified minimum for this route (Prop.-5.4-style
route-optimality): going lower needs a new route, not tuning.

## 8. General k — Theorem 1.7 **[P]**

For every $k \ge 4$ and $n \ge N(k) := k^4\cdot2^{4k+27}$ (explicit, not
optimized): $g_k(n) < 2\,n^{1-2^{2-k}}$ and $h_k(n) < 2.25\,n^{1-2^{2-k}}$,
improving [vD26 Thm 9]'s constant 4 uniformly with an explicit
threshold; the per-$k$ limsup constants are $\gamma_k = 2^{1-2^{2-k}}
\uparrow 2$ (g-side) and $\mu_k = 2((k-1)/2)^{2^{2-k}} \downarrow 2$
(h-side, $k \ge 4$). The g-chain runs van Doorn's argument through the
forbidden-set recursion $f^*$ of §7 at general $k$ (lead constant 1,
was 2); the h-chain needs one new ingredient, **Lemma A′** (a base swap
for the $h$-side: counting-with-exclusions $|U_m| \ge \varphi+3$ forces
all-positive $c_i$; its mechanics mirror the kernel-checked Lemma 7.1).
Full write-out, proofs, and constant reconciliation against the kernel
$k = 4, 5$ closures (no tension; the T1 theorems dominate at those $k$):
`lenses/C4P3-allk-writeup/T2-ALLK.md`. Machine verification:
`verify_allk.py`, exact Fraction/isqrt interval arithmetic, **272
checks PASS** (re-run at the C4 synthesis), including recursion
numerics at $k = 6,7,8$ and endgame margins $\ge 1.08\cdot10^{-2}$;
the Lemma A′ base case was additionally re-verified by an independent
brute-force implementation over 106 exhaustive + 16,224 random
hypothesis-meeting instances (`lab/synthesis_c4/`). Formal anchors
(`lemmaA`, `ceslemgeneral_star`, both T1 closures) are kernel-grade;
the all-$k$ statement itself carries **no Lean object** (honest [P];
a `gFun k n` wrapper on `ceslemgeneral_star` is the cheapest
formalization path, C5-P3).

## 9. Exact values, extremal structure, conjectures — [E]

### 9.1 Method and certificate standard

Values $m_k^v(n)$ (max config-free size) by CEGAR over CaDiCaL with a
definition-direct witness oracle. Every finished cell carries:
(i) extremal sets re-checked by two independent config checkers (Python
DFS; Rust brute force); (ii) clause-tuple UNSAT certificate re-proved by
two engines from different codebases (z3; CaDiCaL on a
sequential-counter encoding); (iii) an archived **DRAT/LRAT proof**:
reference-CaDiCaL DRAT, `drat-trim` "s VERIFIED" (emitting LRAT),
`lrat-check`, and finally **cake_lpr** — a formally verified (CakeML)
checker — "s VERIFIED UNSAT". Per-cell artifacts and sha256 in
`sat_archive/manifest.json` (quote the manifest at submission, not any
prose count). The archive verifies CNF-level UNSAT;
encoder semantics rest on exhaustive SAT-free cross-checks of 14 tiny
cells (no shared code) plus mutation controls (truncated DRAT, deleted
clause, flipped literal — all rejected). The [E] grade requires both
the lab cell and a manifest entry that is either **VERIFIED** or
**TRIVIAL_M_EQ_N** — the latter for cells with $m_k^v(n) = 2n$ (the
whole window is config-free), where no UNSAT proof exists *by design*
and the value is checked by direct construction; the dual-engine +
DRAT/LRAT chain applies to the nontrivial cells only. One archive
incident is disclosed for the record: the $h_4(62)$ cell's first DRAT
proof was *rejected* by drat-trim's backward RAT check (deletion-line
mismatches; the 382 MB proof was emitted while five other SAT jobs
saturated the machine, so transient proof-file corruption under I/O
load is the leading explanation). Not a soundness event — a rejected
proof certifies nothing and claims nothing — and the resolution kept
the trust chain intact: a clean re-run of the *same* default solver on
the identical CNF produced a proof that passed the full
drat-trim → lrat-check → cake_lpr chain (manifest entry VERIFIED; the
archive tool additionally gained a recorded `cadical --plain` fallback
for any future rejection). A cell enters a claimed range
only once its manifest entry is VERIFIED. Full-lab dual-engine
re-verification: the canonical `lab/data/verify_report.json` covers the
frozen 298-cell snapshot (every cell with a claimed value; the cell
list is read from the pinned SAT-archive manifest, sha256
`45f0eedc…`, never from a directory glob) with the identical per-cell
check throughout — `verify_cert.py --both` (z3 **and** CaDiCaL UNSAT
at $|A| \ge M+1$). For wall-clock reasons the pass was assembled from
several runs rather than one process — a detached cold pass
(2026-07-08, 90 cells; transcript `verify_canonical_c5.log`), four
stride-sharded resume runs over the remainder, and a cloud race whose
per-cell results were accepted only after a local re-hash of each
cell's input against the record and a strict match of the dual-engine
output format — and the report discloses this: it carries
`resumed: true`, the manifest sha256, and a `runs` list naming every
contributing transcript with its cell count. **Final counts: 298/298
cells, 0 failures** (completed 2026-07-08; SUBMIT.md gate G1 GREEN;
also quoted in Appendix B). Cells landing after the snapshot
($h_4(65)$–$h_4(68)$, $g_5(24)$, $g_5(25)$) are not covered and not
claimed.

### 9.2 Exact-value tables

Generated from cells by `make_tables.py` (authoritative copy:
`lenses/C4P4-publication/paper/tables-866.md`, regenerated at this
draft; do not hand-edit). Headlines:

- **$g_5(n) = 4$ for $15 \le n \le 23$** — the first exact $g_5$ values
  beyond van Doorn's $n \le 15$ search, directly on his flagged question
  ("cannot even exclude $g_5(N) \le 4$ for all large $N$"); $g_5 = 5$ on
  $5 \le n \le 14$ (sporadic onset). Every cell in the range carries
  DRAT/LRAT + cake_lpr VERIFIED archive proofs and Rust-checked
  extremal sets; the $n = 22$ value is exact with
  extremal-set enumeration time-capped (7 extremal sets recorded), and
  $n = 23$ is a full exact solve (64 extremal sets, all Rust-checked).
- $h_4(n) = 4$ for $n \in \{3,4\} \cup [6,64]$; $h_4(5) = 5$ (sporadic);
  with **unique** extremum $A^*_n$ for $11 \le n \le 64$ (enum-exact;
  equality with $A^*_n$ checked cell-by-cell; the $62$–$64$ archive
  chains landed at this draft — see §9.1 for the disclosed $h_4(62)$
  proof-rejection incident and its clean-re-run resolution). The
  dual-engine (z3 + CaDiCaL) re-proof of every cell, including these,
  is the release-gated canonical pass of §9.1 (SUBMIT.md G1).
- $h_5(n) = z(n)+1$ for all computed $13 \le n \le 26$, spanning the
  Fibonacci jump at $n = 21$.
- $g_4(n) = 3$ at every computed $n \ge 2$ (through $n = 40$, plus the
  $n = 60$ cell landed at this draft), with unique extremum = van
  Doorn's family odds ∪ $\{2n-2, 2n\}$ at both $n = 40$ and $n = 60$ —
  direct exact refutations of the agentic-erdos $g_4(40)/g_4(60) \ge 4$
  claims (§9.4).

### 9.3 Conjecture ledger (tested against every computed cell)

(C1) $h_4(n) = 4$ for all $n \ge 6$ — settled for $n \ge 331{,}777$
(Thm 1.3, kernel-grade) and at the computed exact cells (§9.2); open in
between (a finite but SAT-infeasible gap; see §11, item 2).
(C2) $g_5(n) = 4$ for all $n \ge 15$ — the g-side transfer question; the
$x=0$ equality-triangle escape is legal on the g-side, so the (T★)
machine *strengthens*, and the endgame becomes a (3,2)-machine
enumeration with a zero anchor. Status: **the structural program is now
§10** — the per-anchor dichotomy (†) [P], Theorem Z's all-low/all-top
zone reduction ([P] minus one named audit), a conditional capacity
ceiling shrinking the open band to $d \in [5,19]$, and an in-flight
$n$-free enumeration, **empty in every completed line** (m=4 through
$d\le5$ (L) / $d\le4$ (T), m=5 through $d\le8$, plus the complete
$d=0$ case at $n=15..55$ and $2009/2010$) — in particular the
$A^*_n$-type h-side extremal *dies* on the g-side, killed exactly by
the legalized $x = 0$ anchor. Remaining before a theorem: §10.5's
named list (sweep completion, Lemma C at general width, the $d=0$
write-up, the Theorem-Z audit, the exact $N_{0,g}$ crossover).
(C3) $h_5(n) = z(n)+1$ for all $n \ge 13$.

### 9.4 Refutation note

The repository przchojecki/agentic-erdos claims randomized-search lower
bounds $g_4(40) \gtrsim 4$ and $g_5(40) \gtrsim 13$. These contradict
the Lean-verified $g_4(n) = 3$; the bug is reproducible — requiring
$b_i \in A$ reproduces all four claimed cells exactly. Explicit
witnesses (e.g. $b = (0,1,2,77)$ at $n = 40$) and diagnosis:
`lenses/P5-hygiene/refutation/refutation-przchojecki-866.md`. The
$g_5 \approx 13$ claims carry no evidential weight (same broken
checker), though they are not formally disproved.

## 10. Toward $g_5 = 4$: the per-anchor collapse — graded per part, no exact-value claim

This section reports the g-side structural program (C5-P1 lens,
artifacts `lenses/C5P1-g5eq4/`: `GZONES.md`, `verify_gkill.py`,
`verify_zones.py`, `endgame_v2.py`, `d0_check.py` + logs). **We do not
claim $g_5(n) = 4$ or $g_5(n) \le 5$ for any $n$ here.** Grades are
stated per part; none of this section is [K].

Conventions as in §6: $A \subseteq [1,2n]$ config-free at surplus $m$,
$D$ the missing odds with $d = |D|$, $\Lambda = E/2 \subseteq [1,n]$ the
halved evens, $p = |\Lambda| = d+m$. For a triple
$T = \{a<b<c\} \subseteq \Lambda$ write $x = a+b-c$, $y = a+c-b$,
$z = b+c-a$; on the g-side $x \le 0$ is *legal* as the unique
non-positive summand — exactly the equality-triangle escape that
separates $g_5$ from $h_5$.

### 10.1 The unified per-anchor dichotomy (†) — [P]

The per-o-pair collapse that closed Thm 1.3 (§6, `balanced_kill`)
transfers to the g-side and comes out *stronger*: the three-branch
g-side case algebra (the (A)/(B)/(N) analysis of the earlier transfer
notes, `GTRANSFER.md` §3) merges into one two-sided dichotomy per
anchor. Three lemmas (proofs: `GZONES.md` §1):

- **Lemma U (window unification).** For fixed $(T, u)$,
  $u \in \Lambda$, the f-pairs $(2u-f_2, f_2)$ completing $(x,y,z)$ to
  a 5-config candidate are exactly those with
  $f_2 \equiv (a+b+c+1) \bmod 2$ and
  $u < f_2 \le \min(2u-1+x,\ 2n-1-z)$ — one contiguous window. The
  zero/negative anchor lives *inside* the window; the separate case
  (N) disappears.
- **Lemma K (per-anchor kill count).** One missing odd kills at most
  **3** admissible f-pairs of a fixed $(T,u)$ (tight).
- **Lemma G (g-side balanced kill).** In a config-free $A$ with odd
  coverage there is no $(T,u)$ with $u+x \ge 6d+4$ and
  $u+z \le 2n-6d-4$: the $3d+1$ stepped pairs beat the $3d$ kill
  budget. Hence, with $K_1 := 6d+2$:

> **(†)** for every $T = \{a<b<c\} \subseteq \Lambda$ and every
> $u \in \Lambda$: $\;u + (a{+}b{-}c) \le K_1+1\;$ **or**
> $\;u + (b{+}c{-}a) \ge 2n - K_1 - 1$.

Machine verification (`verify_gkill.py`, exact integers): window =
definition *exhaustively* over 267,503 $(n,T,u)$ cells
($n \in \{12,13,30,31\}$); kill map worst count 3, tight, over 40,012
nonempty cells; 109,386 Lemma-G construction instances
(admissible + distinct); 3,000 random (†)-violating $(n,\Lambda,D)$
each completed to an explicit 5-config with all 10 sums verified in
$A$. One hostile review pass (verdict ACCEPT on this part);
independently re-run green at the C5 synthesis and by the reviewer.
Grade: **[P]** (written proof + exhaustive machine checks at small
$n$ + independent re-runs). Lean port is chartered, not done:
`G_kill` has the same shape as the kernel-verified `K_epairs_le2` of
§6.

### 10.2 Theorem Z: zone reduction from (†) alone — [P] minus one named audit

**Theorem Z.** Let $A$ be 5-config-free at surplus $m \ge 4$ with
$p = d+m \ge 5$ and $n \ge 66d+36$. Then $\Lambda = \{\lambda_1 <
\dots < \lambda_p\}$ is either
**(L) all-low** — $\lambda_{p-2}+\lambda_{p-1} \le K_1+1$ (so the
$p-2$ core elements lie in $[1, 3d+1]$) and $\lambda_p \le 12d+6$ — or
**(T)** the exact **all-top mirror** in offsets $\delta_i = n -
\lambda_i$. In particular: no mixed low/top sets and no middle
elements. (The 12d+8 two-sided windows of the earlier draft-grade
reduction shrink to a $3d+1$ core plus two stragglers, and the
reduction is now a one-page case tree of (†) instances —
`GZONES.md` §2.)

Machine verification (`verify_zones.py`): 59,228 stratified
adversarial samples ($d \in [1,8]$; mixed/mid/half-point/Fibonacci/
cluster shapes) — every (†)-consistent sample lies in (L) ∪ (T) —
plus an exhaustive $d = 1$ boundary sweep. Hostile review verdict
ACCEPT-WITH-EDITS; all findings adopted in place. Grade: **[P] minus
one named pending item** — a fresh-eyes audit of the case tree (the
arithmetic at the binding validity $n = 66d+36$ was already once
corrected under review), chartered for the next campaign. We do not
build any public claim on Theorem Z until that audit lands.

### 10.3 Capacity ceiling — conditional [D]: the one mathematical hole is named

**Lemma C (open at general width).** If some sum $S$ has $r(S) \ge 3$
representations $S = \alpha+\beta$ ($\alpha \le \beta \in \Lambda$),
then three of them admit a role-assignment forming a *valid 4-block*
(4 distinct integers, $\le 1$ non-positive, all 6 pairwise sums even
and present), which is fatal for $n \ge 16d + c_0$ (its anchor window
carries $> 4d$ survivors at kill count $\le 4$). Evidence: exhaustive
machine decision at widths $W \le 18$ (21,817 $r\ge3$ instances, zero
failures) extended independently by the hostile reviewer to $W = 24$
(701,481 instances, zero failures); translation covariance moves
fixed-width configurations but does **not** lift the evidence to
arbitrary width. **The general-$W$ case analysis is an open write-up;
the reviewer's verdict on this part was REJECT-as-written until it is
proven, and we adopt that**: everything downstream of Lemma C is
stated conditionally.

*Conditional on Lemma C*, Theorem Z's core-in-a-box forces, by pair-sum
counting in a box of $3d+2$ values: at $m = 4$, $d \le 18$ (L) /
$d \le 19$ (T); at $m = 5$, $d \le 16$ (L) / $d \le 17$ (T). The
untouched middle band of the earlier analysis, $d \in [5, \sim 87]$,
shrinks to $d \in [5, 19]$. Grade: **[D], conditional** (machine
evidence exhaustive at small scales; general proof open).

### 10.4 The middle band as a finite $n$-free enumeration — [E]-in-progress

For zone candidates the (†)-window endpoints resolve $n$-freely in
mirror/offset coordinates (given $n$'s parity), so each
$(m, d, \text{branch}, n\text{-parity})$ candidate set and its
hitting-set verdict is independent of $n$ beyond the validity
threshold — this *removes* the $n$-stability scope limitation of the
earlier census. `endgame_v2.py` enumerates all
(L)/(T) candidates with $+2$ slack boxes at four large $n$ (two per
parity) and asserts equality of normalized per-candidate verdict maps
across same-parity runs (upgraded from raw counts under review). DFS
pruning (per-$(T,u)$ counts; valid 4-blocks) is sound under extension.

**Sweep status at this draft (disk-read 2026-06-12 21:33 machine-local;
detached jobs still running):** every completed line **EMPTY** with the
$n$-free certificate OK — $m=4$: (L) through $d \le 6$, (T) through
$d \le 5$; $m=5$: both branches through $d \le 8$; **0 survivors in
all 31 completed $(m,d,\text{branch})$ lines**; targets are the
conditional ceilings of §10.3 ($d \le 19$ resp. $17$). The $d \le 4$
lines reproduce the independent C3-era enumeration exactly. Separately,
the $p = 4$ case ($d = 0$, $m = 4$ — outside Theorem Z's $p \ge 5$):
exhaustive over **all** $\Lambda$ (no zone assumption) for
$n = 15..55$ and wide-window sweeps at $n = 2009/2010$, all EMPTY,
run **DONE**; its O(1) hand write-up is a named TODO and stays out of
any assembly. Grade: **[E]-in-progress** (finite computation; harvest
incomplete — any survivor line would itself be a discovery: the first
concrete g-side obstruction family beyond the h-side extremal).

### 10.5 Assembly shape and honest status

If (and only if) the named items close — sweeps empty through the
ceilings, Lemma C at general $W$, the $d=0$ write-up, the Theorem-Z
audit — then $g_5(n) = 4$ assembles for $n \ge N_{0,g}$ as
STRUCTURAL (Z + enumeration $d \le 19$ + capacity $d \ge 20$) + DENSE
(upstream `ceslemgeneral`, $k=5$) with $N_{0,g} \approx 10^{18}$ at
the proven validity slope $1/66$; the slope optimization
($66 \to \sim 16$, tightening the threshold chain) is the named lever
back toward $\sim 2\cdot10^{13}$. The $g_5 \le 5$ rung has the
identical skeleton at $m = 5$ and ships only when the same machinery
closes there. Until then, the strongest true statements remain
Thm 1.6's exact cells ($g_5(n) = 4$ on $15 \le n \le 23$) and the
(†)/Theorem-Z structure above at their stated grades.

## 11. Open problems

1. **$g_5(n) = 4$ for all $n \ge 15$?** (van Doorn's question; the
   actual Erdős-side ask.) The per-o-pair collapse of §6 *does*
   transfer — §10 derives the one-window per-anchor dichotomy (†),
   Theorem Z's two-shape zone reduction, and a conditional capacity
   ceiling at $d \le 19$, with the $n$-free enumeration empty in every
   completed line. What remains is §10.5's named list, headed by
   Lemma C at general width and the sweep harvest; assembly would give
   $g_5(n) = 4$ for $n \ge N_{0,g} \approx 10^{18}$ at slope $1/66$,
   with the slope optimization ($\to \sim 16$) the lever back toward
   $\sim 2\cdot10^{13}$. The first rung $g_5 \le 5$ (large $n$) has
   the identical skeleton at $m = 5$.
2. **The gap $[65, N_0)$ for $h_4 = 4$:** needs a dense lemma at linear
   density ($F_4$-type bounds are $n^{3/4}$); further constant-tuning of
   $N_0 = 331{,}777$ within the current chain is not expected to beat
   $\sim 2.4\cdot10^5$. SAT can never reach $N_0$; ladder extension only
   nibbles the left end.
3. **O'Bryant-with-forbidden-differences:** would push $C_5$ to
   $\approx 1.81\cdot10^6$ and flip the $h_4$ chain.
4. **Slope-1/12 barrier** for $g_5$: provably rigid in the vD skeleton
   (§7); new geometry needed for orders-of-magnitude progress.
5. **g-version of CES Theorem 6** (ambiguity A9): is
   $g_k(n) > n^{1-\epsilon}$ for $k \ge k_0(\epsilon)$? The CES example
   analysis predates the g/h split.

## 12. Methods, verification doctrine, and AI disclosure

**AI disclosure.** The mathematics in this paper was produced by an
AI-agent workflow: Claude (Anthropic) agents generated the proofs,
certificates, code and Lean formalizations across three campaigns of an
iterated attack program; GPT-5.5 (OpenAI, via Codex) served as a
standing *adversarial* referee — every headline result passed at least
one hostile review pass (verdicts and finding dispositions are archived
with thread ids in the program records), and review findings led to
real repairs (notably the Lemma 7.1 singleton bug, §7.3, and the
fixed-$(s,t)$ qualifier in §6's (K)). The upstream Lean development we
build on was formalized by Aristotle (Harmonic) for van Doorn [L866].
Human role: program direction and final review. Every theorem stated as
[K] is machine-checked by the Lean 4 kernel and carries an axiom audit.
Both previously named trust loci are now **discharged in Lean**: the
hand-proved structural reduction of §6 (Thm 1.3's upper half) closed
kernel-grade as `structural_case`/`h4_eq_4` (C4-P1; the (K)
double-count scaffold was formalized *first*, precisely where a hand
error would have surfaced, and the reduction survived), and the
Lemma 7.1 induction of §7 was fully proved earlier (§7.3), the
formalization process itself catching and repairing a real statement
bug (the singleton case). The remaining non-kernel claims are graded
[P]/[E] with their checking artifacts named (§8, §9). No [K] label in
this paper rests on unverified AI output; [P]/[E]/[D] labels state
exactly which parts are machine-checked and which are reviewed prose.

**Verification doctrine.** (i) Exact arithmetic only — integer/rational
interval certificates with outward rounding; no floating-point claim
enters a proof. (ii) Dual independent checkers for every computation
(different codebases, ideally different languages/engines). (iii)
Negative controls: mutated certificates must be rejected. (iv)
Independent re-verification at each campaign synthesis (fresh
implementations, not reruns). (v) SAT results carry archived
DRAT/LRAT proofs checked by a formally verified checker (§9.1). (vi)
Lean: upstream byte-pinned (sha256-verified at every audit), extension
modules sorry-free, `#print axioms` on every cited theorem, fresh
`lake build` at audit time. (vii) An openness kill-check against the
literature is re-run immediately before any public claim (§13).

**Reproducibility.** Single entry point per claim; all spawned compute
at idle priority; artifact map in Appendix B.

## 13. Openness kill-check — FRESH RUN AT DRAFT COMPLETION

**Run 2026-07-08 (release freeze, Draft v5) — all 8 items re-fetched
live this session.** erdosproblems.com/866 HTTP 200 (browser-grade
fetch), OPEN, "cannot be resolved with a finite computation", last
edited 01 December 2025, still citing $g_4 \le 2032$; forum thread 866
newest comments still 04 May 2026; arXiv:2605.00040 still **v1 only**
(live fetch of the submission history); Woett `ErdosProblem866.lean`
still `1e075c4f6e8a` (2026-04-30, GitHub API); przchojecki still
`c58f8589` (2026-05-10); teorth problems.yaml #866 `state: "open"` /
`formalized: "no"` (raw, live); web search (multiple phrasings) clean.
**One delta, assessed non-superseding:** plby/lean-proofs has continued
work on its `Erdos866b.lean` port (2026-06-29 v4.32.0 re-add,
2026-06-29 build fix, 2026-07-02 proof fill-in; file at HEAD
`97957fb9` is sorry-free) — the diffs were read: it formalizes the
**same known theorem set at the same constants** ($h_4 \le 2270$,
$g_4 = 3$, $g_3 = 1$, van Doorn's results), no improved bound, no
exact-value theorem; every bound this paper improves remains the
published best. Verdict **GREEN**. Prior records retained for
provenance:

**Run 2026-06-13 (C6 session, Draft v4), by the C6-P2 release-gate
lens — all 8 items re-fetched live this session: UNCHANGED on every
item.** erdosproblems.com/866 HTTP 200, OPEN, "cannot be resolved with
a finite computation", last edited 01 December 2025, still citing
2032; forum newest 04 May 2026; arXiv:2605.00040 still v1 (live
fetch); Woett `ErdosProblem866.lean` still `1e075c4f6e8a` (2026-04-30,
gh API); plby/lean-proofs `6d0ba683` (2026-06-11, style-only);
przchojecki `c58f8589` (2026-05-10); teorth problems.yaml #866
`state: "open"` / `formalized: "no"` (raw, live); web search clean
(nothing citing, improving, or superseding). Verdict GREEN. The C4-era
record below is retained for provenance:

**Run 2026-06-12 (C4 session), by the C4-P4 lens (this draft's author agent), per
PROBLEM.md §8 — all items re-fetched live this session:**

1. **erdosproblems.com/866** (fetched live, HTTP 200): status **OPEN** —
   "open, and cannot be resolved with a finite computation."; page last
   edited 01 December 2025 (unchanged since the freeze; still citing
   $g_4 \le 2032$).
2. **Forum thread 866**: newest comment still 04 May 2026 (van Doorn's
   bounds + Sothanaphan congratulations); nothing newer.
3. **arXiv:2605.00040**: still **v1 only** (submitted 2026-04-28); no
   revision, no superseding submission found by search.
4. **Woett/Lean-files `ErdosProblem866.lean`**: last commit touching the
   file still `1e075c4f6e8a` (2026-04-30) — GitHub API, live.
5. **plby/lean-proofs `Erdos866b.lean`**: last commit touching the repo
   2026-06-11 ("Address linter.style.refine in Erdos866b") — style-only
   churn, same theorems, same constants.
6. **przchojecki/agentic-erdos**: last repo commit still 2026-05-10
   (`c58f858`); no new claims.
7. **teorth/erdosproblems `problems.yaml`** (main, raw, live): #866
   `state: "open"` (last_update 2025-08-31), `formalized: "no"`.
8. **Web search** (multiple phrasings): no citing, improving, or
   superseding work found.

**Verdict: open; every standing bound this paper improves is still the
published best.** A strict-improvement claim dies if superseded; the
formalization claims survive any scoop (the Lean theorems are ours
regardless; the kill-check decides framing, not whether to finish).
Re-run again immediately before submission.

## Appendix A. Certificate file formats

`cert_energy.csv` / `cert_ruzsa.csv`: rows
$(\tau_{lo}, \tau_{hi}, \Phi_L, \nu_L, \psi_L, \Phi_H, \nu_H, \psi_H)$
tiling $[0, 4\cdot10^5]$; conditions V2–V5 checked per row in exact
integers (and, for the energy form, re-proved row-wise by Lean kernel
`decide`). Cell JSON schema: `{n, k, variant, M, value, extremal_sets,
clause_tuples, status, engines, time_s}`. DRAT/LRAT archive layout and
the full soundness chain: header of `sat_archive/make_drat_archive.py`;
per-cell sha256 in `manifest.json`.

## Appendix B. Verification artifact map

| Claim | Primary artifact | Independent check | Fresh re-run (this draft) |
|---|---|---|---|
| Thm 1.1 | Lean `h4_le_1000` + `cert_energy.csv` | `check_cert.py` ACCEPT; `verify_central.py` re-sweep; mutation tests | `auditC4P4.log`; `numerics_c3p4_fresh.log` [1,3] |
| Thm 1.1′ | `cert_ruzsa.csv` | same pair | `numerics_c3p4_fresh.log` [2,3] |
| Thm 1.2 | Lean `four_le_hFun_four` | Python DFS + Rust checker on $A^*_n$ | `auditC4P4.log` |
| Thm 1.3 | **Lean `h4_eq_4`** (H4Dichotomy, root-imported) | `verify_constants.py` ALL PASS (x24 identity, $q(23)<0<q(24)$, fib CAP to $d=1000$, independent KC1 $=2$ grid tight, 20k+20k balanced-window instances, validity sweep $d \le 9999$; re-run at C4 synthesis); hand chains: DICHOTOMY.md + GTRANSFER.md §5 with `killcount_check.py`, `n0_v2.py`, belt `endgame.py`/`endgame_brute.py`, `validate.py` | `auditC4P1.log` + `c4p1_fullbuild.log` (8039 jobs); `auditC4Synth.log` + from-scratch `c4synth_build.log`; belt re-runs `n0_v2_rerun_c4.log` (star6 PASS at 4,593,324 / fail 4,593,323) + `killcount_rerun_c4.log` (KC1–KC4 ALL PASS) |
| Thm 1.4 | Lean `g5upper_star_charter` + `certify.py` certificate | `verify_recursion.py` (Decimal-60); `verify_numerics.py` (exact tangency identities); mutation report | `auditC4P4.log`; `numerics_c3p4_fresh.log` [4,6] |
| Thm 1.5 | Lean `fibCnt_lt_hFun_five` | `verify_families.py` DFS; $10^6$ sweep | `auditC4P4.log`; `numerics_c3p4_fresh.log` [5] |
| Thm 1.6 | lab cells | dual-engine + DRAT/LRAT + cake_lpr archive | canonical `lab/data/verify_report.json` — frozen 298-cell snapshot, pinned-manifest cell list (sha256 `45f0eedc…`), per-cell `verify_cert.py --both`; **completed 2026-07-08: n_cells = 298, n_failed = 0** (SUBMIT.md G1 GREEN; multi-run assembly disclosed in the report's `runs` list — see §9.1); archive manifest 273 VERIFIED + 25 TRIVIAL_M_EQ_N = 298/298, 0 FAIL (G2); belt dual-engine re-proof of the late cells $h_4(62$–$64)$, $g_5(23)$: 4/4, 0 failures (`verify_new_cells_c5_report.json`, G3) |
| §10 (g-side program; no claim) | `lenses/C5P1-g5eq4/GZONES.md` | `verify_gkill.py` (267,503-cell exhaustive window check; KC tight at 3; 109,386 + 3,000 instances), `verify_zones.py` (59,228 adversarial + exhaustive $d{=}1$; Lemma C 21,817 + independent 701,481 instances), both re-run independently at the C5 synthesis and by the hostile reviewer | sweep logs `eg_m{4,5}_{L,T}.log`, `d0_check.log` (in flight at this draft; status as quoted in §10.4, disk-read 2026-06-12 21:33 machine-local) |

## Appendix C. Lean formalization inventory (audited 2026-06-12/13 (C4–C5 sessions))

Toolchain: lean4 v4.28.0, mathlib 8f9d9cff6bd7. Upstream
`Erdos866/Upstream.lean` byte-pinned, sha256
`043731e35444d446ad8effeb8a5f1febdc904991bf9b9312c3acc2c17ca9845e`
(= GitHub Woett/Lean-files main @ 1e075c4f6e8a), re-hashed at the
C4-P1 and C4-synthesis audits (Codex re-hashed independently). Root
module imports (**all sorry-free**): Statements,
Warmup, G5Small, LowerBounds, H4Cert, H4Tail, H4Improved, H4Target,
G5FStar, G5Port (the former G5FStar stubs `lemmaA` and
`ceslemgeneral_star` are now fully proved in G5Port; quarantine
lifted), and **H4Dichotomy** (the Thm 1.3 port, de-quarantined at
C4-P1: dense regime, both (K) double-counts, the per-o-pair
`K_epairs_le2` + `balanced_kill` collapse, `T_star`,
`triangle_free_fib`/`cap_fib`, `structural_case`, and `h4_eq_4` all
kernel-closed; the 92-structure packing certificates retained as
belt). Paper-item map: Thm 1.1 =
`h4_le_1000` [K]; Thm 1.2 = `four_le_hFun_four`,
`gFun_four_lt_hFun_four` [K]; **Thm 1.3 = `h4_eq_4` [K]** (corollaries
`h4_eq_4_charter`, `h4_eq_4_c2`); Thm 1.4 = `g5upper_star_charter` (+
fallback `g5upper_star`, targets `T1TargetG5_closed_charter` /
`_3520600`, engine `lemmaA` + `ceslemgeneral_star` at general $k$,
numeric layer `key_ineq_star*`, `fStar5_le_poly`) [K]; Thm 1.5 =
`fibCnt_lt_hFun_five` [K]. Upstream anchors cited:
`weak_sidon_key_ineq`,
`weak_sidon_bound`, `ceslemgeneral_pos`, `ceslemgeneral`, `h4upper`,
`g5upper`, `h5lower`, `g5lower`, `g4`, `gFun_le_hFun_le_gFun_succ`,
`generalupper`. **Audit coverage:** every theorem named in this
appendix — including each upstream ingredient cited as [K] in the body
(`weak_sidon_key_ineq` in Lemma 4.1, `ceslemgeneral_pos` in §6) —
appears explicitly in `lean/scripts/auditC4Synth.log` (28 declarations
+ compile-time statement pins, incl. $331777 = 24^4+1$ and
`hFun`-by-`rfl`; the H4Dichotomy declarations additionally in the
module-scoped `auditC4P1.log`) with axioms exactly
`[propext, Classical.choice, Quot.sound]` (the `decide`-backed
`dichoCerts_ok` drops `Classical.choice`) and zero sorryAx, against a
from-scratch rebuild (`c4synth_build.log`, 8039 jobs).

## Appendix D. Reproducibility

Every numeric claim has a single re-run entry point (Appendix B, last
column). SAT pipeline tooling: CaDiCaL (reference binary), z3,
drat-trim, lrat-check, cake_lpr (binary built from repo-pinned source,
sha256 in archive manifest). All long-running compute at OS idle
priority.

## References

- [CES75] S. L. G. Choi, P. Erdős, E. Szemerédi, *Some additive and
  multiplicative problems in number theory*, Acta Arith. **27** (1975),
  37–50.
- [Er72] P. Erdős, *Extremal problems in number theory* (Proc. Number
  Theory Conf., Boulder, Colo., 1972), 80–86.
- [Er92c] P. Erdős, *Some of my forgotten problems in number theory*,
  Hardy–Ramanujan J. **15** (1992), doi:10.46298/hrj.1992.125 (the
  $g_k$ discussion at p. 41). *(Venue/DOI verified via
  hrj.episciences.org/125, 2026-06-12.)*
- [vD26] W. van Doorn, *The cardinality of a set containing the pairwise
  sums of a fixed number of integers*, arXiv:2605.00040v1 (2026).
- [L866] W. van Doorn (informal), Aristotle/Harmonic (formal),
  *ErdosProblem866.lean*, github.com/Woett/Lean-files, commit
  1e075c4f6e8a (2026-04-30); maintained port: github.com/plby/lean-proofs
  `Erdos866b.lean`.
- [Ru93] I. Z. Ruzsa, *Solving a linear equation in a set of integers I*,
  Acta Arith. **65** (1993), no. 3, 259–282. (Weak-Sidon bound,
  Thm 4.6.) *(Title/venue verified via impan.pl Acta Arith. 65/3,
  2026-06-12.)*
- [OB24] K. O'Bryant, *On the size of finite Sidon sets*, Ukr. Mat. Zh.
  **76** (2024), no. 8, 1192–1206, doi:10.3842/umzh.v76i8.7858; English
  translation: Ukr. Math. J. **76** (2025), 1352–1368,
  doi:10.1007/s11253-024-02392-x; arXiv:2207.07800. (Sidon bound
  $\sqrt n + 0.99703\,n^{1/4}$, used by vD26's $f_3$.) *(Verified
  against arXiv abs page + Springer, 2026-06-12.)*
- [Bl] T. F. Bloom, *Erdős Problem #866*, erdosproblems.com/866,
  accessed 2026-06-12.
- [Tan21] Y. K. Tan, M. J. H. Heule, M. O. Myreen, *cake_lpr: Verified
  propagation redundancy checking in CakeML*, TACAS 2021, LNCS 12652,
  223–241, doi:10.1007/978-3-030-72013-1_12. *(Verified via dblp,
  2026-06-12.)*
- [Bie20] A. Biere, K. Fazekas, M. Fleury, M. Heisinger, *CaDiCaL,
  Kissat, Paracooba, Plingeling and Treengeling entering the SAT
  Competition 2020*, in Proc. of SAT Competition 2020 — Solver and
  Benchmark Descriptions (T. Balyo et al., eds.), Department of
  Computer Science Report Series B, vol. B-2020-1, University of
  Helsinki, 2020, pp. 50–53. *(Verified via tuhat.helsinki.fi
  proceedings PDF, 2026-06-12 (C4 session).)*
- [WHH14] N. Wetzler, M. J. H. Heule, W. A. Hunt Jr., *DRAT-trim:
  Efficient checking and trimming using expressive clausal proofs*,
  SAT 2014, LNCS **8561**, Springer, 2014, pp. 422–429,
  doi:10.1007/978-3-319-09284-3_31.
- [dMB08] L. de Moura, N. Bjørner, *Z3: An efficient SMT solver*,
  TACAS 2008, LNCS **4963**, Springer, 2008, pp. 337–340,
  doi:10.1007/978-3-540-78800-3_24.
- [mathlib] The mathlib Community, *The Lean mathematical library*,
  CPP 2020.
