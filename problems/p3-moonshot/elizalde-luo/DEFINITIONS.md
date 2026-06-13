# Elizalde-Luo {1132,3312} conjecture: pinned definitions and ground truth

**Source.** Sergi Elizalde and Amya Luo, *Pattern avoidance in nonnesting permutations*,
arXiv:2412.00336; published version: Discrete Mathematics & Theoretical Computer Science
(DMTCS), vol. 27:1 Permutation Patterns 2024, paper #13 (2025), DOI `10.46298/dmtcs.14885`.
The LaTeX source of the published version is in `src/formatted.tex` (extracted from
`el.tar.gz`); all line numbers below refer to that file.

---

## 1. Objects

`src/formatted.tex`, line 117 (verbatim):

> We denote by $\nn = \{1,1,2,2,\dots, n,n\}$ the multiset consisting of two copies of
> each integer between $1$ and $n$.

A *permutation of* $[n]_2$ is a word of length $2n$ over $\{1,\dots,n\}$ using each
letter exactly twice. **The count is over all such labeled words — no quotient by
relabeling is taken** (see Section 5 below).

## 2. Pattern containment convention (what repeated pattern letters require)

`src/formatted.tex`, lines 119-124 (verbatim):

> Given two words $\pi=\pi_1\pi_2\dots\pi_m$ and $\sigma=\sigma_1\sigma_2\dots\sigma_k$
> over the positive integers $\bbN$, we say that $\pi$ {\em contains} the pattern
> $\sigma$ if there exist indices $1\le i_1<i_2<\dots<i_k\le m$ such that the
> subsequence $\pi_{i_1}\pi_{i_2}\dots\pi_{i_k}$ is in the same relative order as
> $\sigma$, that is,
> - $\pi_{i_r}<\pi_{i_s}$ if and only if $\sigma_r<\sigma_s$, and
> - $\pi_{i_r}=\pi_{i_s}$ if and only if $\sigma_r=\sigma_s$,
>
> for all $r,s\in[k]$. This subsequence is called an {\em occurrence} of $\sigma$.
> If $\pi$ does not contain $\sigma$, we say that $\pi$ {\em avoids} the pattern
> $\sigma$.

Both conditions are **biconditional**: equal pattern letters must map to *equal* word
letters, and strictly ordered pattern letters must map to *strictly* ordered word
letters. Concretely, since every value occurs exactly twice in a permutation of
$[n]_2$:

- $w$ **contains 1132** iff there are positions $i<j<k<l$ and values $a<b<c$ with
  $w_i=w_j=a$, $w_k=c$, $w_l=b$. (The two pattern 1's are the two copies of one value
  $a$; then a strict descent $c>b$ with both entries $>a$, occurring after the second
  copy of $a$.)
- $w$ **contains 3312** iff there are positions $i<j<k<l$ and values $a<b<c$ with
  $w_i=w_j=c$, $w_k=a$, $w_l=b$. (The two pattern 3's are the two copies of one value
  $c$; then a strict ascent $a<b$ with both entries $<c$, occurring after the second
  copy of $c$.)

## 3. Nonnesting permutations (which equality patterns)

`src/formatted.tex`, line 135 (verbatim):

> With this perspective, it is natural to consider permutations of $\nn$ whose
> corresponding matching is nonnesting, i.e., there are no two arcs $(i_1,i_4)$ and
> $(i_2,i_3)$ where $i_1<i_2<i_3<i_4$. They can be defined as permutations of $\nn$
> that avoid the patterns $1221$ and $2112$. Following~\cite{elizalde_nonnesting}, we
> call these {\em nonnesting permutations}, and we denote by $\cC_n$ the set of
> nonnesting permutations of $\nn$.

I.e. nonnesting $\iff$ no indices $i_1<i_2<i_3<i_4$ with
$w_{i_1}=w_{i_4}\neq w_{i_2}=w_{i_3}$ (both relative orders $1221$ and $2112$ are
excluded by the containment convention above). The paper's example (line 136):
$1521352434\in\cC_5$, but $13241342\notin\cC_4$ because of the subsequence $2442$.

Total count (line 137-138): $|\cC_n| = n!\,\Cat_n = \frac{(2n)!}{(n+1)!}$.

**Structured form (validated, not assumed):** a matching of $[2n]$ is nonnesting iff
its $i$-th closer (second occurrence, in position order) is matched to its $i$-th
opener (first occurrence). Hence nonnesting words $=$ (Dyck shape of length $2n$)
$\times$ (permutation $p\in S_n$ labeling the arcs in opener order). This was verified
by exhaustive set-equality against the literal 1221/2112 definition for $n\le 5$ and
by count for $n=6$ (`data/validation.json`, V2).

## 4. The conjecture (verbatim)

`src/formatted.tex`, Section 4 "Further research", lines 1599-1621. Preamble
(line 1600):

> In Table~\ref{tab:conjecture} we list some cases that seem to give interesting
> enumeration sequences. All the conjectures have been checked for $n$ up to $8$.

The relevant row of Table 4 (`tab:conjecture`, line 1614):

> $\{1132,3312\}$ & $3^n-3\cdot2^{n-1}+1$ & A168583

with table caption (line 1619): "Some conjectures on the enumeration of nonnesting
permutations avoiding other patterns." In the paper's notation the claim is
$$\cc_n(1132,3312) = 3^n - 3\cdot 2^{n-1} + 1 \quad (n\ge 1).$$

**OEIS cross-reference.** A168583 ("The number of ways of partitioning the multiset
{1,1,2,3,...,n-1} into exactly three nonempty parts", offset 3, fetched June 2026):
data `1, 4, 16, 58, 196, 634, 1996, 6178, 18916, 57514, ...`; formula "For a>=3,
a(n) = 3^(n-2) - 3*2^(n-3) + 1"; o.g.f. `x^3*(1-2x+3x^2)/((1-x)*(1-2x)*(1-3x))`;
linear recurrence signature (6,-11,6). So the conjectured count is the **shift**
$\cc_n(1132,3312) = A168583(n+2)$, equivalently $a_n = 6a_{n-1} - 11a_{n-2} + 6a_{n-3}$
with $a_1=1, a_2=4, a_3=16$.

**Small values implied by the formula** (the paper does not tabulate them for this
row; it states only the $n\le 8$ check):

| n | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 |
|---|---|---|---|----|-----|-----|------|------|
| $3^n-3\cdot2^{n-1}+1$ | 1 | 4 | 16 | 58 | 196 | 634 | 1996 | 6178 |

## 5. Counting convention: no canonical-labeling quotient

Avoidance of $\{1132,3312\}$ depends on the actual values, so it is **not** invariant
under relabeling the letters; the count is over raw words. Verified numerically
(`data/validation.json`, V4): counting only "canonical" words (first occurrences of
$1,\dots,n$ in increasing order, i.e. identity arc-labeling) and multiplying by $n!$
gives $18, 96, 600, \ldots$ for $n = 3,4,5$ — **not** the true $16, 58, 196$. The
canonical-labeling shortcut is therefore invalid here and is not used. (Side
observation from the data: the number of identity-labeled avoiders equals $n$ for
every computed $n\le 8$.)

## 6. Ground-truth verification status (June 2026)

Brute force (three independent implementations — `data/enumerator.py`,
`data/enumerator.rs`, and a clean-room Codex implementation) confirms

$$\cc_n(1132,3312) = 3^n - 3\cdot 2^{n-1} + 1 \quad \text{for all } n = 1,\dots,8,$$

with counts $1, 4, 16, 58, 196, 634, 1996, 6178$ and nonnesting totals
$n!\,\Cat_n = 1, 4, 30, 336, 5040, 95040, 2162160, 57657600$. See
`data/counts.json`, `data/refined_stats.json` (refined by first letter, positions of
the two copies of $n$, descents, and Dyck shape), and `data/validation.json` (the full
validation ledger: literal-definition cross-checks V1-V5, Python-vs-Rust agreement,
and the Codex clean-room foil, thread `019eb99d-8e25-76a1-bb9b-ad9df1147f59`).
