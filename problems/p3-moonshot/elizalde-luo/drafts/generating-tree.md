# Nonnesting permutations of $[n]_2$ avoiding $\{1132, 3312\}$: a complete proof of the Elizalde–Luo conjecture

**Status: complete proof draft (no known gaps).** Every structural lemma has been
verified numerically against exhaustive ground truth (word-level set equality up to
$n=10$; per-lemma checks to $n=15$ and beyond). See §10 (validation log) and §11
(gap list).

**Conventions** are pinned in `../DEFINITIONS.md` and follow Elizalde–Luo,
*Pattern avoidance in nonnesting permutations* (arXiv:2412.00336, DMTCS 27:1 (2025),
#13). All words are over positive integers; positions are $1$-based.

---

## 0. Statement

A *permutation of* $[n]_2$ is a word $w = w_1 w_2 \cdots w_{2n}$ over $\{1,\dots,n\}$
in which every letter occurs exactly twice. A word $\pi$ *contains* a pattern
$\sigma = \sigma_1\cdots\sigma_k$ if there are indices $i_1 < \cdots < i_k$ with
$\pi_{i_r} < \pi_{i_s} \iff \sigma_r < \sigma_s$ **and**
$\pi_{i_r} = \pi_{i_s} \iff \sigma_r = \sigma_s$ for all $r,s$; otherwise $\pi$
*avoids* $\sigma$. $w$ is *nonnesting* if it avoids $1221$ and $2112$, i.e. there are
no positions $i_1<i_2<i_3<i_4$ with $w_{i_1} = w_{i_4} \ne w_{i_2} = w_{i_3}$.

> **Theorem (Elizalde–Luo conjecture).** For every $n \ge 1$, the number of
> nonnesting permutations of $[n]_2$ avoiding both $1132$ and $3312$ equals
> $$ 3^n - 3\cdot 2^{n-1} + 1 .$$

For $n=1$ the unique word $11$ has length $2 < 4$, avoids everything, and
$3 - 3 + 1 = 1$. **From here on assume $n \ge 2.$**

The proof has three independent parts:

* **Part I (structure).** A nonnesting word is a pair (Dyck shape, label permutation
  $p$). $w$ avoids $\{1132,3312\}$ **iff** (a) $p$ is *extremal* — every entry is a
  running maximum or running minimum, so $p$ is encoded by a sign vector
  $\varepsilon \in \{+,-\}^{n-1}$ — and (b) the shape satisfies a single crossing
  condition $(\star)$ relative to $\varepsilon$. (Lemmas 1–7, Theorem 8.)
* **Part II (counting one fiber).** For each $\varepsilon$ the number of shapes
  satisfying $(\star)$ is
  $$ N(\varepsilon) \;=\; 3\sum_{u=1}^{m-1} 2^{\,m-1-u}\, r_u \;+\; r_m \;+\; 1, $$
  where $r_1,\dots,r_m$ are the lengths of the maximal runs of equal signs in
  $\varepsilon$ (empty sum if $m=1$). (Lemma 9, Theorem 10.)
* **Part III (summing the tree).** Summing $N(\varepsilon)$ over all $2^{n-1}$ sign
  vectors via a succession rule on the sign-vector tree gives
  $3^n - 3\cdot 2^{n-1} + 1$. (Lemma 11, Proposition 12, Theorem 13.)

This is the "Dyck shape $\times$ binary sign labels" decomposition: the generating
tree lives on sign vectors (append a sign = append one new arc), with the fiber
count $N(\varepsilon)$ as the catalytic statistic. §9 explains the generating-tree
reading, including why the naive insert-largest-letter tree fails.

---

## 1. Preliminaries: arcs, FIFO, and the shape–label decomposition

For a permutation $w$ of $[n]_2$ and a value $v$, write $o(v) < c(v)$ for the
positions of the first and second occurrence of $v$ (its *opener* and *closer*). A
position is an opener (resp. closer) if it carries the first (resp. second)
occurrence of its value.

**Lemma 1 (FIFO).** $w$ is nonnesting **iff** for all values $u \ne v$:
$o(u) < o(v) \iff c(u) < c(v)$.

*Proof.* ($\Leftarrow$) If $w$ contains $1221$ or $2112$, there are positions
$i_1<i_2<i_3<i_4$ with $w_{i_1}=w_{i_4}=u \ne v=w_{i_2}=w_{i_3}$. Then
$i_1 = o(u)$, $i_4 = c(u)$, $i_2 = o(v)$, $i_3 = c(v)$ (each value occurs exactly
twice), so $o(u) < o(v)$ while $c(v) < c(u)$ — contradicting the equivalence.
($\Rightarrow$) If $o(u) < o(v)$ and $c(v) < c(u)$ for some $u\neq v$, then since
$o(v) < c(v)$ the four positions $o(u) < o(v) < c(v) < c(u)$ carry the values
$u,v,v,u$, an occurrence of $1221$ (if $u<v$) or $2112$ (if $u>v$), so $w$ is not
nonnesting. $\blacksquare$

For nonnesting $w$, list the values in order of their openers: $p_1, \dots, p_n$
(so $o(p_1) < \cdots < o(p_n)$); by Lemma 1 also $c(p_1) < \cdots < c(p_n)$. Call
the pair $(o_i, c_i) := (o(p_i), c(p_i))$ **arc $i$**; thus the $i$-th opener (in
position order) and the $i$-th closer belong to arc $i$, and $p \in S_n$ is the
**label permutation**. The **shape** of $w$ is the word in $\{U,D\}^{2n}$ with $U$
at openers and $D$ at closers.

**Proposition 2 (decomposition).** The map $w \mapsto (\text{shape}, p)$ is a
bijection from nonnesting permutations of $[n]_2$ to (Dyck words of length $2n$)
$\times\, S_n$. Here a *Dyck word* has $n$ $U$'s and $n$ $D$'s, every prefix
containing at least as many $U$'s as $D$'s.

*Proof.* The shape of a nonnesting word is Dyck: in any prefix, every closer
$c_i$ in it is preceded by its opener $o_i$, and $c_i \le t \Rightarrow o_i < t$,
so $\#\{i : c_i \le t\} \le \#\{i: o_i \le t\}$. Conversely, given a Dyck word and
$p\in S_n$, define $w$ by putting $p_i$ on the $i$-th $U$ **and** on the $i$-th $D$.
In a Dyck word the $i$-th $D$ comes after the $i$-th $U$ (the prefix ending at the
$i$-th $D$ has $\ge i$ $U$'s), so each value $p_i$ occurs exactly twice, opener
before closer, and openers/closers are simultaneously sorted by $i$; by Lemma 1, $w$
is nonnesting. The two constructions are mutually inverse by definition of arcs.
$\blacksquare$

This is the validated "structured form" of `DEFINITIONS.md` §3 (validation V2:
set equality for $n \le 5$, counts at $n=6$); it gives the count
$|\mathcal{C}_n| = \mathrm{Cat}_n \cdot n!$.

**Lemma 3 (arc-level form of the two patterns).** Let $w$ be any permutation of
$[n]_2$ (nonnesting not needed). Then:

* (a) $w$ contains $1132$ $\iff$ there exist a value $a$ and positions
  $c(a) < x < y$ with $w_x > w_y > a$.
* (b) $w$ contains $3312$ $\iff$ there exist a value $a$ and positions
  $c(a) < x < y$ with $w_x < w_y < a$.

*Proof.* (a) ($\Leftarrow$) The positions $o(a) < c(a) < x < y$ carry values
$(a, a, w_x, w_y)$ with $a < w_y < w_x$ and $w_x \neq w_y$: both order biconditionals
of the containment definition match $\sigma = 1132$ ($\sigma_1=\sigma_2=1 <
\sigma_4=2 < \sigma_3=3$). ($\Rightarrow$) In an occurrence $i_1<i_2<i_3<i_4$ of
$1132$, $w_{i_1} = w_{i_2} =: a$ forces $\{i_1,i_2\} = \{o(a), c(a)\}$, so
$i_2 = c(a)$; take $x = i_3$, $y = i_4$: $w_x > w_y > a$ by the pattern's order
relations. (b) is identical with all inequalities reversed. $\blacksquare$

Lemma 3 is exactly the "fast check" used by all enumerators; it was *additionally*
verified against the literal definition by exhaustive comparison (validation V1:
all words for $n \le 4$, all nonnesting words for $n=5$).

**Lemma 4 (complement involution).** Let $\kappa(w)$ be defined by
$\kappa(w)_t = n+1-w_t$. Then $\kappa$ is an involution on permutations of $[n]_2$
that (i) preserves nonnesting-ness, openers, closers, arcs and the shape;
(ii) maps occurrences of $1132$ bijectively to occurrences of $3312$ and vice versa
(at the same positions); (iii) replaces the label permutation $p$ by its complement
$p^c_i = n+1-p_i$.

*Proof.* $\kappa$ negates all value comparisons and preserves value equalities and
positions. Equality patterns ($1221 \leftrightarrow 2112$) are exchanged, so
nonnesting (avoiding both) is preserved; first/second occurrences of each value are
preserved, hence so are arcs and shape, and (iii) is immediate. For (ii): a
subsequence is an occurrence of $\sigma$ in $w$ iff it is an occurrence of the
complement of $\sigma$ (within $\sigma$'s own values) in $\kappa(w)$; the complement
of $1132$ on $\{1,2,3\}$ ($1\leftrightarrow 3$, $2 \leftrightarrow 2$) is $3312$,
and conversely. $\blacksquare$

---

## 2. Part I(a): the label permutation must be extremal

**Definition.** $p \in S_n$ is **extremal** if for every $i \ge 2$, either
$p_i > \max\{p_1,\dots,p_{i-1}\}$ (then set $\varepsilon_i = +$) or
$p_i < \min\{p_1,\dots,p_{i-1}\}$ (then $\varepsilon_i = -$). The **sign vector**
of $p$ is $\varepsilon(p) = (\varepsilon_2, \dots, \varepsilon_n) \in \{+,-\}^{n-1}$.
(Arc $1$ carries no sign.)

**Lemma 5 (avoidance forces extremality).** If a nonnesting $w$ avoids
$\{1132, 3312\}$, then its label permutation $p$ is extremal.

*Proof.* Suppose not: some $v$ has $\alpha, \beta < v$ with
$p_\alpha < p_v < p_\beta$. By Lemma 1, $c_{\min(\alpha,\beta)} <
c_{\max(\alpha,\beta)} < c_v$.

* If $\alpha < \beta$: apply Lemma 3(a) with $a = p_\alpha$, $x = c_\beta$,
  $y = c_v$ (so $c(a) = c_\alpha < x < y$): $w_x = p_\beta > w_y = p_v > p_\alpha$,
  hence $w$ contains $1132$.
* If $\beta < \alpha$: apply Lemma 3(b) with $a = p_\beta$, $x = c_\alpha$,
  $y = c_v$: $w_x = p_\alpha < w_y = p_v < p_\beta$, hence $w$ contains $3312$.

Either way, a contradiction. $\blacksquare$

**Lemma 6 (extremal $\leftrightarrow$ sign vectors).** The map
$p \mapsto \varepsilon(p)$ is a bijection from extremal permutations of $[n]$ onto
$\{+,-\}^{n-1}$. Moreover, for extremal $p$, every prefix set
$\{p_1, \dots, p_i\}$ is an interval of integers, and
$p_1 = 1 + \#\{i : \varepsilon_i = -\}$.

*Proof.* *Prefix sets are intervals*, by downward induction on $i$:
$\{p_1,\dots,p_n\} = [n]$ is an interval; if $\{p_1,\dots,p_{i+1}\}$ is an interval
then deleting $p_{i+1}$ — its maximum or minimum, by extremality — leaves an
interval. Consequently, writing $\{p_1, \dots, p_i\} = [\ell_i, h_i]$:
if $\varepsilon_{i+1} = +$ then $p_{i+1} = h_i + 1$, and if $\varepsilon_{i+1} = -$
then $p_{i+1} = \ell_i - 1$ (it must extend the interval by exactly one on the
corresponding side). Hence $\varepsilon$ determines $p$ once $p_1$ is known; and
$p_1$ is determined by $\varepsilon$, because $\ell_n = 1$ and $\ell$ decreases by
one exactly at the minus signs, giving $p_1 = 1 + \#\{-\text{ signs}\}$. So the map
is injective. It is surjective: given $\varepsilon$, start from
$p_1 = 1 + \#\{-\}$ and build $p$ by the displayed rules; the result is an extremal
permutation of $[n]$ with sign vector $\varepsilon$. $\blacksquare$

**Lemma 7 (signs decide all pairwise comparisons).** Let $p$ be extremal and
$1 \le u < v \le n$, $v \ge 2$. Then $\varepsilon_v = + \iff p_v > p_u$, and
$\varepsilon_v = - \iff p_v < p_u$.

*Proof.* If $\varepsilon_v = +$ then $p_v$ exceeds all earlier entries, in
particular $p_u$; if $\varepsilon_v = -$ then $p_v < p_u$ likewise. These two cases
are exhaustive and mutually exclusive, giving both biconditionals. $\blacksquare$

---

## 3. Part I(b): the crossing characterization

Throughout this section $w$ is nonnesting with **extremal** $p$ and sign vector
$\varepsilon$; *arc $i$ has sign $\varepsilon_i$* ($i \ge 2$). Recall (Lemma 1)
that $o_1 < o_2 < \cdots$ and $c_1 < c_2 < \cdots$, and $o_i < c_i$. Note that
$c_1$ is the **first closer of the whole word**.

**Definition (condition $(\star)$).** A shape (with arcs indexed as above) satisfies
$(\star)$ with respect to $\varepsilon$ if:

> for all $2 \le k < j \le n$ with $\varepsilon_k = \varepsilon_j$:
> if $o_j < c_k$ then $o_j < c_1$.

In words: *after the first closer, no arc may open while an earlier arc of the same
sign is still open.* (Pairs with $o_j < c_1$ — i.e. arcs that open during the
initial run of openers — are unrestricted; opposite-sign pairs are unrestricted;
nesting is already excluded by nonnesting-ness.)

**Theorem 8 (characterization).** Let $w$ be a nonnesting permutation of $[n]_2$
with label permutation $p$ and shape $T$. Then $w$ avoids $\{1132, 3312\}$ **iff**
$p$ is extremal and $T$ satisfies $(\star)$ with respect to $\varepsilon(p)$.

*Proof.*

**($\Rightarrow$)** $p$ is extremal by Lemma 5. Suppose $(\star)$ fails: there are
same-sign arcs $k < j$ with $c_1 < o_j < c_k$. Note $k \ge 2$, so by Lemma 7
(with $u = 1$): if the common sign is $+$ then $p_1 < p_k < p_j$ (the second
inequality by Lemma 7 with $u = k < j$). The positions
$o_1 < c_1 < o_j < c_k$ then satisfy Lemma 3(a) with $a = p_1$, $x = o_j$,
$y = c_k$: $w_x = p_j > w_y = p_k > p_1$ — so $w$ contains $1132$. If the common
sign is $-$ then symmetrically $p_1 > p_k > p_j$ and Lemma 3(b) (same positions)
shows $w$ contains $3312$. Either way $w$ is not an avoider. Contrapositively, an
avoider satisfies $(\star)$.

**($\Leftarrow$)** Let $p$ be extremal and $T$ satisfy $(\star)$; suppose for
contradiction that $w$ contains $1132$ (the $3312$ case follows by applying the
$1132$ case to $\kappa(w)$: by Lemma 4, $\kappa(w)$ is nonnesting with the same
shape and complemented labels, which are extremal with all signs flipped, and
$(\star)$ is invariant under flipping all signs since it only refers to sign
*equality*).

By Lemma 3(a) there are a value $a$ — belonging to some arc $t$, so $a = p_t$ and
$c(a) = c_t$ — and positions $c_t < x < y$ with $w_x > w_y > p_t$. Let $j$ be the
arc of the value $w_x$ and $k$ the arc of the value $w_y$; then $t, j, k$ are
pairwise distinct (three distinct values) and
$$ p_j > p_k > p_t, \qquad x \in \{o_j, c_j\},\quad y \in \{o_k, c_k\},
\qquad c_t < x < y. $$
We use throughout: $u < v \iff o_u < o_v \iff c_u < c_v$ (Lemma 1), and Lemma 7.
Four cases.

* **Case A: $x = o_j$, $y = o_k$.** Then $o_j < o_k$, so $j < k$, and $p_k < p_j$
  forces $\varepsilon_k = -$ (Lemma 7, $u=j<v=k$). If $k > t$, then $p_k > p_t$
  forces $\varepsilon_k = +$ — contradiction. If $k < t$, then
  $y = o_k < c_k < c_t$, contradicting $y > x > c_t$.

* **Case B: $x = o_j$, $y = c_k$.** Then $c_k = y > c_t$, so $k > t$, and
  $p_k > p_t$ forces $\varepsilon_k = +$. If $j < k$, then $p_k < p_j$ forces
  $\varepsilon_k = -$ — contradiction. So $k < j$, and $p_j > p_k$ forces
  $\varepsilon_j = + = \varepsilon_k$: a same-sign pair $k < j$ with
  $o_j = x < y = c_k$. By $(\star)$, $o_j < c_1$. But $o_j = x > c_t \ge c_1$ —
  contradiction.

* **Case C: $x = c_j$, $y = o_k$.** Then $c_j > c_t$, so $j > t$, and $p_j > p_t$
  forces $\varepsilon_j = +$. Also $o_k = y > x = c_j > o_j$, so $k > j$, and
  $p_k < p_j$ forces $\varepsilon_k = -$, while $p_k > p_t$ with $k > j > t$ forces
  $\varepsilon_k = +$ — contradiction.

* **Case D: $x = c_j$, $y = c_k$.** Then $c_t < c_j < c_k$ gives $t < j < k$;
  $p_j > p_t$ forces $\varepsilon_j = +$; and $p_k > p_t$ forces $\varepsilon_k = +$
  while $p_k < p_j$ ($k > j$) forces $\varepsilon_k = -$ — contradiction.

All cases are impossible, so $w$ avoids $1132$; by the complement argument it also
avoids $3312$. $\blacksquare$

**Corollary 8.1.** The map $w \mapsto (\varepsilon(p), T)$ is a bijection from
avoiders of size $n$ onto pairs (sign vector $\varepsilon$, Dyck shape $T$
satisfying $(\star)$ w.r.t. $\varepsilon$). Hence
$$ a_n \;=\; \sum_{\varepsilon \in \{+,-\}^{n-1}} N(\varepsilon), \qquad
N(\varepsilon) := \#\{\,T \text{ Dyck, } T \text{ satisfies } (\star)\,\}. $$

*Proof.* Combine Proposition 2 (shape, $p$ determine $w$), Lemma 6 ($\varepsilon$
determines extremal $p$), and Theorem 8. $\blacksquare$

*Numeric check (§10, T1):* for $2 \le n \le 10$ the set of words constructed from
all pairs $(\varepsilon, T \text{ with } (\star))$ **equals** the exhaustively
enumerated avoider set — e.g. $57514$ words at $n = 10$.

---

## 4. Part II: counting the shapes in one fiber

Fix $\varepsilon \in \{+,-\}^{n-1}$, $n \ge 2$. Write $\varepsilon$ as maximal runs
of equal signs, of lengths $r_1, \dots, r_m$ ($r_u \ge 1$, $\sum r_u = n-1$).
Define run boundaries on **arc indices**:
$$ e_0 = 1, \qquad e_u = 1 + r_1 + \cdots + r_u \ (1 \le u \le m), \qquad
b_u = e_{u-1} + 1, $$
so run $u$ consists of arcs $b_u, b_u + 1, \dots, e_u$, all of one sign, runs
alternating in sign, and $e_m = n$. For an arc $i \ge 2$ let
$$ k_i \;=\; \max\{\,k : 2 \le k < i,\ \varepsilon_k = \varepsilon_i\,\} \quad
(\text{set } k_i = 0 \text{ if none}). $$
Explicitly: $k_i = i - 1$ if $i$ is not the first arc of its run; $k_{b_u} =
e_{u-2}$ for $u \ge 3$; and $k_{b_1} = k_{b_2} = 0$.

**Lemma 9 (m-coordinates).** For a Dyck shape $T$ of size $n$, let
$m_i = \#\{\text{closers before } o_i\}$ for $2 \le i \le n$ (and $m_1 = 0$). Then:

1. $T \mapsto (m_2, \dots, m_n)$ is a bijection from Dyck shapes onto integer
   vectors with $0 \le m_2 \le m_3 \le \cdots \le m_n$ and $m_i \le i-1$ for all
   $i$.
2. For all arc indices $j, k$: $\;o_j < c_k \iff m_j \le k - 1$. In particular
   $o_j < c_1 \iff m_j = 0$.
3. $T$ satisfies $(\star)$ **iff** for every $i \ge 2$:
   $\; m_i = 0$ or $k_i = 0$ or $m_i \ge k_i$.

*Proof.* (1) Monotonicity: $o_i < o_{i+1}$, so closers before $o_i$ are among those
before $o_{i+1}$. Bound: $m_i \le i - 1$ iff fewer than $i$ closers precede $o_i$
iff $c_i > o_i$, which holds. Conversely, given such a vector, build the word
$$ U\; D^{\,m_2 - m_1}\, U\; D^{\,m_3 - m_2}\, U\, \cdots\, U\; D^{\,n - m_n}, $$
i.e. put $m_{i} - m_{i-1}$ closers between the $(i-1)$-st and $i$-th opener and
$n - m_n$ at the end. All exponents are $\ge 0$; the total number of $D$'s is $n$;
the $i$-th $U$ is preceded by exactly $m_i \le i-1$ $D$'s, so every prefix ending at
a $U$ has more $U$'s than $D$'s, and any other prefix has $D$-count at most that of
the next $U$ or of the full word — hence Dyck. The two maps are mutually inverse.
(2) $o_j < c_k$ iff fewer than $k$ closers precede $o_j$ (the closers being
$c_1 < c_2 < \cdots$) iff $m_j < k$. (3) By (2), $(\star)$ reads: for all same-sign
pairs $k < j$: $m_j \le k-1 \Rightarrow m_j = 0$. Fix $j$ with $k_j \neq 0$ and
suppose $m_j \neq 0$. The condition for the pairs $(k, j)$, over all same-sign
$k < j$, is then: $m_j \ge k$ for every such $k$ — which is equivalent to
$m_j \ge k_j$, since $k_j$ is the largest such $k$. Conversely if $m_j = 0$ or
$k_j = 0$ all pairs $(k,j)$ are unconstrained or vacuous. Ranging over $j$ gives
exactly statement (3). $\blacksquare$

Call a vector $(m_2,\dots,m_n)$ as in Lemma 9(1) **valid** (for $\varepsilon$) if it
satisfies 9(3). So $N(\varepsilon) = \#\{\text{valid vectors}\}$, and the allowed
value set for each coordinate is
$$ m_i \in \{0\} \cup [\,\max(k_i, 1),\; i-1\,] \qquad (2 \le i \le n), $$
subject to monotonicity. Note for a **mid-run** arc ($k_i = i-1$) this set is
$\{0,\, i-1\}$: mid-run coordinates are extreme. (Intuition: after the first closer,
each new arc of a sign must wait for the previous same-sign arc to close; FIFO makes
"the previous one" the binding constraint.)

**Theorem 10 (fiber count).** With runs $r_1, \dots, r_m$ as above,
$$ N(\varepsilon) \;=\; f(r_1,\dots,r_m) \;:=\;
3\sum_{u=1}^{m-1} 2^{\,m-1-u} r_u \;+\; r_m \;+\; 1 $$
(the sum is empty when $m = 1$, giving $N = r_1 + 1$).

*Proof.* For a valid vector let
$$ h \;=\; \max\{\, i \in [1, n] : m_i = 0 \,\} \qquad (m_1 = 0 \text{, so } h
\text{ is well defined; } h \ge 1). $$
By monotonicity, $m_i = 0 \iff i \le h$. We count valid vectors with each fixed
$h$, and sum. Write $V_h$ for that count.

**(i) $h = n$:** the all-zero vector. It is valid ($0$ is always allowed), so
$V_n = 1$.

Now let $h < n$ and let $w$ be the index of the run containing arc $h+1$ (i.e.
$b_w \le h + 1 \le e_w$). All coordinates $m_i$ with $i > h$ satisfy $m_i \ge 1$,
hence $m_i \ge \max(k_i, 1)$ is required. We claim the valid vectors with this $h$
are exactly the following product set, where "forced" means a single value:

* $m_i = 0$ for $i \le h$;
* **(mid-run, forced)** $m_i = i - 1$ for every $i > h$ that is *not* the first
  arc of its run (this includes $i = h+1$ whenever $h + 1 > b_w$);
* **(first active run-start)** if $h + 1 = b_w$ (equivalently $h = e_{w-1}$), then
  $$ m_{b_w} \in W_w := \begin{cases}
     \{1\} & w = 1 \ (\text{i.e. } h = 1, \ b_1 = 2),\\
     [\,1,\ e_1\,] & w = 2,\\
     [\,e_{w-2},\ e_{w-1}\,] & w \ge 3;
     \end{cases} $$
* **(later run-starts)** for every run $u$ with $w < u \le m$:
  $\; m_{b_u} \in \{\, e_{u-1} - 1,\ e_{u-1} \,\}$ — two free choices each,
  independent of everything else.

*Every valid vector has this form.* First note that for $u > w$ we have
$e_{u-1} \ge e_w > h$ (in the case $h = e_{w-1}$ because $e_w = e_{w-1} + r_w > h$;
in the mid-run case because $h \le e_w - 1$), so every arc of runs
$w+1, \dots, m$, and the arc $e_{u-1}$ for $u > w$, lies strictly beyond $h$.
Now: mid-run $i > h$: allowed set $\{0, i-1\}$ and $m_i \neq 0$, so $m_i = i-1$.
First active run-start (case $h+1 = b_w$): the allowed set is
$\{0\} \cup [\max(k_{b_w},1),\, b_w - 1]$ with $0$ excluded; since
$b_w - 1 = e_{w-1}$ and $k_{b_w} = e_{w-2}$ for $w \ge 3$ (resp. $k_{b_w} = 0$ for
$w \le 2$, and $b_1 - 1 = 1$ for $w = 1$), this set is exactly $W_w$; the
monotonicity constraint from the left is $m_{b_w} \ge m_h = 0$, vacuous.
Later run-start $b_u$ ($u > w$): upper bound $m_{b_u} \le b_u - 1 = e_{u-1}$. Lower
bound $m_{b_u} \ge e_{u-1} - 1$, by cases on $r_{u-1}$:
if $r_{u-1} \ge 2$, the previous arc $e_{u-1}$ is mid-run and $> h$, so
$m_{e_{u-1}} = e_{u-1} - 1$ and monotonicity gives $m_{b_u} \ge e_{u-1} - 1$;
if $r_{u-1} = 1$ then $e_{u-2} = e_{u-1} - 1$, and either $u \ge 3$, in which case
the $(\star)$-constraint $m_{b_u} \ge k_{b_u} = e_{u-2}$ gives the bound, or
$u = 2$ (so $w = 1$, $h = 1$, $e_1 = 2$), in which case $e_{u-1} - 1 = 1$ and
$m_{b_2} \ge 1$ holds because $b_2 > h$. Hence
$m_{b_u} \in \{e_{u-1}-1,\, e_{u-1}\}$.

*Every choice in the product set is valid.* The bound $m_i \le i - 1$ and the
$(\star)$-conditions $m_i \in \{0\} \cup [\max(k_i,1), i-1]$ hold by construction:
mid-run, $m_i = i-1 \ge k_i = i-1$; run-starts, $W_w \subseteq [\max(k_{b_w},1),
e_{w-1}]$ and $\{e_{u-1}-1, e_{u-1}\} \subseteq [\max(k_{b_u},1), e_{u-1}]$ because
$k_{b_u} = e_{u-2} \le e_{u-1}-1$ (or $k_{b_u} = 0$). Monotonicity at each junction
$i \to i+1$: inside the zero block, $0 \le 0$; from $m_h = 0$ to anything
nonnegative; mid-run to mid-run, $i-1 \le i$; into a mid-run arc $i+1$ from any
arc, $m_i \le i - 1 < i = m_{i+1}$; into a run-start $b_u$ ($u > w$) from
$e_{u-1}$: the left value satisfies $m_{e_{u-1}} \le e_{u-1} - 1$ (the universal
bound), and the right value satisfies $m_{b_u} \ge e_{u-1} - 1$ (its window), so
the junction is monotone. Thus every junction is monotone for **every**
combination of window choices, independently of the choices made. Hence
$$ V_h = |W_w| \cdot 2^{\,m - w} \quad (h = e_{w-1}), \qquad
V_h = 2^{\,m-w} \quad (b_w \le h \le e_w - 1), $$
where in the second case the mid-run coordinates up to $e_w$ are forced and runs
$w+1, \dots, m$ contribute the binary windows (note $e_{u-1} \ge e_w > h$ holds for
$u > w$ there as well, and $h+1 > b_w$ requires $r_w \ge 2$).

The values $h \in [1, n]$ are exhausted exactly once by: $h = e_0 = 1$ ($w = 1$,
$|W_1| = 1$); $h = e_{w-1}$ for $w = 2, \dots, m$ ($|W_w| = r_{w-1} + 1$, using
$|[1, e_1]| = e_1 = r_1 + 1$ and $|[e_{w-2}, e_{w-1}]| = r_{w-1} + 1$); mid-run
values $h \in [b_w, e_w - 1]$, which number $r_w - 1$ for each $w$; and $h = n$.
Therefore
$$ N(\varepsilon) = 1 \;+\; 2^{m-1} \;+\; \sum_{w=2}^{m} (r_{w-1} + 1)\, 2^{m-w}
\;+\; \sum_{w=1}^{m} (r_w - 1)\, 2^{m-w}. $$
Reindex the first sum with $u = w - 1$ and split the second:
$$ \sum_{u=1}^{m-1} (r_u + 1) 2^{m-1-u} + \sum_{u=1}^{m-1} (r_u - 1) 2^{m-u}
+ (r_m - 1) = \sum_{u=1}^{m-1} \bigl[(r_u+1) + 2(r_u - 1)\bigr] 2^{m-1-u} + r_m - 1 $$
$$ = \sum_{u=1}^{m-1} (3 r_u - 1)\, 2^{m-1-u} + r_m - 1
= 3\!\sum_{u=1}^{m-1} 2^{m-1-u} r_u \;-\; (2^{m-1} - 1) \;+\; r_m - 1. $$
Adding the $1 + 2^{m-1}$ from cases (i) and ($h=1$):
$$ N(\varepsilon) = 3\sum_{u=1}^{m-1} 2^{m-1-u} r_u + r_m + 1. $$
For $m = 1$ the same bookkeeping reads $N = 1 + 1 + (r_1 - 1) = r_1 + 1$. 
$\blacksquare$

*Numeric checks (§10):* per-$h$ counts $V_h$ match brute force for **every**
$\varepsilon$ with $n \le 9$ (Test A); $N(\varepsilon)$ matches brute-force shape
counts for $n \le 9$ (T2/Test B) and the closed form for every $\varepsilon$ with
$n \le 15$ (Test C); word-level set equality up to $n = 10$ (T1).

**Corollary 10.1 (identity labels).** For $p = \mathrm{id}$ ($\varepsilon = +^{n-1}$,
$m=1$): exactly $n$ avoiders — matching the independent side observation recorded in
`data/validation.json` (V4) for all $n \le 8$.

---

## 5. Part III: summing over the sign-vector tree

Organize all sign vectors (all lengths) into the binary tree where the children of
$\varepsilon$ are $\varepsilon{+}$ and $\varepsilon{-}$ (append one sign on the
right = append one new arc/letter; see §9). Write $f(\varepsilon)$ for the closed
form of Theorem 10 and $\ell(\varepsilon) = r_m$ for the last run length.

**Lemma 11 (succession identities).** For every nonempty $\varepsilon$ with runs
$(r_1, \dots, r_m)$ and last sign $s$:
$$ f(\varepsilon s) = f(\varepsilon) + 1, \qquad
f(\varepsilon \bar{s}) = 2 f(\varepsilon) + \ell(\varepsilon), $$
and the child statistics are $\ell(\varepsilon s) = \ell(\varepsilon) + 1$,
$\ell(\varepsilon \bar s) = 1$.

*Proof.* Same sign: runs become $(r_1, \dots, r_m + 1)$; $m$ is unchanged, the sum
term is unchanged, $r_m + 1$ replaces $r_m$: $f$ increases by exactly $1$. Opposite
sign: runs become $(r_1, \dots, r_m, 1)$ with $m' = m + 1$:
$$ f(\varepsilon\bar s) = 3\sum_{u=1}^{m} 2^{\,m-u} r_u + 1 + 1
= 2 \cdot 3\sum_{u=1}^{m-1} 2^{\,m-1-u} r_u + 3 r_m + 2
= 2\bigl(f(\varepsilon) - r_m - 1\bigr) + 3 r_m + 2 = 2 f(\varepsilon) + r_m. 
\blacksquare $$

**Proposition 12 (level sums).** For $k \ge 1$ let
$S_k = \sum_{|\varepsilon| = k} f(\varepsilon)$ and
$T_k = \sum_{|\varepsilon| = k} \ell(\varepsilon)$. Then $T_k = 2^{k+1} - 2$ and
$S_k = 3^{k+1} - 3 \cdot 2^{k} + 1$.

*Proof.* Base $k=1$: $f(+) = f(-) = 2$ (runs $(1)$: $f = 1+1$) and $\ell = 1$, so
$S_1 = 4 = 3^2 - 3\cdot 2 + 1$ and $T_1 = 2 = 2^2 - 2$. Each $\varepsilon$ of
length $k$ has exactly two children of length $k+1$, and every vector of length
$k+1$ is a child of exactly one parent. By Lemma 11,
$$ T_{k+1} = \sum_{|\varepsilon|=k} \bigl[(\ell + 1) + 1\bigr] = T_k + 2\cdot 2^k,
$$
so by induction $T_k = 2 + \sum_{j=1}^{k-1} 2^{j+1} = 2^{k+1} - 2$. And
$$ S_{k+1} = \sum_{|\varepsilon|=k} \bigl[(f + 1) + (2f + \ell)\bigr]
= 3 S_k + 2^k + T_k = 3 S_k + 3\cdot 2^k - 2. $$
If $S_k = 3^{k+1} - 3\cdot2^k + 1$ then
$S_{k+1} = 3^{k+2} - 9\cdot 2^k + 3 + 3\cdot 2^k - 2 = 3^{k+2} - 3\cdot 2^{k+1} + 1$.
$\blacksquare$

**Theorem 13 (main theorem).** For all $n \ge 1$, the number of nonnesting
permutations of $[n]_2$ avoiding $\{1132, 3312\}$ is $3^n - 3\cdot 2^{n-1} + 1$.

*Proof.* $n = 1$: the unique word $11$, and $3 - 3 + 1 = 1$. For $n \ge 2$:
by Corollary 8.1 and Theorem 10,
$a_n = \sum_{\varepsilon \in \{\pm\}^{n-1}} f(\varepsilon) = S_{n-1}
= 3^{n} - 3\cdot 2^{n-1} + 1$ by Proposition 12. $\blacksquare$

---

## 6. Worked example

$n = 4$, $\varepsilon = (+,-,+)$, so $p = (2,3,1,4)$ (Lemma 6: $p_1 = 1 + 1$). Runs
$r = (1,1,1)$, $m = 3$; Theorem 10: $N = 3(2\cdot 1 + 1\cdot 1) + 1 + 1 = 11$.
The valid $m$-vectors $(m_2, m_3, m_4)$, their $h$, and the words:

| $h$ | windows | vectors | count |
|---|---|---|---|
| 4 | — | $(0,0,0)$ | 1 |
| 3 | $m_4 \in \{e_2 - 1, e_2\} = \{2,3\}$ | $(0,0,2), (0,0,3)$ | 2 |
| 2 | $m_3 \in [e_0, e_1] = [1,2]$, $m_4 \in \{2,3\}$ | $(0,1,2),(0,1,3),(0,2,2),(0,2,3)$ | 4 |
| 1 | $m_2 = 1$, $m_3 \in \{1, 2\}$, $m_4 \in \{2,3\}$ | $(1,1,2),(1,1,3),(1,2,2),(1,2,3)$ | 4 |

Total $11$; e.g. $(0,1,2)$ is the shape $UUDUDUDD$ (one closer before $o_3$, two
before $o_4$), giving the word $2\,3\,2\,1\,3\,4\,1\,4$ — present in the $n=4$
avoider list; and $(0,1,3)$ gives $UUDUDDUD$, word $2\,3\,2\,1\,3\,1\,4\,4$,
likewise present.

---

## 7. Why the formula is what it is (interpretation)

$N(\varepsilon)$ decomposes the fiber by $h$ = length of the initial all-openers
block. Once the first closer has passed ($h$ fixed), each remaining sign-run
contributes a factor $2$ (its first arc can open just before or just after the
final closer of the previous run), except that the run in which the "free phase"
ends contributes a window of size $r + 1$; the linear terms $r_u$ and the powers
$2^{m-1-u}$ in the closed form are exactly the sum of these geometric
contributions over the possible $h$. The three eigenvalues $1, 2, 3$ of the
level-sum recursion (signature $(6,-11,6)$, matching OEIS A168583's o.g.f.
denominator $(1-x)(1-2x)(1-3x)$) arise as: $3$ = binary sign choice $\times$
average branching of the windows; $2$ = the sign tree alone; $1$ = the constant
boundary term.

---

## 8. Relation to the literature conventions

* The count is over **raw labeled words** (no canonical-form quotient):
  `DEFINITIONS.md` §5; our Corollary 8.1 counts exactly those.
* The nonnesting totals $n!\,\mathrm{Cat}_n$ are recovered: Proposition 2.
* The conjectured sequence $1, 4, 16, 58, 196, 634, 1996, 6178$
  ($= 3^n - 3\cdot 2^{n-1} + 1$) is OEIS A168583 shifted by $2$; our theorem proves
  the Elizalde–Luo Table 4 row $\{1132, 3312\}$.

---

## 9. Generating-tree reading (the assigned strategy) and a failed tree

**The tree that works.** Append arcs on the right. Concretely, on words: for an
avoider $w$ of $[n+1]_2$, the letter $w_{2n+2}$ at the last position is the closer
of arc $n+1$ (the last closer belongs to the last arc, Lemma 1); deleting both
copies of that value and normalizing (subtract $1$ from every letter exceeding the
deleted value — only relevant when the deleted value is the minimum) yields an
avoider of $[n]_2$ whose sign vector and $m$-vector are the truncations
$(\varepsilon_2..\varepsilon_n)$, $(m_2..m_n)$. Conversely the children of an
avoider $(\varepsilon, (m_2..m_n))$ of size $n$ are obtained by appending a sign
$\varepsilon_{n+1} = s$ (insert a new maximum value if $s = +$, new minimum if
$s = -$) and choosing the position of its opener — i.e. a value
$m_{n+1} \in Z \cup [\max(k_{n+1}, m_n, 1),\, n]$, where $Z = \{0\}$ if $m_n = 0$
and $Z = \emptyset$ otherwise (monotonicity forbids $m_{n+1} = 0$ after a nonzero
$m_n$) — its closer going to the new last position. (That this parent/child relation is well defined and exhaustive is
exactly Lemma 9 + Theorem 8: truncations of valid data are valid, extensions are
the allowed windows.)

At the level of fibers (sum over shapes for fixed $\varepsilon$), Lemma 11 is the
**succession rule**
$$ \boxed{(f, \ell) \ \longmapsto\ (f+1,\ \ell+1)\ \text{ and }\ (2f + \ell,\ 1)},
\qquad \text{root } (2, 1) \text{ at } n = 2, $$
whose level sums (Proposition 12) give $3^n - 3\cdot2^{n-1} + 1$. The catalytic
statistic $\ell$ (last run length) is what keeps the rule finite — the per-shape
tree alone does not have bounded labels.

Note the asymmetric proof burden: the **same-sign** branch of the rule is fully
proved by a two-line argument directly on $m$-vectors ($m_{n+1} \in \{0, n\}$, with
$0$ available only on the all-zero vector — so $N(\varepsilon s) = N(\varepsilon) +
1$); the **opposite-sign** branch, at shape level, needs the distribution of $m_n$
over the fiber, not just $N$ — which is why the honest proof routes through the
explicit fiber count (Theorem 10) and derives the rule afterwards (Lemma 11),
rather than proving the rule first.

**The tree that fails.** The naive generating tree (delete both copies of the
*largest letter* $n$) does **not** have bounded or label-finite branching: already
at level $2$ the four avoiders $1212, 1122, 2121, 2211$ have $2, 1, 5, 8$ children
respectively, and extreme nodes like $nn(n{-}1)(n{-}1)\cdots$ gain $\Theta(n)$ new
children per level. This matches the prior warning (Codex) that largest-entry
insertion is not the right tree; the right "insertion" is *append the last arc*
(new running extreme), i.e. grow the sign vector.

---

## 10. Numeric validation log

Ground truth and scripts live in `../data/` and `../explore/`. All tests are
re-runnable; none failed at the recorded scopes.

| # | Claim tested | Scope | Result | Script |
|---|---|---|---|---|
| V0 | brute-force avoider counts $= 3^n - 3\cdot2^{n-1}+1$ | $n \le 8$ (3 independent implementations incl. clean-room Codex) | pass | `data/enumerator.py`, `data/enumerator.rs`, ledger `data/validation.json` |
| V0+ | same, via pruned DFS on the incremental-suffix characterization (Lemma 3) | $n \le 10$ ($a_9 = 18916$, $a_{10} = 57514$ — **two levels beyond the paper's check**) | pass | `explore/gen.py`, `explore/gen10.py` |
| V1 | Lemma 3 fast checks $\equiv$ literal containment definition | all words $n\le4$; all nonnesting $n=5$ | pass | `data/enumerator.py` (V1) |
| V2 | Prop 2 decomposition $\equiv$ literal nonnesting filter | set equality $n \le 5$; counts $n = 6$ | pass | `data/enumerator.py` (V2) |
| T0 | every avoider has extremal label perm; all $2^{n-1}$ sign vectors occur | $n \le 9$ | pass | `explore/structure1.py` |
| T1 | **Theorem 8 set equality**: avoiders $=$ words from (extremal $p$, shape with $(\star)$) | $2 \le n \le 10$ (word-level set equality; $57514$ words at $n=10$) | pass | `explore/structure2.py`, inline n=10 check |
| T2/B | $N(\varepsilon)$ by shape brute force $=$ $\#$valid $m$-vectors (Lemma 9) | all $\varepsilon$, $n \le 9$ | pass | `explore/structure3.py` (Test B) |
| TA | **per-$h$ window products** $V_h$ of Theorem 10 vs brute force | all $\varepsilon$, $n \le 9$ | pass | `explore/structure3.py` (Test A) |
| T3/C | closed form $f$ $=$ $N(\varepsilon)$ (via independent DP on $m$-vectors) | all $\varepsilon$, $n \le 15$ ($32768$ sign vectors at $n=15$) | pass | `explore/structure2.py` (T3), `structure3.py` (Test C) |
| T4 | succession identities (Lemma 11) on fiber counts | all $\varepsilon$, $n \le 9$ | pass | `explore/structure2.py` (T4) |
| TD | $\sum_\varepsilon f(\varepsilon) = 3^n - 3\cdot2^{n-1}+1$ | $n \le 22$ (exhaustive over $2^{n-2}$ compositions) | pass | inline (TestD fast variant) |
| TF | fuzz: random nonnesting words satisfy [avoid (Lemma 3 form) $\iff$ extremal $+$ $(\star)$]; random $(\varepsilon,$ valid $m$-vector$)$ constructions are avoiders | $200{,}000$ words $n=12..16$; $9{,}000$ constructions $n \in \{20,30,40\}$ (note: uses the Lemma 3 fast form, whose equivalence to the literal definition is the separately-validated V1 — so this stress-tests Theorem 8 downstream of Lemma 3, not Lemma 3 itself) | pass | `explore/fuzz_theorem8.py` |
| X1 | Corollary 10.1: identity-labeled avoiders $= n$ | $n \le 8$ | pass | `data/validation.json` V4 side observation |
| X2 | first-letter distribution: $\sum_{\#- = q} f(\varepsilon)$ vs refined stats (e.g. $5,47,92,47,5$ at $n=5$) | $n = 5$ | pass | hand check vs `data/refined_stats.json` |

Independence notes: T1 compares two completely different generation pipelines
(pruned DFS on the word automaton vs. construction from $(\varepsilon, T)$ pairs).
Test C compares the closed form against a DP that knows nothing of the $h$-analysis.
V0's $n\le8$ layer was reproduced by a clean-room Codex implementation from the
paper's literal definitions (thread recorded in `data/validation.json`).

**Hostile-referee passes (Codex / GPT-5.5, thread
`019eb9d2-38a6-7ce1-b8e7-7c16a81c18bc`, June 2026).** Round 1 attacked Theorem 8's
case analysis, Theorem 10's window products, Lemma 9, Lemmas 5–7, the
succession-rule algebra, and the conventions; it reran `structure2.py` and wrote an
independent checker (`explore/codex_referee/referee_check.py`: literal containment
vs. the characterization for all nonnesting words through $n=6$, $n=7$ avoider-list
reconstruction, Theorem 10 windows through $n=9$, fiber totals through $n=13$ — all
passed). Findings: one MINOR wording issue in Lemma 9(3), fixed. Round 2 attacked
Lemma 3's conventions, the Dyck inverse arguments, the $h$-partition, and §9;
findings: two MINOR exposition issues (the §9 child-window display, and the fuzz
test's description), both fixed. Verdict both rounds: **"proof confirmed modulo
minor edits."**

## 11. Honest gap list

* **No known gaps.** Every lemma above has a complete written proof, and every
  proof step that could hide an error (the four-case analysis of Theorem 8, the
  window/product analysis of Theorem 10, the algebra of Lemma 11/Proposition 12)
  has a matching exhaustive numeric test at small-to-moderate sizes.
* Points a referee should scrutinize (all believed sound, all tested):
  1. Theorem 8, Case B is the only place $(\star)$ is used; Cases A, C, D derive
     contradictions purely from FIFO + Lemma 7. The case split is over
     $x \in \{o_j, c_j\} \times y \in \{o_k, c_k\}$ and is exhaustive because
     $w_x \neq w_y$ forces $j \neq k$ and $w_x, w_y \neq p_t$ forces $j,k \neq t$.
  2. Theorem 10's claim that the per-$h$ valid set is a *product* of independent
     windows — the only coupling risk is monotonicity between consecutive
     run-start coordinates when intervening runs have length 1; the proof handles
     this by showing each window's lower bound dominates the previous window's
     upper bound. Verified exhaustively per-$h$ (Test A).
  3. Lemma 9's translation $o_j < c_k \iff m_j \le k-1$ silently uses FIFO
     (closers indexed in arc order), which holds by Lemma 1/Proposition 2.
* Formalization outlook (Lean): all objects are finite and all maps explicit;
  the only induction is over $n$ (Lemma 6, Proposition 12) and the case analyses
  are decidable predicates on tuples of indices. No generating functions, no
  analysis. The succession rule needs only Lemma 11's two algebraic identities.
